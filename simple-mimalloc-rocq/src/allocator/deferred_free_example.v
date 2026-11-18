From AllSrc.iris_heap_lang_asm Require Import lang notation proofmode.
From AllSrc.allocator Require Import utils.
From AllSrc.allocator Require Import heap_allocator.
From AllSrc.intrusive_list Require Import thread_safe_ilist.

Section DefEx. 
  Context `{!heapGS_gen hlc Σ, !spin_lockG Σ, !my_ghostG Σ}. 
  
  Implicit Types l lt ld : loc. 
  Implicit Types γ : gname.
  Implicit Types d : nat.

  Definition f_next : nat := 0.
  Definition f_branch1 : nat := 2.
  Definition f_branch2 : nat := 3.

  (* BLOCK_SIZE hast to be at least 4 *)
  Definition tree_size : nat := 4.
  Definition data_size : nat := HAlloc.BLOCK_SIZE - tree_size.

  (* tree functions *)
  Definition new_tree : val := λ: "al", 
    let: "l" := HAlloc.heap_alloc "al" #tree_size in
    ("l" + #f_next) <- #NULL ;; 
    ("l" + (#f_next + #1)) <- #NULL ;; 
    ("l" + #f_branch1) <- #NULL ;; 
    ("l" + #f_branch2) <- #NULL ;; 
    "l". 

  (* need ilist node pointer for this! *)
  Definition make_pointer_tree_rec : val := rec: "rec" "al" "ln" "d" := 
    if: "d" ≤ #0 then #()
    else 
      let: "lt" := new_tree "al" in 
      "rec" "al" ("lt" + #f_branch1) ("d" - #1) ;; 
      "rec" "al" ("lt" + #f_branch2) ("d" - #1) ;;
      "ln" <- "lt" ;;
      #().

  (* TODO(Ben): arguably should use heap alloc here aswell or a solution 
     without this allocation *)
  Definition make_pointer_tree : val := λ: "al" "d", 
    let: "root" := Alloc #NULL in
    make_pointer_tree_rec "al" "root" "d" ;;
    let: "tree" := !"root" in 
    Free "root" ;;
    "tree".

  (* TODO(Ben): every node owning next is somewhat unrealistic *)
  (* tree definitions *)
  Fixpoint is_tree (γ : gname) (lt : loc) (d : nat) 
    (owns_next : bool) : iProp Σ :=
    match d with 
    | 0   => ⌜lt = NULL⌝
    | S d => ∃ lt1 lt2, 
      HAlloc.is_valid_loc γ lt ∗
      (lt + f_branch1) ↦ #lt1 ∗ 
      (lt + f_branch2) ↦ #lt2 ∗
      is_tree γ lt1 d true ∗ 
      is_tree γ lt2 d true ∗
      (* TODO(Ben): why the Z.of_nat necessary here and not elsewhere *)
      ([∗ list] i ∈ seq tree_size data_size, 
      ∃ v, (lt + (Z.of_nat i)) ↦ v) ∗
      if owns_next then (lt + f_next)%Z ↦∗ [LitV NULL; LitV NULL] 
      else True
    end.

  (* TODO(Ben): does this work? probably depth = 1? + false? *)
  Definition ts_queue_inv : loc → iProp Σ := 
    λ l, (∃ γ, is_tree γ l 1 false)%I.
  
  (* runtime functions *)
  Definition alloc_free_loop : val := rec: "rec" "al" "tsq" := 
    if: TSIList.is_empty "tsq" then #() 
    else 
      let: "l" := HAlloc.heap_alloc "al" #1 in
      HAlloc.heap_free "l" ;; (*could also make this a push to tsq*) 
      "rec" "al" "tsq". 

  Definition callback_free : val := λ: "lt" "tsq", 
    let: "tl" := !("lt" + #f_branch1) in
    let: "tr" := !("lt" + #f_branch2) in
    HAlloc.heap_free "lt" ;;
    if: "tl" ≠ #NULL then TSIList.push_front "tsq" "tl" else #() ;;
    if: "tr" ≠ #NULL then TSIList.push_front "tsq" "tr" else #().

  Definition callback_loop : val := rec: "rec" "i" "max_free" "tsq" := 
    if: "i" ≤ "max_free" then #()
    else 
      match: TSIList.pop_back "tsq" with 
        SOME "lt" =>  
          callback_free "lt" "tsq" ;;
          "rec" ("i" + #1) "max_free" "tsq"
      | NONE     => #()
      end. 

  Definition runtime : val := λ: "_", 
    let: "tsq" := TSIList.new #() in
    let: "al" := HAlloc.heap_new_alloc #() in  
    HAlloc.heap_register_callback "al" (λ: "_", 
      let: "max_free" := #100 in 
      callback_loop #0 "tsq" 
    ) ;; 
    let: "tree" := make_pointer_tree "al" #10 in 
    alloc_free_loop "tsq".

  (* hoare triples *)
  Lemma new_tree_hoare γ al : 
    {{{ HAlloc.is_allocator γ al false }}}
      new_tree #al
    {{{ l, RET #l; 
      is_tree γ l 1 true ∗ 
      HAlloc.is_allocator γ al false 
    }}}.
  Proof.
    iIntros (φ) "Hal Hphi". iUnfold new_tree.
    wp_pures. wp_apply (HAlloc.heap_alloc_hoare with "Hal").
    rewrite /HAlloc.BLOCK_SIZE /tree_size.
    iIntros (l) "[(%Hlnp & %Hbs & Hun & Hvl & Hal)|(_ & %H & _)]"; [|lia].
    iDestruct "Hun" as "([%v1 H1] & [%v2 H2] & [%v3 H3] & [%v4 H4] & H5)".
    wp_store. wp_store. wp_store. wp_store. 
    iApply "Hphi". iFrame. rewrite -Z.add_assoc array_singleton. auto.
  Qed.
  
  (* TODO: what to do with all the next pointers 
     we don't store them in the is tree 
     so we can't to tsq rn.. 
     maybe have a boolean that says whether 
     the tree owns its pointer or not!! *)
  Lemma make_pointer_tree_rec_hoare γ al l d : 
    {{{ HAlloc.is_allocator γ al false ∗ l ↦ #NULL }}} 
      make_pointer_tree_rec #al #l #d 
    {{{ RET #(); ∃ l', 
      HAlloc.is_allocator γ al false ∗
      l ↦ #l' ∗ is_tree γ l' d true 
    }}}.
  Proof.
    iInduction d as [|d IH] forall (l); iIntros (φ) "[Hal Hl] Hphi"; 
    iUnfold make_pointer_tree_rec; wp_pures.
    { iApply "Hphi". by iFrame. }
    wp_apply (new_tree_hoare with "Hal"). 
    iIntros (lt) "(Ht & Hal & Hc)". 
    fold make_pointer_tree_rec. wp_pures.
    replace (Z.of_nat (S d) - 1)%Z with (Z.of_nat d) by lia.
    iDestruct "Ht" as (lt1 lt2) "(Hvl & Hlt1 & Hlt2 & -> & -> & Hun)".
    wp_apply ("IH" with "[Hal Hc Hlt1]"); [iFrame|].
    iIntros "(%lt1 & Hal & Hlt1 & Ht1)". wp_pures.
    replace (Z.of_nat (S d) - 1)%Z with (Z.of_nat d) by lia.
    wp_apply ("IH" with "[Hal Hlt2]"); [iFrame|].
    iIntros "(%lt2 & Hal & Hlt2 & Ht2)". wp_store.
    iApply "Hphi". iFrame "Hal Hl". iUnfold is_tree. 
    iExists lt1, lt2. by iFrame.
  Qed.

  Lemma make_pointer_tree_hoare al γ d : 
    {{{ HAlloc.is_allocator γ al false }}} 
      make_pointer_tree #al #d 
    {{{ l, RET #l; HAlloc.is_allocator γ al false ∗ is_tree γ l d true }}}.
  Proof.
    iIntros (φ) "Hal Hphi". iUnfold make_pointer_tree.
    wp_pures. wp_alloc l as "Hl". wp_pures. 
    wp_apply (make_pointer_tree_rec_hoare with "[Hal Hl]"); [iFrame|].
    iIntros "(%l' & Hal & Hl & Ht)". wp_load.
    wp_free. wp_pures. iApply "Hphi". by iFrame.
  Qed.

  Lemma alloc_free_loop_hoare γ (al tsq : loc) ϕ : 
    {{{ HAlloc.is_allocator γ al false ∗ TSIList.is_ts_ilist tsq ϕ }}}
      alloc_free_loop #al #tsq 
    {{{ RET #(); 
      HAlloc.is_allocator γ al false ∗ 
      TSIList.is_ts_ilist tsq ϕ 
    }}}.
  Proof. 
    iLöb as "IH".
    iIntros (φ) "[Hal Htsq] Hphi". iUnfold alloc_free_loop.
    wp_pures. fold alloc_free_loop.
    wp_apply (TSIList.is_empty_hoare with "Htsq").
    iIntros (b) "Htsq". destruct b; wp_pures.
    { iApply "Hphi". by iFrame. }
    wp_bind (HAlloc.heap_alloc _ _ ).
    wp_apply (HAlloc.heap_alloc_hoare with "Hal").
    wp_apply HAlloc.heap_alloc_hoare.  
  Admitted.

  (* TODO(Ben): now also takes tsq ... *)
  Lemma callback_free_hoare γ l d al fo : 
    {{{ HAlloc.is_allocator γ al fo ∗ is_tree γ l d ∗ ∃ v, l ↦ v }}}
      callback_free #l
    {{{ RET #(); 
      HAlloc.is_allocator γ al fo
      }}}.
  Proof.
    iIntros (φ) "(Hal & Ht & %v & Hl) Hphi". iUnfold callback_free.
    wp_pures. wp_apply twp_wp.
    iDestruct (is_tree_unfold with "Ht") as (lt1 lt2) 
    "(Hvl & Hb1 & Hb2 & Hun & Hd)".
    wp_apply (HAlloc.heap_free_hoare with "[Hal Hl Hb1 Hb2 Hun Hvl]").
    - iFrame. admit.
    - 
  Qed.

  (* we can't say anything stronger i think*)
  Lemma callback_loop_hoare (i mf d : nat) (tsq : loc) 
    (ϕ : loc → iProp Σ) : 
    d = mf - i →  
    {{{ TSIList.is_ts_ilist tsq ϕ }}} 
      callback_loop #i #mf #tsq
    {{{ RET #(); TSIList.is_ts_ilist tsq ϕ }}}.
  Proof. Admitted.

  (* make more meaningfull? *)
  Lemma runtime_hoare : 
    {{{ True }}}
      runtime #() 
    {{{ RET #(); True }}}.
  Proof. Admitted.

End DefEx.
