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
      (* TODO(Ben): make arbitrary values.. *)
      if owns_next then (lt + f_next)%Z ↦∗ [LitV NULL; LitV NULL] 
      else True
    end.

  Definition tsq_inv γ : loc → iProp Σ := 
    λ l, (∃ d, is_tree γ l d false ∗ ⌜0 < d⌝)%I.
  
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
    (if: "tl" ≠ #NULL 
     then TSIList.push_front "tsq" ("tl" + #f_next) 
     else #()) ;;
    if: "tr" ≠ #NULL 
    then TSIList.push_front "tsq" ("tr" + #f_next) 
    else #().

  Definition callback_loop : val := rec: "rec" "i" "max_free" "tsq" := 
    if: "max_free" ≤ "i" then #()
    else 
      let: "l" := TSIList.pop_back "tsq" in 
      if: "l" = #NULL then #() 
      else
        "l" <- #NULL ;;
        ("l" + #1) <- #NULL ;;
        callback_free "l" "tsq" ;;
        "rec" ("i" + #1) "max_free" "tsq". 

  Definition runtime : val := λ: "_", 
    let: "al" := HAlloc.heap_new_alloc #() in  
    let: "tsq" := TSIList.new #() in
    HAlloc.heap_register_callback "al" (λ: "_", 
      let: "max_free" := #100 in 
      callback_loop #0 "max_free" "tsq" 
    ) ;; 
    let: "tree" := make_pointer_tree "al" #10 in 
    TSIList.push_front "tsq" ("tree" + #f_next) ;;
    alloc_free_loop "al" "tsq".

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
      HAlloc.is_allocator γ al false ∗ TSIList.is_ts_ilist tsq ϕ 
    }}}.
  Proof. 
    iLöb as "IH".
    iIntros (φ) "[Hal Htsq] Hphi". iUnfold alloc_free_loop.
    wp_pures. fold alloc_free_loop.
    wp_apply (TSIList.is_empty_hoare with "Htsq").
    iIntros (b) "Htsq". destruct b; wp_pures.
    { iApply "Hphi". by iFrame. }
    wp_apply (HAlloc.heap_alloc_hoare γ al 1 with "Hal").
    iIntros (l) "[(%Hnl & %Hbs & Hun & Hvl & Hal)|(-> & %Hbs & Hal)]"; 
    [|rewrite /HAlloc.BLOCK_SIZE in Hbs; lia]. wp_pures.
    wp_bind (HAlloc.heap_free _). wp_apply twp_wp.
    wp_apply (HAlloc.heap_free_hoare with "[$Hal $Hvl $Hun]").
    iIntros "Hal". wp_pures.
    by wp_apply ("IH" with "[$Hal $Htsq]").
  Qed.

  Lemma callback_free_hoare γ l al d fo tsq : 
    {{{ 
      HAlloc.is_allocator γ al fo ∗ 
      TSIList.is_ts_ilist tsq (tsq_inv γ) ∗
      is_tree γ l (S d) true 
    }}}
      callback_free #l #tsq 
    {{{ RET #(); 
      HAlloc.is_allocator γ al fo ∗ 
      TSIList.is_ts_ilist tsq (tsq_inv γ)
    }}}.
  Proof.
    iIntros (φ) "(Hal & Htsq & Ht) Hphi". iUnfold callback_free.
    wp_pures. destruct d. 
    { iDestruct "Ht" as  (lt1 lt2) "(Hvl & Htl & Htr & 
      -> & -> & Hd & Hl)".
      wp_load. wp_load. wp_pures.
      wp_bind (HAlloc.heap_free _). wp_apply twp_wp.
      rewrite array_cons array_singleton.
      iDestruct "Hl" as "[Hl1 Hl2]".
      wp_apply (HAlloc.heap_free_hoare with 
      "[$Hal Htl Htr Hd Hl1 Hl2 Hvl]").
      - iFrame. rewrite /f_next Z.add_0_r. iFrame.
      - iIntros "Hal". wp_pures. iApply "Hphi". auto. }
    iDestruct "Ht" as (lt1 lt2) "(Hvl & Htl & Htr & 
    H1 & H2 & Hd & Hl)". fold is_tree.
    wp_load. wp_load. wp_pures.
    wp_bind (HAlloc.heap_free _). wp_apply twp_wp.
    iEval (rewrite array_cons array_singleton) in "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    wp_apply (HAlloc.heap_free_hoare with 
    "[$Hal Htl Htr Hd Hl1 Hl2 Hvl]").
    { iFrame. rewrite /f_next Z.add_0_r. iFrame. }
    iIntros "Hal". wp_pures. 
    iDestruct "H1" as (lt1l lt2l) "(Hvll & Htll & Htrl & 
    H1l & H2l & Hdl & Hll)".
    case_bool_decide. 
    { iEval (rewrite array_cons array_singleton) in "Hll". 
      iDestruct "Hll" as "[Hll1 Hll2]".
      iDestruct (pointsto_not_null with "Hll1") as "%Hln".
      rewrite /f_next Z.add_0_r in Hln. simplify_eq. }
    wp_pures. 
    wp_apply (TSIList.push_front_hoare with 
    "[$Htsq Hvll Htll Htrl H1l H2l Hdl $Hll]").
    { iUnfold tsq_inv. iExists (S d). iSplitL; [|iPureIntro; lia].
      iExists lt1l, lt2l. iFrame. rewrite /f_next Z.add_0_r. iFrame. }
    iIntros "Htsq". wp_pures. 
    iDestruct "H2" as (lt1r lt2r) "(Hvlr & Htlr & Htrr & 
    H1r & H2r & Hdr & Hlr)".
    case_bool_decide. 
    { iEval (rewrite array_cons array_singleton) in "Hlr". 
      iDestruct "Hlr" as "[Hlr1 Hlr2]".
      iDestruct (pointsto_not_null with "Hlr1") as "%Hln".
      rewrite /f_next Z.add_0_r in Hln. simplify_eq. }
    wp_pures.
    wp_apply (TSIList.push_front_hoare with 
    "[$Htsq Hvlr Htlr Htrr H1r H2r Hdr $Hlr]").
    { iUnfold tsq_inv. iExists (S d). iSplitL; [|iPureIntro; lia].
      iExists lt1r, lt2r. iFrame. rewrite /f_next Z.add_0_r. iFrame. }
    iIntros "Htsq". iApply "Hphi". auto.
  Qed.

  Lemma callback_loop_hoare γ i mf d fo tsq al : 
    d = mf - i →  
    {{{ 
      HAlloc.is_allocator γ al fo ∗ TSIList.is_ts_ilist tsq (tsq_inv γ) 
    }}} 
      callback_loop #i #mf #tsq
    {{{ RET #(); 
      HAlloc.is_allocator γ al fo ∗TSIList.is_ts_ilist tsq (tsq_inv γ)
    }}}.
  Proof.
    iInduction d as [|d IH] forall (i); simpl; 
    iIntros (Hd φ) "[Hal Htsq] Hphi"; iUnfold callback_loop; wp_pures.
    { case_bool_decide; [|lia]. wp_pures. iApply "Hphi". auto. }
    case_bool_decide; wp_pures; [iApply "Hphi"; auto|].
    wp_apply (TSIList.pop_back_hoare with "Htsq").
    iIntros (l) "[(%v1 & %v2 & %Hnl & Htsq & Hl & Hinv)|(-> & Htsq)]";
    wp_pures; [|iApply "Hphi"; auto].
    case_bool_decide; [simplify_eq|]. wp_pures. fold callback_loop.
    rewrite array_cons array_singleton. iDestruct "Hl" as "[Hl1 Hl2]".
    wp_store. wp_store. 
    rewrite /tsq_inv.  iDestruct "Hinv" as (d') "[Ht %Hd']".
    destruct d'; [lia|].
    wp_apply (callback_free_hoare with "[$Hal $Htsq Ht Hl1 Hl2]").
    { iDestruct "Ht" as (lt1 lt2) "(H1 & H2 & H3 & H4 & H5 & H6 & _)".
      iUnfold is_tree. fold is_tree. iExists lt1, lt2. 
      rewrite array_cons array_singleton /f_next Z.add_0_r. iFrame. }
    iIntros "[Hal Htsq]". wp_pures.
    replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1))%Z by lia.
    wp_apply ("IH" with "[] [$Hal $Htsq]"); [iPureIntro; lia|].
    iIntros "[Hal Htsq]". iApply "Hphi". auto.
  Qed.

  Lemma runtime_hoare : 
    {{{ True }}}
      runtime #() 
    {{{ RET #(); True }}}.
  Proof.
    iIntros (φ) "_ Hphi". iUnfold runtime. wp_pures.
    wp_bind (HAlloc.heap_new_alloc _). wp_apply twp_wp.
    wp_apply (HAlloc.heap_new_alloc_hoare); [done|].
    iIntros (al) "[%γ Hal]". wp_pures.
    wp_apply (TSIList.new_hoare (tsq_inv γ)); [done|].
    iIntros (tsq) "#Htsq". wp_pures.
    wp_bind (HAlloc.heap_register_callback _ _). wp_apply twp_wp.
    wp_apply (HAlloc.heap_register_callback_hoare with "[$Hal]").
    - iIntros (φ'). iModIntro. iIntros "Hh Hphi". wp_pures. 
      wp_apply (callback_loop_hoare γ 0 100 100 true tsq al 
      with "[Hh]"); [done|iFrame "Htsq Hh"|].
      iIntros "[[Hh _] _]". by iApply "Hphi". 
    - iIntros "Hal". wp_pures.
      wp_apply (make_pointer_tree_hoare al γ 10 with "Hal").
      iIntros (l) "[Hal Ht]". wp_pures. wp_let.
  Qed.

End DefEx.
