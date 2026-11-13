From AllSrc.iris_heap_lang_asm Require Import lang notation proofmode.
From AllSrc.allocator Require Import utils.
From AllSrc.allocator Require Import heap_allocator.
From AllSrc.intrusive_list Require Import thread_safe_ilist.

Section DefEx. 
  Context `{!heapGS_gen hlc Σ, !spin_lockG Σ, !my_ghostG Σ}. 
  
  Implicit Types l lt : loc. 

  Definition f_next : nat := 0.
  Definition f_branch1 : nat := 1.
  Definition f_branch2 : nat := 2.

  Definition tree_size := 3.


  (* tree functions *)
  Definition new_tree : val := λ: "al", 
    let: "l" := HAlloc.heap_alloc "al" #tree_size in
    ("l" + #f_branch1) <- #NULL ;; 
    ("l" + #f_branch2) <- #NULL ;; 
    "l".

  Definition tree_free_node : val := λ: "lt", 
    HAlloc.heap_free "lt".

  (* need ilist node pointer for this! *)
  Definition make_pointer_tree_rec : val := rec: "rec" "ln" "d" := 
    if: "d" ≤ #0 then #()  
    else 
      let: "lt" := new_tree #() in 
      "rec" ("lt" + #f_branch1) ("d" - #1) ;; 
      "rec" ("lt" + #f_branch2) ("d" - #1) ;;
      "ln" <- "lt" ;;
      #().

  Definition make_pointer_tree : val := λ: "d", 
    let: "root" := Alloc #NULL in
    make_pointer_tree_rec "root" "d"  
    !"root". 


  (* tree definitions *)
  Fixpoint is_tree (lt : loc) (d : nat) : iProp Σ :=
    ∃ lt1 lt2, 
      (lt + f_branch1) ↦ #lt1 ∗ (lt + f_branch2) ↦ #lt2 ∗
      match d with 
      | 0   => ⌜lt1 = NULL⌝ ∗ ⌜lt2 = NULL⌝ 
      | S d => is_tree lt1 d ∗ is_tree lt2 d
      end.

  Definition ts_queue_inv : loc → iProp Σ := 
    λ l, (∃ d, is_tree l d)%I.
  

  (* runtime functions *)
  Definition alloc_free_loop : val := rec: "rec" "al" "tsq" := 
    if: TSIList.is_empty "tsq" then #() 
    else 
      let: "lt" := new_tree "al" in 
      tree_free_node "lt" ;; 
      "rec" "al" "tsq". 

  Definition callback_loop : val := rec: "rec" "i" "max_free" "tsq" := 
    if: "i" ≤ "max_free" then #()
    else 
      match: TSIList.pop_back "tsq" with 
        SOME "lt" =>  
          tree_free_node "lt" ;;
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
    let: "tree" := make_pointer_tree #10 in 
    alloc_free_loop "tsq".


  (* hoare triples *)
  Lemma new_tree_hoare γ al : 
    {{{ HAlloc.is_heap γ al }}}
      new_tree #al
    {{{ l, RET #l; is_tree l 0 ∗ HAlloc.is_heap γ al }}}.
  Proof. Admitted.

  Lemma tree_free_node_hoare l d : 
    {{{ is_tree l d ∗ ∃ v, l ↦ v }}}
      tree_free_node #l
    {{{ RET #(); True }}}.
  Proof. Admitted.

  Lemma make_pointer_tree_rec_hoare l (d : nat) : 
    {{{ l ↦ #NULL }}} 
      make_pointer_tree_rec #l #d 
    {{{ RET #(); ∃ l', l ↦ #l' ∗ is_tree l' d }}}.
  Proof. Admitted. 

  Lemma make_pointer_tree_hoare d : 
    {{{ True }}} 
      make_pointer_tree #d 
    {{{ l, RET #l; is_tree l d }}}.
  Proof. Admitted.

  Lemma alloc_free_loop_hoare γ (al tsq : loc) ϕ : 
    {{{ HAlloc.is_heap γ al ∗ TSIList.is_ts_ilist tsq ϕ }}}
      alloc_free_loop #al #tsq 
    {{{ RET #(); HAlloc.is_heap γ al ∗ TSIList.is_ts_ilist tsq ϕ }}}.
  Proof. Admitted.

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
