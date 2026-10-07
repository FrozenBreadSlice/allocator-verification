From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.

Module Seq.
Section seq.
  Context `{!heapGS_gen hlc Σ}.

  Definition new : val := λ: "start" "end", 
    "start" <- "end".

  Definition push : val := λ: "start" "new",
    "new"   <- !"start" ;;
    "start" <- "new".

  Definition pop : val := λ: "start",
    let: "rem" := ! "start" in
    "start" <- ! "rem" ;;
    "rem".

  Definition next : val := λ: "start", 
    ! "start".

  Fixpoint pred (s: loc) (L: list loc) (e: loc) : iProp Σ :=
    match L with
      | []          => s ↦ #e
      | next :: L'  => s ↦ #next ∗ pred next L' e
    end.
  Notation is_seq := pred.

  Fact pred_nil {s e: loc} :
    is_seq s [] e ⊣⊢ s ↦ #e.
  Proof. done. Qed.

  Fact pred_cons {s x e: loc} (L: list loc) :
    is_seq s (x :: L) e ⊣⊢ s ↦ #x ∗ is_seq x L e.
  Proof. done. Qed.

  Lemma split {s g e: loc} (L R: list loc) :
    is_seq s (L ++ g :: R) e ⊣⊢ is_seq s L g ∗ is_seq g R e.
  Proof.
    induction L as [| x L] in s, g, e, R |- *; simpl; 
    try rewrite IHL; [done|]. iSplitR. 
    - iIntros "(Hs & His1 & His2)". iFrame. 
    - iApply bi.sep_assoc'. 
  Qed.

  Lemma pred_start_unique {s e : loc} (L R : list loc) :
    is_seq s (L ++ s :: R) e ⊢ False.
  Proof.
    iIntros "H". destruct L.
    - simpl. destruct R; simpl.
      + iDestruct "H" as "(H1 & H2)".
        iCombine "H1" "H2" gives %[H1 H2].
        auto.
      + iDestruct "H" as "(H1 & H2 & H3)".
        iCombine "H1" "H2" gives %[H1 H2].
        auto.
    - iAssert (is_seq s (l :: L) s ∗ is_seq s R e)%I with "[H]" as "H".
      + by iApply split.
      + destruct R; simpl.
        * iDestruct "H" as "((H1 & H2) & H3)".
          iCombine "H1" "H3" gives %[H1 H2].
          auto.
        * iDestruct "H" as "((H1 & H2) & H3 & H4)".
          iCombine "H1" "H3" gives %[H1 H2].
          auto.
  Qed.

  Lemma pred_start_unique_elem_of {s e : loc} (L : list loc) :
    s ∈ L -> is_seq s L e ⊢ False.
  Proof.
    iIntros (H) "H".
    assert (∃ L1 L2, L = L1 ++ s :: L2).
    { apply list_elem_of_In in H. by apply In_split in H. } 
    destruct H0 as (L1 & L2 & ->).
    by iApply pred_start_unique. 
  Qed.

  Lemma pred_list_unique {s e : loc} (L : list loc) : 
    is_seq s L e ⊢ is_seq s L e ∗ ⌜NoDup L⌝. 
  Proof.
    iInduction L as [|x L IH] forall (s e); simpl; iIntros "H".
    { iFrame. iPureIntro. by apply NoDup_nil. }
    iDestruct "H" as "(Hs & His)". iSpecialize ("IH" with "His").
    destruct (decide (x ∈ L)).
    - iPoseProof (pred_start_unique_elem_of) as "H"; [apply e0|]. 
      iDestruct "IH" as "(H' & H'')". iSpecialize ("H" with "H'").
      by iExFalso.
    - iDestruct "IH" as "(H & %H')". iFrame. iPureIntro.
      by apply NoDup_cons_2.
  Qed.

  Lemma pred_unique {s e : loc} (L : list loc) : 
    is_seq s L e ⊢ is_seq s L e ∗ ⌜NoDup (s::L)⌝. 
  Proof.
    iIntros "H'". destruct (decide (s ∈ L)).
    - iPoseProof (pred_start_unique_elem_of) as "H"; [apply e0|]. 
      iSpecialize ("H" with "H'"). by iExFalso.
    - iPoseProof (pred_list_unique with "H'") as "H". 
      iDestruct "H" as "(H & %H)". iFrame. iPureIntro.
      by apply NoDup_cons_2.
  Qed.

  Lemma new_spec {s e: loc} {v} :
    {{{ s ↦ v }}} 
      new #s #e
    {{{ RET #(); is_seq s [] e }}}.
  Proof. iIntros (φ) "Hs Hphi". iUnfold new. wp_store. iApply "Hphi". by iFrame. Qed.

  Lemma push_spec {s l e: loc} (L: list loc) v :
    {{{ l ↦ v ∗ is_seq s L e }}} 
      push #s #l
    {{{ RET #(); is_seq s (l :: L) e }}}.
  Proof. 
    iIntros (φ) "(Hl & Hs) Hphi". iUnfold push. wp_pures.
    destruct L; [|iDestruct "Hs" as "(Hs & His)"]; wp_load; 
    wp_store; wp_store; iApply "Hphi"; by iFrame.
  Qed.

  Lemma pop_spec {s e l: loc} (L: list loc) :
    {{{ is_seq s (l :: L) e }}}
      pop #s
    {{{ v, RET #l; l ↦ v ∗ is_seq s L e }}}.
  Proof. 
    iIntros (φ) "(Hs & His) Hphi". iUnfold pop. wp_load.
    destruct L; [|iDestruct "His" as "(Hl & His)"]; wp_load; 
    wp_store; iApply "Hphi"; fold pred; by iFrame.
  Qed.

  Lemma next_spec {s n e : loc} (L R: list loc) :
    {{{ is_seq s L e }}}
      next #s
    {{{ RET #((L ++ [e]) !!! 0%nat : loc); is_seq s L e }}}.
  Proof. 
    iIntros (φ) "His Hphi". iUnfold next. destruct L; 
    [|iDestruct "His" as "(Hs & His)"];  wp_load; iApply "Hphi"; 
    fold pred; by iFrame.
  Qed.

End seq.
End Seq.

Global Opaque Seq.pred Seq.new Seq.push Seq.pop Seq.next.
