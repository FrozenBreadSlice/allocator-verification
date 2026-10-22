From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.
From AllSrc.intrusive_list Require Import seq.

Module Cycle.
Section cycle.
  Context `{!heapGS_gen hlc Σ}.

  Definition pred c (L: list loc) : iProp Σ := Seq.pred c L c.
  Notation is_cycle := pred.

  Fact pred_nil c :
    is_cycle c [] ⊣⊢ c ↦ #c.
  Proof. done. Qed.

  Fact pred_rotate c c' L :
    is_cycle c (c' :: L) ⊣⊢ is_cycle c' (L ++ [c]).
  Proof.
    unfold is_cycle. rewrite Seq.split /=. by apply :comm.
  Qed.

  Lemma pred_unique {c} (L : list loc) : 
    is_cycle c L ⊢ is_cycle c L ∗ ⌜NoDup (c::L)⌝. 
  Proof. apply Seq.pred_unique. Qed.

  Lemma pred_rotateN s' s L1 L2 :
    is_cycle s' (L1 ++ s :: L2) ⊢ is_cycle s (L2 ++ s' :: L1). 
  Proof.
    unfold is_cycle. rewrite !Seq.split. iIntros "(H1 & H2)". iFrame.
  Qed.

  Lemma pred_unique_cycle {s s' l : loc} (L L' : list loc) : 
    l ∈ L → l ∈ L' → 
    is_cycle s L ∗ is_cycle s' L' ⊢ False.
  Proof.
    iIntros (HlL HlL') "(Hc1 & Hc2)".
    assert (∃ L1 L2, L = L1 ++ l :: L2).
    { apply in_split. by apply list_elem_of_In. }
    assert (∃ L1 L2, L' = L1 ++ l :: L2).
    { apply in_split. by apply list_elem_of_In. }
    destruct H as (L1 & L2 & ->).
    destruct H0 as (L1' & L2' & ->).
    rewrite pred_rotateN (pred_rotateN s'). 
    destruct L2', L2; simpl; rewrite /is_cycle !Seq.pred_cons; 
    iDestruct "Hc1" as "(Hc1 & _)"; iDestruct "Hc2" as "(Hc2 & _)"; 
    iCombine "Hc1" "Hc2" gives %[H1 _]; rewrite dfrac_op_own in H1; 
    rewrite dfrac_valid_own in H1; by apply Qp.not_add_le_r in H1.
  Qed.

  Definition new : val      :=  λ: "l", Seq.new "l" "l".

  Definition is_empty : val := λ: "l", !"l" = "l".

  Definition next : val   :=  Seq.next.

  Definition insert : val := Seq.push.

  Definition remove : val := Seq.pop.

  Lemma new_spec c v :
    {{{ c ↦ v }}}
      new #c
    {{{ RET #(); is_cycle c [] }}}.
  Proof.
    iIntros (φ) "Hc Hphi". iUnfold new. wp_pures. 
    by wp_apply (Seq.new_spec with "Hc"). 
  Qed.

  Lemma is_empty_spec c L :
    {{{ is_cycle c L }}}
      is_empty #c
    {{{ RET #(bool_decide (L = [])); is_cycle c L }}}.
  Proof.
    iIntros (φ) "Hic Hphi". unfold is_empty. 
    unfold pred. destruct L as [| x L]; simpl.
    { wp_pures. rewrite Seq.pred_nil. wp_load. wp_pures. 
      case_bool_decide; [by iApply "Hphi"|simplify_eq]. }
    rewrite Seq.pred_cons. iDestruct "Hic" as "[Hc Hic]".
    wp_load. wp_pures. case_bool_decide; [simplify_eq|].
    iModIntro. destruct L; simpl. 
    - rewrite Seq.pred_nil. 
      iPoseProof (pointsto_ne with "Hc Hic") as "%H". contradiction.
    - rewrite Seq.pred_cons. iDestruct "Hic" as "(Hc' & Hic)".
      iPoseProof (pointsto_ne with "Hc Hc'") as "%H". contradiction.
    - iApply "Hphi". by iFrame.
  Qed.

  Lemma next_spec c (L: list loc) :
    {{{ is_cycle c L }}}
      next #c
    {{{ RET #((L ++ [c]) !!! 0%nat : loc); is_cycle c L }}}.
  Proof.
    unshelve eapply Seq.next_spec; eauto.
  Qed.

  Lemma insert_spec {c l v} L :
    {{{ l ↦ v ∗ is_cycle c L }}}
      insert #c #l
    {{{ RET #(); is_cycle c (l :: L) }}}.
  Proof.
    iIntros (φ) "Hc Hphi".
    wp_apply (Seq.push_spec with "Hc"); done.
  Qed.

  Lemma remove_spec c l L :
    {{{ is_cycle c (l :: L) }}}
      remove #c
    {{{ v, RET #l; is_cycle c L ∗ l ↦ v }}}.
  Proof.
    iIntros (φ) "Hc Hphi".
    wp_apply (Seq.pop_spec with "Hc").  
    iIntros (v) "(Hl & Hs)". iApply "Hphi". by iFrame.
  Qed.

End cycle.
End Cycle.

Global Opaque Cycle.pred 
              Cycle.new Cycle.is_empty Cycle.next 
              Cycle.insert Cycle.remove.
