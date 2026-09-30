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
