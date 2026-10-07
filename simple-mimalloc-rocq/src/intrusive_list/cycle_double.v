From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.
From AllSrc.intrusive_list Require Import cycle_single.

Module DCycle.
Section Dcycle.
  Context `{!heapGS_gen hlc Σ}.

  Definition reverse_add_1 (L: list loc) : list loc := 
    (λ l, (l + 1)%Z) <$> (reverse L). 
  Definition reverse_sub1 (L: list loc) : list loc := 
    (λ l, (l - 1)%Z) <$> (reverse L).

  Fact reverse_add1_cons l L :
    reverse_add_1 (l :: L) = reverse_add_1 L ++ [(l + 1)%Z].
  Proof. rewrite /reverse_add_1 reverse_cons fmap_app //. Qed.

  Fact reverse_add1_snoc l L :
    reverse_add_1 (L ++ [l]) = (l + 1)%Z :: reverse_add_1 L.
  Proof. 
    rewrite /reverse_add_1 reverse_app reverse_singleton fmap_app //.
  Qed.

  Fact sub1_reverse_add1 L :
    (λ l, (l - 1)%Z) <$> (reverse_add_1 L) = reverse L.
  Proof.
    rewrite /reverse_add_1 -list_fmap_compose.
    rewrite (list_fmap_ext (_ ∘ _) id).
    { by rewrite list_fmap_id. }
    intros i l H; simpl. rewrite -Z.add_sub_assoc.
    replace (1 - 1)%Z with 0%Z by lia. by rewrite Z.add_0_r. 
  Qed.

  Lemma list_nil_or_snoc {A} (L: list A) :
    L = [] ∨ ∃ L' x, L = L' ++ [x].
  Proof.
    induction L as [|x L]; simpl; first by left.
    destruct IHL as [->|(L'&y&->)].
    - right. by exists [], x.
    - right. by exists (x :: L'), y.
  Qed.

  Definition pred c (L: list loc) : iProp Σ :=
    Cycle.pred c L ∗ Cycle.pred (c + 1)%Z (reverse_add_1 L).
  Notation is_dcycle := pred.

  Fact pred_unfold c L :
    is_dcycle c L ⊣⊢ Cycle.pred c L ∗ Cycle.pred (c + 1)%Z (reverse_add_1 L).
  Proof. done. Qed.

  Lemma pred_rotate {c} c' L :
    is_dcycle c (c' :: L) ⊣⊢ is_dcycle c' (L ++ [c]).
  Proof.
    rewrite /pred /reverse_add_1 reverse_cons reverse_app 
    reverse_singleton !fmap_app /=. by rewrite !Cycle.pred_rotate.
  Qed.

  Lemma pred_unique (c : loc) (L : list loc) : 
    is_dcycle c L ⊢ is_dcycle c L ∗ ⌜NoDup (c::L)⌝. 
  Proof. 
    iIntros "(H1 & H2)".
    iPoseProof (Cycle.pred_unique with "H1") as "(H1 & Hd)".
    iFrame.
  Qed.

  Definition new : val := λ: "l",
      Cycle.new ("l" + #0) ;;
      Cycle.new ("l" + #1).

  Definition is_empty : val := λ: "pos", 
    Cycle.is_empty ("pos" + #0).

  Definition next : val := λ: "pos",
    Cycle.next ("pos" + #0).

  Definition prev : val := λ: "pos", 
    (Cycle.next ("pos" + #1)) - #1.

  Definition insert_0 : val := λ: "pos" "new",
      let: "next" := next "pos" in
      Cycle.insert ("next" + #1) ("new" + #1) ;;
      Cycle.insert ("pos" + #0) ("new" + #0).

  Definition insert_1 : val := λ: "pos" "new",
      let: "prev" := prev "pos" in
      Cycle.insert ("prev" + #0) ("new" + #0) ;;
      Cycle.insert ("pos"  + #1) ("new" + #1).

  Definition remove_0 : val := λ: "pos",
      let: "2next" := next (next "pos") in
      let: "l0" := Cycle.remove ("pos" + #0) in
      Cycle.remove ("2next" + #1) ;;
      "l0".

  Definition remove_1 : val := λ: "pos",
      let: "2prev" := prev (prev "pos") in
      Cycle.remove ("pos"   + #1);;
      Cycle.remove ("2prev" + #0).

  Lemma new_spec c v0 v1 :
    {{{ c ↦∗ [v0 ; v1] }}}
      new #c
    {{{ RET #(); is_dcycle c [] }}}.
  Proof. 
    iIntros (φ) "Hc Hphi". iUnfold new. wp_pures. 
    rewrite 2!array_cons. iDestruct "Hc" as "(Hn & Hp & _)".
    wp_apply (Cycle.new_spec with "[Hn]"); [by rewrite Z.add_0_r|].
    iIntros "Hn". wp_pures. wp_apply (Cycle.new_spec with "Hp"). iIntros "Hp".
    rewrite !Cycle.pred_nil Z.add_0_r. iApply "Hphi". iFrame.
  Qed.

  Lemma is_empty_spec c L :
    {{{ is_dcycle c L }}}
      is_empty #c
    {{{ RET #(bool_decide (L = [])); is_dcycle c L }}}.
  Proof. 
    iIntros (φ) "Hid Hphi". iUnfold is_empty. wp_pures. 
    iDestruct "Hid" as "(Hic1 & Hic2)". rewrite Z.add_0_r.
    wp_apply (Cycle.is_empty_spec with "Hic1"). iIntros "Hic1". 
    iApply "Hphi". iFrame.
  Qed.

  Lemma next_spec c (L: list loc) :
    {{{ is_dcycle c L }}}
      next #c
    {{{ RET #((L ++ [c]) !!! 0%nat : loc); is_dcycle c L }}}.
  Proof. 
    iIntros (φ) "(Hic1 & Hic2) Hphi". iUnfold next. 
    wp_pures. rewrite Z.add_0_r. wp_apply (Cycle.next_spec with "Hic1"). 
    iIntros "Hic1". iApply "Hphi". iFrame.
  Qed.

  Lemma prev_spec c (L: list loc) :
    {{{ is_dcycle c L }}}
      prev #c
    {{{ RET #((reverse L ++ [c]) !!! 0%nat : loc); is_dcycle c L }}}.
  Proof.
    iIntros (φ) "(Hic1 & Hic2) Hphi". iUnfold prev. wp_pures.
    wp_apply (Cycle.next_spec with "Hic2"). iIntros "Hic2".
    wp_pures. replace ((reverse_add_1 L ++ [c + 1]) !!! 0%nat - 1)%Z 
    with ((reverse L ++ [c]) !!! 0%nat); [iApply "Hphi"; by iFrame|].
    rewrite /reverse_add_1 -(list_fmap_singleton (λ l, (l + 1)%Z)).
    rewrite -fmap_app list_lookup_total_fmap.
    - rewrite -Z.add_sub_assoc. replace (1 - 1)%Z with 0%Z by lia.
      by rewrite Z.add_0_r.
    - rewrite length_app /=; lia.
  Qed.

  Lemma insert_0_spec c l L v0 v1 :
    {{{ l ↦∗ [v0 ; v1] ∗ is_dcycle c L }}}
      insert_0 #c #l
    {{{ RET #(); is_dcycle c (l :: L) }}}.
  Proof.
    iIntros (φ) "(Hl & (Hic1 & Hic2)) Hphi". iUnfold insert_0.
    rewrite !array_cons array_nil. iDestruct "Hl" as "(Hl & Hl1 & _)".
    wp_pures. wp_apply (next_spec with "[Hic1 Hic2]"); [by iFrame|].
    iIntros "(Hic1 & Hic2)". destruct L; simpl; wp_pures.
    { wp_apply (Cycle.insert_spec with "[Hic2 Hl1]"). 
      - rewrite /reverse_add_1 reverse_nil fmap_nil. iFrame. 
      - iIntros "Hic2". wp_pures. rewrite !Z.add_0_r. 
        wp_apply (Cycle.insert_spec with "[Hic1 Hl]"); [by iFrame|].
        iIntros "Hic1". iApply "Hphi". by iFrame. }
    wp_apply (Cycle.insert_spec with "[Hic2 Hl1]").
    { rewrite reverse_add1_cons -Cycle.pred_rotate. by iFrame. }
    iIntros "Hic2". wp_pures. rewrite !Z.add_0_r. 
    wp_apply (Cycle.insert_spec with "[Hic1 Hl]"); [by iFrame|].
    iIntros "Hic1". iApply "Hphi". rewrite Cycle.pred_rotate 
    -app_comm_cons Cycle.pred_rotate -reverse_add1_cons  
    -reverse_add1_cons. by iFrame.
  Qed.

  Lemma insert_1_spec c l L v0 v1 :
    {{{ l ↦∗ [v0 ; v1] ∗ is_dcycle c L }}}
      insert_1 #c #l
    {{{ RET #(); is_dcycle c (L ++ [l]) }}}.
  Proof.
    iIntros (φ) "(Hl & (Hic1 & Hic2)) Hphi". iUnfold insert_1.
    rewrite !array_cons array_nil. iDestruct "Hl" as "(Hl & Hl1 & _)".
    wp_pures. wp_apply (prev_spec with "[Hic1 Hic2]"); [by iFrame|].
    iIntros "(Hic1 & Hic2)". destruct (list_nil_or_snoc L); 
    [simplify_eq|destruct H as (L' & l' & ->)]; simpl; wp_pures; 
    rewrite !Z.add_0_r.
    { wp_apply (Cycle.insert_spec with "[Hic1 Hl]"); [by iFrame|].
      iIntros "Hic1". wp_pures. 
      wp_apply (Cycle.insert_spec with "[Hic2 Hl1]"); [by iFrame|]. 
      rewrite /reverse_add_1 reverse_nil fmap_nil. iIntros "Hic2".
      iApply "Hphi". by iFrame. }
    assert ((reverse (L' ++ [l']) ++ [c]) !!! 0%nat = l').
    { rewrite reverse_app reverse_singleton !lookup_total_app_l /=; 
      by lia. }
    rewrite H. wp_apply (Cycle.insert_spec with "[Hl Hic1]").
    { rewrite -Cycle.pred_rotate. by iFrame. }
    iIntros "Hic1". wp_pures. 
    wp_apply (Cycle.insert_spec with "[Hl1 Hic2]"); [by iFrame|].
    iIntros "Hic2". iApply "Hphi". rewrite -reverse_add1_snoc 
    Cycle.pred_rotate -app_comm_cons Cycle.pred_rotate. by iFrame.
  Qed.

  Lemma remove_0_spec c l L :
    {{{ is_dcycle c (l :: L) }}}
      remove_0 #c
    {{{ v0 v1, RET #l; is_dcycle c L ∗ l ↦∗ [v0; v1] }}}.
  Proof.
    iIntros (φ) "(Hic1 & Hic2) Hphi". iUnfold remove_0. wp_pures.
    wp_apply (next_spec with "[Hic1 Hic2]"); [by iFrame|].
    iIntros "(Hic1 & Hic2)". wp_pures. wp_apply (next_spec with "[Hic1 Hic2]").
    { iAssert (is_dcycle c (l :: L))%I with "[Hic1 Hic2]" as "Hc"; [by iFrame|].
      by rewrite pred_rotate. }
    iIntros "(Hic1 & Hic2)". wp_pures. rewrite Z.add_0_r. 
    wp_apply (Cycle.remove_spec with "[Hic1]"); [by rewrite -Cycle.pred_rotate|].
    iIntros (v) "Hic1". wp_pures. destruct L; simpl; wp_pures. 
    { wp_apply (Cycle.remove_spec with "[Hic2]"). 
      - by rewrite /reverse_add_1 reverse_singleton list_fmap_singleton 
        Cycle.pred_rotate /=. 
      - iIntros (v') "(Hic2 & Hl1)". wp_pures. iApply "Hphi". 
        iDestruct "Hic1" as "(Hic1 & Hl)". iSplitL "Hic1 Hic2"; [by iFrame|].
        rewrite !array_cons array_nil. by iFrame. }
    iDestruct "Hic1" as "(Hic1 & Hl)".
    wp_apply (Cycle.remove_spec with "[Hic2]").
    { rewrite reverse_add1_cons reverse_add1_snoc. by rewrite -Cycle.pred_rotate. }
    iIntros (v') "(Hic2 & Hl1)". wp_pures. iApply "Hphi". iSplitL "Hic1 Hic2".
    { iSplitL "Hic1"; [done|]. by rewrite !Cycle.pred_rotate reverse_add1_cons. }
    rewrite !array_cons array_nil. by iFrame.
  Qed.

  Lemma remove_1_spec c l L :
    {{{ is_dcycle c (L ++ [l]) }}}
      remove_1 #c
    {{{ v0 v1, RET #l; is_dcycle c L ∗ l ↦∗ [v0; v1] }}}.
  Proof.
    iIntros (φ) "(Hic1 & Hic2) Hphi". iUnfold remove_1. wp_pures.
    wp_apply (prev_spec with "[Hic1 Hic2]"); [by iFrame|].
    iIntros "(Hic1 & Hic2)". 
    assert ((reverse (L ++ [l]) ++ [c]) !!! 0 = l).
    { rewrite reverse_app reverse_singleton !lookup_total_app_l; simpl; try lia. }
    rewrite H. wp_apply (prev_spec with "[Hic1 Hic2]").
    { rewrite reverse_add1_snoc !Cycle.pred_rotate -Cycle.pred_rotate 
      -reverse_add1_cons. by iFrame. }
    iIntros "(Hic1 & Hic2)". wp_pures. 
    wp_apply (Cycle.remove_spec with "[Hic2]");
    [by rewrite reverse_add1_cons -Cycle.pred_rotate|]. 
    iIntros (v) "(Hic2 & Hl1)". 
    destruct (list_nil_or_snoc L); [simplify_eq|destruct H0 as (L' & l' & ->)]; 
    wp_pures.
    { rewrite Z.add_0_r. 
      wp_apply (Cycle.remove_spec with "[Hic1]"); [by rewrite Cycle.pred_rotate|].
      iIntros (v') "(Hic1 & Hl)". iApply "Hphi". iSplitL "Hic1 Hic2"; [by iFrame|].
      rewrite !array_cons array_nil. by iFrame. }
    assert ((reverse (c :: L' ++ [l']) ++ [l]) !!! 0 = l').
    { rewrite reverse_cons reverse_app reverse_singleton !lookup_total_app_l; 
      simpl; try lia. }
    rewrite H0 Z.add_0_r. wp_apply (Cycle.remove_spec with "[Hic1]").
    { by rewrite app_comm_cons -Cycle.pred_rotate. }
    iIntros (v') "(Hic1 & Hl)". iApply "Hphi". iSplitL "Hic1 Hic2".
    - rewrite Cycle.pred_rotate. by iFrame.
    - rewrite !array_cons array_nil. by iFrame.
  Qed.

End Dcycle.
End DCycle.

Global Opaque DCycle.pred 
              DCycle.new DCycle.is_empty DCycle.next DCycle.prev 
              DCycle.insert_0 DCycle.insert_1 
              DCycle.remove_0 DCycle.remove_1.
