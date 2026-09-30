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
