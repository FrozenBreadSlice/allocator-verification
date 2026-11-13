From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.
From AllSrc.intrusive_list Require Import ilist.
From AllSrc.iris_heap_lang_asm.lib Require Export spin_lock.

Module TSIList.
Section TSIList.
  Context `{!heapGS_gen hlc Σ, !spin_lockG Σ}.

  Implicit Types l il tsq q : loc.
  Implicit Types L : list loc.

  Definition f_lock : nat := 0.
  Definition f_queue : nat := 1.

  Definition new : val := λ: "_", 
    let: "tsq" := AllocN #3 #1 NONE in 
    let: "lk" := spin_lock.newlock #() in 
    ("tsq" + #f_lock) <- "lk" ;;
    IList.new ("tsq" + #f_queue) ;; 
    "tsq".

  Definition is_empty : val := λ: "tsq", 
    let: "lk" := !("tsq" + #f_lock) in 
    let: "q" := "tsq" + #f_queue in 
    spin_lock.acquire "lk" ;;
    let: "emp" := IList.is_empty "q" in 
    spin_lock.release "lk" ;;
    "emp".

  Definition push_front : val := λ: "tsq" "new", 
    let: "lk" := !("tsq" + #f_lock) in 
    let: "q" := "tsq" + #f_queue in 
    spin_lock.acquire "lk" ;;
    IList.push_front "q" "new" ;;
    spin_lock.release "lk".

  Definition pop_back : val := λ: "tsq", 
    let: "lk" := !("tsq" + #f_lock) in 
    let: "q" := "tsq" + #f_queue in 
    spin_lock.acquire "lk" ;;
    if: IList.is_empty "q" 
    then spin_lock.release "lk" ;; NONE
    else
      let: "l" := IList.pop_back "q" in
      spin_lock.release "lk" ;; 
      SOME "l".

  (* works as intrusive lists only if next pointer is at the top 
   other wise ϕ l for l ∈ L won't mean anything*)
  (* TODO(Ben): maybe make tuple, now can't clean up the list *)
  Definition is_ts_ilist (tsq : loc) (ϕ : loc → iProp Σ) : iProp Σ := 
    ∃ γ lk, (tsq + f_lock) ↦□ lk ∗ 
      spin_lock.is_lock γ lk 
        (∃ L, ([∗ list] l ∈ L, ϕ l) ∗ IList.is_ilist (tsq + f_queue)%Z L).

  Global Instance test tsq ϕ : Persistent (is_ts_ilist tsq ϕ).
  Proof. apply _. Qed.

  Lemma new_hoare ϕ : 
    {{{ True }}}
      new #() 
    {{{ tsq, RET #tsq; is_ts_ilist tsq ϕ }}}.
  Proof. 
    iIntros (φ) "_ Hphi". iUnfold new. wp_pures.
    wp_apply wp_allocN; [lia|lia|done|].
    iIntros (l) "(%Hl & %Hal & H & _)".
    replace (Z.to_nat 3) with (1 + 2) by lia. 
    rewrite replicate_add array_app length_replicate.
    simpl. rewrite array_singleton.
    iDestruct "H" as "[H1 H2]". wp_pures.
    wp_apply spin_lock.newlock_spec_delay_init; [done|].
    iIntros (lk γ) "H". wp_pures. rewrite Z.add_0_r. wp_store.
    wp_pures. wp_apply (IList.new_hoare with "H2").
    iIntros "Hil". wp_pures. iApply "Hphi". iUnfold is_ts_ilist.
    iExists γ, lk. rewrite Z.add_0_r. 
    iMod (pointsto_persist with "H1") as "#H1".
    iSplitR; [iApply "H1"|]. iApply "H". auto.
  Qed.
  
  Lemma is_empty_hoare tsq ϕ :
    {{{ is_ts_ilist tsq ϕ }}}
      is_empty #tsq
    {{{ (b: bool), RET #b; is_ts_ilist tsq ϕ }}}.
  Proof. 
    iIntros (φ) "(%γ & %lk & Hflock & #Hlock) Hphi". 
    iUnfold is_empty. wp_pures. wp_load. wp_pures.
    wp_apply (spin_lock.acquire_spec with "Hlock").
    iIntros "(HLock & %L & Hp & Hq)". wp_pures.
    wp_apply (IList.is_empty_hoare with "Hq").
    iIntros "Hq". wp_pures.
    wp_apply (spin_lock.release_spec with "[HLock Hp Hq]").
    { iFrame. iSplitR; [iApply "Hlock"|]. iFrame. }
    iIntros "_". wp_pures. iApply "Hphi". by iFrame "Hlock Hflock".
  Qed.

  Lemma push_front_hoare tsq l v0 v1 ϕ : 
    {{{ l ↦∗ [v0; v1] ∗ ϕ l ∗ is_ts_ilist tsq ϕ }}} 
      push_front #tsq #l
    {{{ RET #(); is_ts_ilist tsq ϕ }}}.
  Proof. 
    iIntros (φ) "(Hl & Hphil & (%γ & %lk & Hflock & #Hlock)) Hphi".
    iUnfold push_front. wp_pures. wp_load. wp_pures.
    wp_apply (spin_lock.acquire_spec with "Hlock").
    iIntros "(HLock & %L & Hp & Hq)". wp_pures.
    wp_apply (IList.push_front_hoare with "[Hq Hl]"); [iFrame|].
    iIntros "Hq". wp_pures.
    wp_apply (spin_lock.release_spec with "[HLock Hp Hq Hphil]").
    { iFrame. iSplitR; [iApply "Hlock"|]. by iFrame. }
    iIntros "_". iApply "Hphi". by iFrame "Hlock Hflock".
  Qed.

  Lemma pop_back_hoare tsq ϕ :
    {{{ is_ts_ilist tsq ϕ }}}
      pop_back #tsq 
    {{{ vret, RET vret;
      (∃ l v0 v1, ⌜vret = SOMEV #l⌝ ∗ is_ts_ilist tsq ϕ ∗ 
        l ↦∗ [v0; v1] ∗ ϕ l)
        ∨
      (⌜vret = NONEV⌝ ∗ is_ts_ilist tsq ϕ)
    }}}.
  Proof.
    iIntros (φ) "(%γ & %lk & Hflock & #Hlock) Hphi".
    iUnfold pop_back. wp_pures. wp_load. wp_pures.
    wp_apply (spin_lock.acquire_spec with "Hlock").
    iIntros "(HLock & %L & Hp & Hq)". wp_pures.
    wp_apply (IList.is_empty_hoare with "Hq"). iIntros "Hq".
    destruct (DCycle.list_nil_or_snoc L); simplify_eq; wp_pures.
    - wp_apply (spin_lock.release_spec with "[HLock Hp Hq]").
      { iFrame. iSplitR; [iApply "Hlock"|]. auto. }
      iIntros "_". wp_pures. iApply "Hphi". 
      iRight. by iFrame "Hlock Hflock".
    - destruct H as (L' & x & H). case_bool_decide. 
      { simplify_eq. apply app_nil_r_inv in H0. inv H0. }
      wp_pures. rewrite H.
      wp_apply (IList.pop_back_hoare with "Hq").
      iIntros (v0 v1) "[Hq Hl]". wp_pures.
      iDestruct (big_sepL_app with "Hp") as "[Hp [Hl' _]]".
      wp_apply (spin_lock.release_spec with "[HLock Hp Hq]").
      { iFrame. iSplitR; [iApply "Hlock"|]. iFrame. }
      iIntros "_". wp_pures. iApply "Hphi". 
      iLeft. iFrame. iSplitR; [done|]. auto.
  Qed.

End TSIList.
End TSIList.
