From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.
From AllSrc.iris_heap_lang_asm.lib Require Import assert.
From AllSrc.allocator Require Import page_allocator.
From AllSrc.intrusive_list Require Import ilist.
From AllSrc.allocator Require Import utils.
From AllSrc.allocator Require Import heap_ghost_state.

From AllSrc.iris_heap_lang_asm.lib Require Import diverge.
(* Heap allocator

*)

Definition my_ghostΣ : gFunctors := #[GFunctor (authR (gmultisetUR loc))].

Instance subG_my_ghostΣ {Σ} : subG my_ghostΣ Σ → my_ghostG Σ.
Proof. solve_inG. Qed.

Module HAlloc. Section HAlloc.

  Context `{!heapGS_gen hlc Σ, !my_ghostG Σ}.
 
  Implicit Types al l lq lf : loc.
  Implicit Types res bs fbs i n : nat.
  Implicit Types Lq Lf : list loc.
  Implicit Types γ : gname.

  (* index in page for things owned by heap *)
  Definition f_list : nat := 0.
  Definition f_in_full : nat := 2.
  Definition f_heap : nat := 3.

  (* index in heap *)
  Definition f_queue : nat := 0.
  Definition f_full : nat := 2.
  
  (* other constans *)
  Definition num_f : nat := 2.
  Definition queue_size : nat := 2.

  (* TODO(Ben): more queues with block sizes later *)
  Definition BLOCK_SIZE : nat := 16. 
  Definition PAGE_ALIGN : nat := 128.  

  (* 
    function definitions
  *)

  Definition heap_new_alloc : val := λ: "_", 
    let: "al" := AllocN (#num_f * #queue_size) #1 NONE in 
    IList.new ("al" + #f_queue) ;;
    IList.new ("al" + #f_full) ;;
    "al".

  Definition heap_free : val := λ: "l", 
    let: "lmd" := ("l" `quot` #PAGE_ALIGN) * #PAGE_ALIGN in
    if: !("lmd" + #f_in_full) 
    then 
      let: "heap" := !("lmd" + #f_heap) in 
      match: IList.remove ("heap" + #f_full) ("lmd" + #f_list) with 
        NONE => assert:#false 
      | SOME "lp" => 
        IList.push_front ("heap" + #f_queue) "lp" ;;
        ("lp" + #f_in_full) <- #false ;;
        PAlloc.page_free "lmd" "l" ;; #()
      end
    else  
      PAlloc.page_free "lmd" "l";; #(). 
  (* TODO(Ben): can we remove this and still get fancy update?*)

  Definition queue_alloc : val := rec: "rec" "bsq" "full" := 
    if: IList.is_empty "bsq" then NONE 
    else 
      let: "lp" := IList.prev "bsq" in
      match: PAlloc.page_alloc "lp" with 
        NONE => 
          let: "lp'" := IList.pop_back "bsq" in 
          IList.push_front "full" "lp'" ;;
          ("lp'" + #f_in_full) <- #true ;;
          "rec" "bsq" "full" 
      | SOME "l" => SOME "l"
      end.

   Definition heap_alloc : val := λ: "al" "n", 
    if: #BLOCK_SIZE < "n" then NONE 
    else
      let: "bsq" := ("al" + #f_queue) in 
      let: "full" := ("al" + #f_full) in 
      match: queue_alloc "bsq" "full" with 
        NONE => 
          let: "res" := #(Z.to_nat (PAGE_ALIGN `quot` BLOCK_SIZE - 1)) in
          let: "lp" := 
            PAlloc.page_new_alloc "res" #BLOCK_SIZE #PAGE_ALIGN in 
          IList.push_front "bsq" "lp" ;;
          let: "l" := PAlloc.page_alloc "lp" in 
          ("lp" + #f_in_full) <- #false ;;
          ("lp" + #f_heap) <- "al" ;;
          "l"
      | SOME "l" => SOME "l"
      end.

  (* 
    Representation
  *)
  Local Definition alignment_condition (a bs res mds : nat) := 
    0 < a ∧ 0 < bs ∧ mds < bs ∧ 0 < res ∧ 
    res = Z.to_nat (a `quot` bs - 1)%Z. 
   
  Definition is_heap_internal γ (al : loc) (Lq Lf : list loc) : iProp Σ :=
    ∃ res (L : gmultiset loc), 
      ⌜PAlloc.MDSIZE < BLOCK_SIZE⌝ ∗
      ⌜res = Z.to_nat (PAGE_ALIGN `quot` BLOCK_SIZE - 1)%Z⌝ ∗
      ⌜dom L = list_to_set (Lq ++ Lf)⌝ ∗
      my_auth γ L ∗ 
      IList.is_ilist (al + f_queue)%Z Lq ∗ 
      IList.is_ilist (al + f_full)%Z Lf ∗
      ([∗ list] lp ∈ Lq,  
          ∃ fbs,
          ⌜(multiplicity lp L = (res - fbs) + 1)%nat⌝ ∗
          my_frac γ lp ∗ (*TODO(Ben): probably needed for dealloc?*)
          ⌜(PAGE_ALIGN | lp)%Z⌝ ∗
          PAlloc.is_page lp BLOCK_SIZE res fbs ∗ 
          (lp + f_in_full)%Z ↦ #false ∗
          (lp + f_heap)%Z ↦ #al) ∗
      ([∗ list] lp ∈ Lf, 
          ∃ fbs,
          ⌜(multiplicity lp L = (res - fbs) + 1)%nat⌝ ∗
          my_frac γ lp ∗
          ⌜(PAGE_ALIGN | lp)%Z⌝ ∗
          PAlloc.is_page lp BLOCK_SIZE res fbs ∗ 
          (lp + f_in_full)%Z ↦ #true ∗
          (lp + f_heap)%Z ↦ #al).

  Definition is_heap γ al : iProp Σ := 
    ∃ Lq Lf, is_heap_internal γ al Lq Lf.

  Definition is_valid_loc γ (l al : loc) : iProp Σ := 
    let lmd := down_align l PAGE_ALIGN in 
    my_frac γ lmd ∗   
    PAlloc.is_valid_loc l lmd.
  
  (*
    Hoare triples and proofs
  *)

  Local Lemma sanity_check (a bs res mds : nat) : 
    alignment_condition a bs res mds → 
    mds + res * bs < a. 
  Proof. 
    intros (Ha & Hbs1 & Hbs2 & Hres & Hreseq).
    intros. simplify_eq.
    assert (2 ≤ a `quot` bs)%Z by lia.
    replace (Z.to_nat (a `quot` bs - 1) * bs) 
    with (Z.to_nat (a `quot` bs * bs) - bs) by lia. 
    assert (a `quot` bs * bs ≤ a)%Z.
    { apply quot_mult_bound; lia. } lia. 
  Qed.

  Local Lemma down_align_location_general (lin lbase : loc) (i mds bs res a : nat) : 
    alignment_condition a bs res mds → 
    (a | lbase)%Z → 
    (0 < lbase)%Z →
    i < res → 
    lin = (lbase + mds + i * bs)%Z → 
    down_align lin a = lbase.
  Proof. 
    intros (Ha0 & Hbs & Hbsmds & Hres & Hreseq) Hlba Hlb0 Hir Hlineq.
    apply down_align_in_range; try done; [lia|]. rewrite Hlineq. 
    assert (0 ≤ mds + i * bs < a); [|lia]. split; [lia|].
    assert (mds + res * bs < a); [|nia].
    apply sanity_check. unfold alignment_condition. auto.
  Qed.

  Local Lemma down_align_location l l' i : 
    (PAlloc.MDSIZE < BLOCK_SIZE)%Z → 
    (0 < l')%Z →
    (PAGE_ALIGN | l')%Z → 
    i < Z.to_nat (PAGE_ALIGN `quot` BLOCK_SIZE - 1) → 
    l = (l' + PAlloc.MDSIZE + i * BLOCK_SIZE)%Z → 
    down_align l PAGE_ALIGN = l'.
  Proof. 
    intros Hbs Hl Hla Hi Heql.
    remember (Z.to_nat (PAGE_ALIGN `quot` BLOCK_SIZE - 1)) as res.
    apply (down_align_location_general 
      l l' i PAlloc.MDSIZE BLOCK_SIZE res PAGE_ALIGN); try done.
    rewrite /alignment_condition /PAlloc.MDSIZE /BLOCK_SIZE /PAGE_ALIGN.
    repeat (split; (try (done || lia))).
  Qed.

  Local Lemma in_internal_lists γ al l Lq Lf : 
    is_heap_internal γ al Lq Lf -∗ 
    is_valid_loc γ l al -∗ 
    is_heap_internal γ al Lq Lf ∗ is_valid_loc γ l al ∗ 
    ⌜down_align l PAGE_ALIGN ∈ (Lq ++ Lf)⌝.
  Proof.
    iIntros "Hh Hvl".
    iDestruct "Hh" as "(%res & %L & %Hc1 & %Hc2 & %Hdom & Hauth & Hil1 &
    Hil2 & Hp1 & Hp2)".
    iDestruct "Hvl" as "(Hfrac & Hvl)".
    remember (down_align l PAGE_ALIGN) as lmd.
    iAssert (⌜lmd ∈ L⌝ -∗ ⌜lmd ∈ (Lq ++ Lf)⌝)%I as "H".
    { iPureIntro. intros. set_solver. }
    iPoseProof (my_auth_my_frac_agree with "Hauth Hfrac") as "%H'".
    iFrame. iSplit; [auto|]. iSplitL; [rewrite Heqlmd; iFrame|].
    by iApply "H".
  Qed.
     
  Lemma heap_new_alloc_hoare :
    {{{ emp }}}
      heap_new_alloc #() 
    {{{ al, RET #al; ∃ γ, is_heap γ al }}}.
  Proof. 
    iIntros (φ) "_ Hphi". iUnfold heap_new_alloc. wp_pures.
    wp_apply wp_allocN; [done|done|done|]. iIntros (l) "(_ & _ & [Hl _])".
    wp_pures. unfold num_f, queue_size. 
    replace (Z.to_nat (2%nat * 2%nat)) with (2 + 2) by lia.
    rewrite replicate_add array_app length_replicate.
    iDestruct "Hl" as "(H1 & H2)". simpl.
    wp_apply (DCycle.new_spec with "[H1]"); [by rewrite Z.add_0_r|].
    iIntros "Hq". wp_pures. wp_apply (DCycle.new_spec with "H2"). 
    iIntros "Hf". wp_pures. iApply "Hphi". iUnfold is_heap.
    iFrame. simpl. 
    iPoseProof (my_auth_unit) as "H". 
    iMod "H" as (γ) "Hauth". 
    iExists γ, _, (∅ : gmultiset loc). iSplitR.
    { rewrite /PAlloc.MDSIZE /BLOCK_SIZE. iPureIntro. lia. }
    iSplitR; [done|]. iSplitR. 
    { iPureIntro. set_solver. } auto.
  Qed.
  
  Lemma heap_free_hoare γ l al : 
    {{{ 
      is_heap γ al ∗ ([∗ list] i ∈ seq 0 BLOCK_SIZE, ∃ v, (l + i)%Z ↦ v) ∗ 
      is_valid_loc γ l al
    }}}
      heap_free #l 
    {{{ RET #(); is_heap γ al }}}.
  Proof. 
    iIntros (φ) "((%Lq & %Lf & Hh) & Hun & Hvl) Hphi".
    iPoseProof (in_internal_lists with "Hh Hvl") as 
    "(Hh & (Hfrac & Hvl) & %HinL)". 
    iDestruct "Hh" as "(%res & %L & %Hr1 & %Hr2 & %Hdom & Hauth & Hil1 & 
    Hil2 & Hp1 & Hp2)". iUnfold heap_free. wp_pures.
    remember (down_align l PAGE_ALIGN) as lmd.
    assert (l `quot` PAGE_ALIGN * PAGE_ALIGN = lmd)%Z by done. rewrite H. 
    apply elem_of_app in HinL. destruct HinL.
    - iPoseProof (IList.pred_unique with "Hil1") as "(Hil1 & %Hd)".
      apply NoDup_cons in Hd as [Hd1 Hd2].
      destruct (list_elem_of_split _ _ H0) as (L1 & L2 & HLq). rewrite HLq. 
      iPoseProof ((big_sepL_get_middle _ L1 L2 lmd) with "Hp1") 
      as "((%fbs & %Hm & Hfracp & %Ha & Hp & Hif & Hh) & Hp1)". wp_load. wp_pures. 
      wp_apply (PAlloc.page_free_hoare with "[Hp Hun Hvl]"); [iFrame|].
      iIntros "Hp". wp_pures. iApply "Hphi". iExists Lq, Lf, res.
      destruct (decide (lmd ∈ Lf)). (* this gets us lmd ∉ Lf, needed later *)
      { iPoseProof (IList.pred_unique_cycle with "[Hil1 Hil2]") as "%H'"; 
        [apply e|apply H0|rewrite HLq; iFrame|done]. }
      iExists (L ∖ {[+ lmd +]}). rewrite -HLq. iFrame.
      iSplitR; [done|]. iSplitR; [done|]. destruct (decide (res < S (fbs))).
      { by iPoseProof (PAlloc.page_res_geq_fbs with "Hp") as "Hcon". }
      assert (multiplicity lmd L > 1)by lia. 
      iSplitR. { iPureIntro. rewrite -Hdom. multiset_solver. }
      iSplitL "Hauth Hfrac". 
      { by iPoseProof (my_auth_my_frac_dealloc with "Hauth Hfrac") as "H". }
      iSplitR "Hp2".
      { rewrite HLq. iApply big_sepL_get_middle.
        iSplitR "Hp1". 
        - iFrame. iSplitR; [|done]. iPureIntro. 
          rewrite multiplicity_difference multiplicity_singleton_eq. lia.
        - iApply big_sepL_mono; [|done]. iIntros (k y Hl) "(%fbs' & %Hmult2 
          & Hay & Hpy & Hyinf & Hyh)". iFrame. iPureIntro.
          assert (lmd ∉ (L1 ++ L2)).
          { apply NoDup_cons_middle. by rewrite -HLq. }
          rewrite multiplicity_difference. assert (y ≠ lmd). 
          { apply list_elem_of_lookup_2 in Hl. set_solver. }
          rewrite multiplicity_singleton_ne; [|done]. 
          by rewrite Nat.sub_0_r. }
      iApply big_sepL_mono; [|done]. iIntros (k y Hl) "(%fbs' & %Hmult2 
      & Hay & Hpy & Hyinf & Hyh)". iFrame.
      iPureIntro. rewrite multiplicity_difference. assert (y ≠ lmd). 
      { apply list_elem_of_lookup_2 in Hl. set_solver. }
      rewrite multiplicity_singleton_ne; [|done]. by rewrite Nat.sub_0_r.
  - iPoseProof (IList.pred_unique with "Hil2") as "(Hil2 & %Hd)".
    apply NoDup_cons in Hd as [Hd1 Hd2].
    destruct (decide (lmd ∈ Lq)). (* this gets us lmd ∉ Lq, needed later *)
    { iPoseProof (IList.pred_unique_cycle with "[Hil1 Hil2]") as "%H'"; 
      [apply H0|apply e|iFrame|done]. }
    destruct (list_elem_of_split _ _ H0) as (L1 & L2 & HLf). rewrite HLf. 
    iPoseProof ((big_sepL_get_middle _ L1 L2 lmd) with "Hp2") 
    as "((%fbs & %Hm & Hfracp & %Ha & Hp & Hif & Hh) & Hp2)". 
    wp_load. wp_pures. wp_load. wp_pures. 
    wp_apply (IList.remove_hoare with "[Hil2]"); [by rewrite Z.add_0_r|].
    iIntros "(Hlmdl & Hil2)". wp_pures.
    wp_apply (IList.push_front_hoare with "[Hlmdl Hil1]"); [iFrame|].
    iIntros "Hil1". rewrite !Z.add_0_r. wp_store. 
    wp_apply (PAlloc.page_free_hoare with "[Hp Hun Hvl]"); [iFrame|].
    iIntros "Hp". wp_pures. iApply "Hphi". iExists (lmd::Lq), (L1 ++ L2), res.
    destruct (decide (res < S (fbs))).
    { by iPoseProof (PAlloc.page_res_geq_fbs with "Hp") as "Hcon". }
    assert (multiplicity lmd L > 1) by lia. 
    iExists (L ∖ {[+ lmd +]}). rewrite Z.add_0_r. iFrame. 
    iSplitR; [done|]. iSplitR; [done|]. 
    iSplitR. 
    (* TODO(Ben): help multiset_solver here or remove for the easy proof*)
    { assert (dom L = list_to_set ((lmd :: Lq) ++ L1 ++ L2)) 
      by multiset_solver. rewrite -H2. iPureIntro. multiset_solver. }
    iSplitL "Hauth Hfrac".
    { by iPoseProof (my_auth_my_frac_dealloc with "Hauth Hfrac") as "H". }
    iSplitL "Hp1".
    { iSplitR. 
      - iSplitR; [|done]. iPureIntro. rewrite multiplicity_difference 
        multiplicity_singleton_eq. lia.
      - iApply big_sepL_mono; [|done]. 
        iIntros (k y Hl) "(%fbs' & %Hmult & Ha' & Hp & Hinf & Hh)". 
        iFrame. iPureIntro. rewrite multiplicity_difference 
        multiplicity_singleton_ne. lia.
        apply list_elem_of_lookup_2 in Hl. set_solver. }
    iApply big_sepL_mono; [|done]. 
    iIntros (k y Hl) "(%fbs' & %Hmult & Ha' & Hp & Hinf & Hh)". 
    iFrame. iPureIntro. rewrite multiplicity_difference 
    multiplicity_singleton_ne. lia.
    assert (lmd ∉ (L1 ++ L2)); [apply NoDup_cons_middle; by rewrite -HLf|].
    apply list_elem_of_lookup_2 in Hl. set_solver.
  Qed.
 
  Local Lemma queue_alloc_hoare γ al Lq Lf : 
    {{{ is_heap_internal γ al Lq Lf }}} 
      queue_alloc #(al + f_queue) #(al + f_full) 
    {{{ vret, RET vret; 
      (∃ Lq' L Lf' l, ⌜vret = SOMEV #l⌝ ∗ 
        ⌜Lq = Lq' ++ L⌝ ∗ ⌜Lf' = L ++ Lf⌝ ∗
        ([∗ list] i ∈ seq 0 BLOCK_SIZE, ∃ v, (l + i)%Z ↦ v) ∗ 
        is_valid_loc γ l al ∗
        is_heap_internal γ al Lq' Lf') 
      ∨
      (⌜vret = NONEV⌝ ∗ is_heap_internal γ al [] (Lq ++ Lf))
    }}}.
  Proof. 
    revert Lf. induction Lq using rev_ind; iIntros (Lf φ) "(%res & %L & %Hr 
    & %Hr2 & %Hdom & Hauth & Hil1 & Hil2 & Hp1 & Hp2) Hphi"; 
    iUnfold queue_alloc; wp_pures; 
    wp_apply (IList.is_empty_hoare with "Hil1"); iIntros "Hil1"; wp_pures. 
    { iApply "Hphi". iRight. by iFrame. }
    case_bool_decide.
    { specialize (app_nil_r_inv _ _ H) as H'. inversion H'. }
    wp_pures. wp_apply (IList.prev_hoare with "Hil1").
    iIntros "Hil1". 
    assert (((reverse (Lq ++ [x]) ++ [(al + f_queue)%Z]) !!! 0%nat) = x) 
    as Hind. 
    { rewrite reverse_snoc. rewrite lookup_total_app_l; 
      simpl; [done|lia]. }
    rewrite Hind. wp_pures. 
    iPoseProof (big_sepL_snoc with "Hp1") as "(Hp1 & Hpx)".
    iDestruct "Hpx" as "(%fbs & %Hml & Hfracx & %Hax & Hp & Hinf & Hal)".
    destruct (decide (res < fbs)).
    { by iPoseProof (PAlloc.page_res_geq_fbs with "Hp") as "Hcon". }
    iPoseProof (IList.pred_unique with "Hil1") as "(Hil1 & %Hnd)".  
    apply NoDup_cons_1_2 in Hnd. apply NoDup_snoc in Hnd as [Hnd1 Hnd2].
    destruct (decide (x ∈ Lf)).
    { iPoseProof (IList.pred_unique_cycle with "[Hil1 Hil2]") as "H"; 
      [apply e| | iFrame|done]. apply elem_of_app. right. 
      by apply list_elem_of_singleton. }
    wp_apply (PAlloc.page_alloc_hoare with "Hp").
    iIntros (v) "[H | H]".
    - iDestruct "H" as "(%l & -> & %Hfbs & Hun & Hvl & Hp)". 
      iPoseProof (PAlloc.get_usefull_pure_facts with "Hp Hvl") 
      as "((%ld & %i & %Hld & %Hl & %Hi) & %Hlp' & %Hr0)".
      wp_pures. iApply "Hphi". 
      assert (down_align l PAGE_ALIGN = x) as Hx.
      { apply (down_align_location l x i); [lia|done|done|lia|lia]. }
      iLeft. iExists (Lq ++ [x]), [], Lf, l. iSplitR; [done|]. 
      iSplitR; [by rewrite app_nil_r|]. iSplitR; [by rewrite app_nil_l|].
      iSplitL "Hun"; [done|].
      iPoseProof (my_auth_my_frac_alloc with "Hauth") as "Hauth".
      iMod "Hauth" as "(Hauth & Hfrac)".
      iSplitL "Hvl Hfrac"; [iFrame; by rewrite Hx|]. rewrite Hx.
      iExists res. iExists (L ⊎ {[+ x +]}).
      iSplitR; [iPureIntro; lia|]. iSplitR; [done|].
      iFrame. iSplitR. 
      { iPureIntro. apply set_eq. set_solver. }
      iSplitL "Hp1".
      { rewrite big_sepL_nil. iSplitL.
        - iApply big_sepL_mono; [|done]. 
          iIntros (k y Hl') "(%fbs' & %Hmult & Hay & Hpy & Hinfy & Hhy)". 
          iFrame. iPureIntro. apply list_elem_of_lookup_2 in Hl'. 
          rewrite multiplicity_disj_union.
          rewrite multiplicity_singleton_ne; [lia|set_solver]. 
        - iSplitR; [|done]. iSplitR; [|done]. iPureIntro.
          rewrite multiplicity_disj_union multiplicity_singleton_eq.
          lia. } 
      iApply big_sepL_mono; [|done]. 
      iIntros (k y Hl') "(%fbs' & %Hmult & Hay & Hpy & Hinfy & Hhy)". 
      iFrame. iPureIntro. apply list_elem_of_lookup_2 in Hl'. 
      rewrite multiplicity_disj_union.
      rewrite multiplicity_singleton_ne; [lia|set_solver]. 
    - iDestruct "H" as "(-> & -> & Hp)". wp_pures.
      wp_apply (IList.pop_back_hoare with "Hil1"). 
      iIntros (v1 v2) "(Hil1 & Hx)". wp_pures.
      wp_apply (IList.push_front_hoare with "[Hil2 Hx]"); [iFrame|].
      iIntros "Hil2". wp_pures. wp_store. fold queue_alloc.
      iApply (IHLq with "[Hp1 Hp2 Hil1 Hil2 Hauth Hp Hinf Hal Hfracx]"). 
      { iFrame. iFrame. iSplitR; [iPureIntro; lia|]. 
        rewrite -app_assoc /= in Hdom. auto. }
      iNext. iIntros (v) "[H | H]". iApply "Hphi". 
      { iDestruct "H" as "(%Lq' & %Lf'' & %Lf' & %l & -> & -> & -> &
        Hlbs & Hivl & Hal)". iLeft. iExists Lq', (Lf'' ++ [x]), 
        (Lf'' ++ [x] ++ Lf). iFrame. iSplitR; [done|]. 
        iSplitR; [by rewrite app_assoc|]. by rewrite app_assoc. }
      iApply "Hphi". iRight. by rewrite -app_assoc /=.
  Qed.

  Lemma heap_alloc_hoare γ al n : 
    {{{ is_heap γ al }}} 
      heap_alloc #al #n
    {{{ vret, RET vret; 
       (∃ l, ⌜vret = SOMEV #l⌝ ∗ 
          ([∗ list] i ∈ seq 0 BLOCK_SIZE, ∃ v, (l + i)%Z ↦ v) ∗ 
          is_valid_loc γ l al ∗ is_heap γ al)
        ∨ 
      ⌜vret = NONEV⌝ ∗ is_heap γ al 
    }}}.
  Proof. 
    iIntros (φ) "(%Lq & %Lf & %res & %L & %Hr & %Hr2 & %Hdom & Hauth & Hil1 
    & Hil2 & Hp1 & Hp2) Hphi". 
    iUnfold heap_alloc. wp_pures. case_bool_decide.
    { wp_pures. iApply "Hphi". iRight. by iFrame. } 
    wp_pures. 
    wp_apply (queue_alloc_hoare with "[Hauth Hil1 Hil2 Hp1 Hp2]"); 
    [by iFrame|]. iIntros (v) "[H | H]".
    { iDestruct "H" as "(%Lq' & %Ld & %Lf' & %l &->&->&->& Hl &Hlv & Hh)".
      wp_pures. iApply "Hphi". iLeft. by iFrame. }
    iDestruct "H" as "(-> & %res' & %L' & %Hr' & %Hr2' & %Hdom' & Hauth & 
    Hil1 & Hil2 & Hp1 & Hp2)". wp_pures. 
    wp_apply (PAlloc.page_new_alloc_hoare _ BLOCK_SIZE PAGE_ALIGN).
    { iPureIntro. rewrite /BLOCK_SIZE /PAGE_ALIGN. 
      split; [|lia]. replace (Z.of_nat 128) with (8 * 16)%Z by lia. 
      rewrite Z.quot_mul; lia. }
    iIntros (lp) "(Hp & Hf & %Halp)". rewrite !array_cons.
    iDestruct "Hf" as "(Hf1 & Hf2 & Hinf & Hheap & _)". 
    rewrite <-2Z.add_assoc. wp_pures.
    wp_apply (IList.push_front_hoare with "[Hil1 Hf1 Hf2]"); 
    [iFrame; by rewrite array_nil|]. iIntros "Hil1". wp_pures. 
    wp_apply (PAlloc.page_alloc_hoare with "[Hp]"); [done|].
    (* in right branch contradiction res = 0 ∧ res > 0 *)
    iIntros (v) "[H | (-> & %Hr_0 & (%a&%b&%c&%d&?& %Hr_not_0 &?))]"; [|lia].
    iDestruct "H" as "(%l & -> & Hfbs & Hun & Hvl & Hp)". wp_pures. 
    wp_store. wp_store. iApply "Hphi". iLeft. iExists l. 
    iSplitR; [done|]. iSplitL "Hun"; [done|].
    iPoseProof (my_auth_my_frac_alloc with "Hauth") as "Hauth".
    iMod "Hauth" as "(Hauth & Hfrac)".
    iPoseProof (PAlloc.get_usefull_pure_facts with "Hp Hvl") 
    as "((%ld & %i & %Hld & %Hl & %Hi) & %Hlp' & %Hr0)".
    assert (down_align l PAGE_ALIGN = lp) as Hlp.
    { apply (down_align_location l lp i); [lia|done|done|done|lia]. }
    iSplitL "Hfrac Hvl".
    { iFrame. by rewrite Hlp. } 
    destruct (decide (lp ∈ (Lq ++ Lf))). 
    { iPoseProof (IList.pred_unique_cycle with "[Hil1 Hil2]") as "%H'"; 
      [apply e| |iFrame|done]. by rewrite list_elem_of_singleton.  }
    rewrite Hlp. simpl in Hdom'.
    iExists [lp], (Lq ++ Lf), res, (L' ⊎ (2 *: {[+ lp +]})). 
    iPoseProof ((my_auth_my_frac_alloc _ _ lp) with "Hauth") as "Hauth".
    iMod "Hauth" as "(Hauth & Hfrac)".
    iFrame. iSplitR; [done|]. iSplitR; [done|].
    assert (({[+ lp; lp +]} : gmultiset loc) = 2 *: {[+ lp +]}) as Hmlp
    by multiset_solver.
    iSplitR. 
    { iPureIntro. apply set_eq. intros. rewrite -Hmlp. set_solver. }
    iSplitL "Hauth"; [by rewrite -Hmlp gmultiset_disj_union_assoc|]. 
    rewrite -Hr2. iSplitR "Hp2".
    { iExists (res - 1). (*TODO(Ben): add fraction?*) iFrame "Hp". 
      iSplitR; [|done]. iPureIntro. assert (lp ∉ L') by set_solver.
      assert (multiplicity lp L' = 0) as HmL'; 
      [by apply not_elem_of_multiplicity|].
      rewrite multiplicity_disj_union HmL' /= multiplicity_scalar_mul 
      multiplicity_singleton_eq. lia. }
    iApply big_sepL_mono; [|done]. iIntros (k y Hl') "(%fbs & %Hmult & Ha & 
    Hp & Hf & Hh)". simplify_eq. iFrame. iPureIntro.
    apply list_elem_of_lookup_2 in Hl'. 
    rewrite multiplicity_disj_union.
    rewrite multiplicity_scalar_mul multiplicity_singleton_ne; 
    [lia|set_solver].
  Qed.
 
  Local Definition unsafe_unwrap: val := λ: "x",
    match: "x" with 
      SOME("v") => "v" 
    | NONE => diverge #()
    end.

  Local Lemma unsafe_unwrap_hoare (v x : val) :
    {{{ ⌜x = SOMEV v ∨ x = NONEV⌝ }}}
      unsafe_unwrap x
    {{{ RET v; ⌜x = NONEV → False⌝ }}}.
  Proof.
    iIntros (Φ) "%lx HY".
    destruct lx; rewrite H; wp_lam; wp_pure; wp_pure.
    * wp_pures. by iApply "HY".
    * wp_pure. iLöb as "IH". wp_lam. by wp_apply "IH".
  Qed.

  Local Definition test_program_heap : val := λ: "_", 
    let: "al" := heap_new_alloc #() in
    let: "l1" := unsafe_unwrap (heap_alloc "al" #(BLOCK_SIZE - 1)%nat) in
    let: "l2" := unsafe_unwrap (heap_alloc "al" #(BLOCK_SIZE - 3)%nat) in
    "l1" <- #1 ;;
    ("l1" + #1) <- #2 ;;
    "l2" <- #3 ;; 
    ("l2" + #1) <- #4 ;;
    heap_free "l1" ;;
    heap_free "l2". 
    (*TODO(Ben): heap_dealloc "al".*)
  
  (* also breaking abstration with ghost stat here *)
  Local Lemma test_progam_heap_hoare :
    {{{ emp }}} 
      test_program_heap #() 
    {{{ RET #(); emp }}}.
  Proof. 
    iIntros (φ) "_ Hphi". iUnfold test_program_heap.
    wp_pures. wp_apply (heap_new_alloc_hoare); [done|].
    iIntros (al) "(%γ & Hp)". wp_pures.
    wp_apply (heap_alloc_hoare with "[Hp]"); [done|]. 
    iIntros (v) "[(%l & -> & Hun & Hv & Hp)|(-> & H)]";
    wp_apply unsafe_unwrap_hoare;
    [iPureIntro; by left| 
    |iPureIntro; by right|iIntros; by specialize (H eq_refl)].
    iIntros. wp_pures.
    wp_apply (heap_alloc_hoare with "Hp"). 
    iIntros (v) "[(%l' & -> & Hun' & Hv' & Hp)|(-> & H)]"; 
    wp_apply unsafe_unwrap_hoare;
    [iPureIntro; by left| 
    |iPureIntro; by right|iIntros; by specialize (H0 eq_refl)].
    iIntros. wp_pures.
    iDestruct "Hun" as "((%v0 & Hl0) & (%v1 & Hl1) & Hun)".
    iDestruct "Hun'" as "((%v2 & Hl2) & (%v3 & Hl3) & Hun')".
    rewrite 2!Z.add_0_r.
    wp_store. wp_store. wp_store. wp_store. 
    wp_apply (heap_free_hoare with "[Hp Hl0 Hl1 Hun Hv]").
    { iFrame. rewrite Z.add_0_r. auto. }
    iIntros "Hp". wp_pures.
    wp_apply (heap_free_hoare with "[Hp Hl2 Hl3 Hun' Hv']").
    { iFrame. rewrite Z.add_0_r. auto. }
    iIntros "Hp". by iApply "Hphi".
    (* TODO(Ben): dealloc *) 
    Unshelve. exact #(). exact #().
  Qed.

End HAlloc. End HAlloc.
