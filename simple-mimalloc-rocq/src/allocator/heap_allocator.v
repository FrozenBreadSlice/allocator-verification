From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.
From AllSrc.iris_heap_lang_asm.lib Require Import assert.
From AllSrc.allocator Require Import page_allocator.
From AllSrc.intrusive_list Require Import ilist.
From AllSrc.allocator Require Import utils.
From AllSrc.allocator Require Export heap_ghost_state.
From AllSrc.iris_heap_lang_asm.lib Require Import unwrap.

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
  Definition f_callback : nat := 4.
  
  (* other constans *)
  Definition num_qs : nat := 2. (*includes full list*)
  Definition num_f : nat := num_qs + 1. (*includes full list*)
  Definition queue_size : nat := 2.

  (* TODO(Ben): more queues with block sizes later *)
  Definition BLOCK_SIZE : nat := 16. 
  Definition PAGE_ALIGN : nat := 128.  

  (* 
    function definitions
  *)

  Definition heap_new_alloc : val := λ: "_", 
    let: "al" := AllocN (#num_qs * #queue_size + #1) #1 NONE in 
    IList.new ("al" + #f_queue) ;;
    IList.new ("al" + #f_full) ;;
    "al".

  Definition heap_register_callback : val := λ: "al" "f", 
    ("al" + #f_callback) <- SOME "f". 

  Definition heap_deregister_callback : val := λ: "al", 
    ("al" + #f_callback) <- NONE. 

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
        PAlloc.page_free "lmd" "l"
      end
      else PAlloc.page_free "lmd" "l".

  Definition queue_alloc : val := rec: "rec" "bsq" "full" := 
    if: IList.is_empty "bsq" then #NULL 
    else 
      let: "lp" := IList.prev "bsq" in
      let: "l" := PAlloc.page_alloc "lp" in
      if: "l" = #NULL 
      then 
        let: "lp" := IList.pop_back "bsq" in 
        IList.push_front "full" "lp" ;;
        ("lp" + #f_in_full) <- #true ;;
        "rec" "bsq" "full"
      else "l".
      
  Definition alloc_new_page : val := λ: "bsq" "al",
    let: "res" := #(Z.to_nat (PAGE_ALIGN `quot` BLOCK_SIZE - 1)) in
    let: "lp" := PAlloc.page_new_alloc "res" #BLOCK_SIZE #PAGE_ALIGN in 
    IList.push_front "bsq" "lp" ;;
    let: "l" := PAlloc.page_alloc "lp" in 
    ("lp" + #f_in_full) <- #false ;;
    ("lp" + #f_heap) <- "al" ;;
    "l".

  Definition heap_alloc : val := λ: "al" "n", 
    if: #BLOCK_SIZE < "n" then #NULL 
    else
      (* mimalloc has a cache lookup before this *)
      match: !("al" + #f_callback) with 
        NONE     => #() 
      | SOME "f" => "f" #()
      end ;;
      let: "bsq" := ("al" + #f_queue) in 
      let: "full" := ("al" + #f_full) in 
      let: "l" := queue_alloc "bsq" "full" in 
      if: "l" = #NULL 
      then alloc_new_page "bsq" "al"
      else "l".

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
          my_frac γ lp ∗ 
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

  Definition m_only_free : bool := false. 
  Definition m_also_alloc : bool := true.

  Definition is_allocator γ al (only_free : bool)  : iProp Σ := 
    is_heap γ al ∗ 
    (if only_free then True%I
    else 
      ((al + f_callback) ↦ NONEV 
        ∨ 
      (∃ f, (al + f_callback) ↦ SOMEV f ∗  
       □ (is_heap γ al -∗ WP (f #()) {{ v, ⌜v = #()⌝ ∗ is_heap γ al }}))
      ))%I. 
            
  Definition is_valid_loc γ (l : loc) : iProp Σ := 
    let lmd := down_align l PAGE_ALIGN in 
    my_frac γ lmd ∗   
    PAlloc.is_valid_loc lmd l. 

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
    is_valid_loc γ l -∗ 
    is_heap_internal γ al Lq Lf ∗ is_valid_loc γ l ∗ 
    ⌜down_align l PAGE_ALIGN ∈ (Lq ++ Lf)⌝.
  Proof.
    iIntros "Hh Hvl".
    iDestruct "Hh" as "(%res & %L & %Hc1 & %Hc2 & %Hdom & 
    Hauth & Hil1 & Hil2 & Hp1 & Hp2)".
    rewrite /is_valid_loc.
    iDestruct "Hvl" as "(Hfrac & Hvl)".
    remember (down_align l PAGE_ALIGN) as lmd.
    iAssert (⌜lmd ∈ L⌝ -∗ ⌜lmd ∈ (Lq ++ Lf)⌝)%I as "H".
    { iPureIntro. intros. set_solver. }
    iDestruct (my_auth_my_frac_agree with "Hauth Hfrac") as "%H'".
    iFrame. iSplit; [auto|]. by iApply "H".
  Qed.
     
  Lemma heap_new_alloc_hoare :
    [[{ emp }]]
      heap_new_alloc #() 
    [[{ al, RET #al; ∃ γ, is_allocator γ al false }]].
  Proof. 
    iIntros (φ) "_ Hphi". iUnfold heap_new_alloc. wp_pures.
    wp_apply twp_allocN; [done|done|done|]. iIntros (l) "(_ & _ & [Hl _])".
    wp_pures. unfold num_qs, queue_size. 
    replace (Z.to_nat (2%nat * 2%nat + 1)) with (2 + 2 + 1) by lia.
    rewrite !replicate_add !array_app !length_replicate array_singleton.
    iDestruct "Hl" as "([H1 H2] & H3)". simpl.
    wp_apply (IList.new_hoare with "[H1]"); [by rewrite Z.add_0_r|].
    iIntros "Hq". wp_pures. wp_apply (IList.new_hoare with "H2"). 
    iIntros "Hf". wp_pures. iApply "Hphi". 
    iDestruct (my_auth_unit) as "H". iMod "H" as (γ) "Hauth". 
    iExists γ. iSplitR "H3"; [|by iLeft].
    iExists [], [], _, (∅ : gmultiset loc). iFrame. simpl. iSplitR.
    { rewrite /PAlloc.MDSIZE /BLOCK_SIZE. iPureIntro. lia. }
    iSplitR; [done|]. iSplitR. 
    { iPureIntro. set_solver. } auto.
  Qed.
 
  Lemma heap_register_callback_hoare γ al f : 
    [[{ is_allocator γ al false ∗ 
      {{{ is_heap γ al }}} #f #() {{{ RET #(); is_heap γ al }}} 
    }]]
      heap_register_callback #al #f
    [[{ RET #(); is_allocator γ al false }]].
  Proof. 
    iIntros (φ) "[[Hh Hf] H] Hphi". iUnfold heap_register_callback.
    iDestruct "Hf" as "[Hf | (%f' & Hf & Hwp)]";
    wp_store; iApply "Hphi"; iFrame; iRight;
    iExists #f; iFrame; iModIntro; 
    iDestruct "H" as "#H"; iModIntro;
    iIntros "Hh"; iApply ("H" with "Hh"); iNext; auto.
  Qed.
 
  Lemma heap_deregister_callback_hoare γ al : 
    [[{ is_allocator γ al false }]]
      heap_deregister_callback #al
    [[{ RET #(); is_allocator γ al false }]].
  Proof. 
    iIntros (φ) "[Hh Hf] Hphi". iUnfold heap_deregister_callback.
    iDestruct "Hf" as "[Hf | (%f' & Hf & Hwp)]";
    wp_store; iApply "Hphi"; by iFrame.  
  Qed.

  (* TODO(Ben): shorter proof should be possible, 
    can make total correctness as well.. *)
  Lemma heap_free_hoare γ fo l al : 
    [[{ 
      is_allocator γ al fo ∗ 
      ([∗ list] i ∈ seq 0 BLOCK_SIZE, ∃ v, (l + i)%Z ↦ v) ∗ 
      is_valid_loc γ l
    }]]
      heap_free #l 
    [[{ RET #(); is_allocator γ al fo }]].
  Proof. 
    iIntros (φ) "([(%Lq & %Lf & Hh) Hf] & Hun & Hvl) Hphi".
    iDestruct (in_internal_lists with "Hh Hvl") as 
    "(Hh & (Hfrac & Hvl) & %HinL)". 
    iDestruct "Hh" as "(%res & %L & %Hr1 & %Hr2 & %Hdom
    & Hauth & Hil1 & Hil2 & Hp1 & Hp2)". iUnfold heap_free. wp_pures.
    remember (down_align l PAGE_ALIGN) as lmd.
    assert (l `quot` PAGE_ALIGN * PAGE_ALIGN = lmd)%Z by done. rewrite H. 
    apply elem_of_app in HinL. destruct HinL.
    - iDestruct (IList.pred_unique with "Hil1") as "(Hil1 & %Hd)".
      apply NoDup_cons in Hd as [Hd1 Hd2].
      destruct (list_elem_of_split _ _ H0) as (L1 & L2 & HLq). rewrite HLq. 
      iDestruct (big_sepL_get_middle _ L1 L2 lmd with "Hp1") 
      as "((%fbs & %Hm & Hfracp & %Ha & Hp & Hif & Hh) & Hp1)". wp_load. 
      wp_pures. iApply twp_fupd.
      wp_apply (PAlloc.page_free_hoare with "[Hp Hun Hvl]"); [iFrame|].
      iIntros "Hp". iApply "Hphi". iFrame "Hf".
      iExists Lq, Lf, res.
      destruct (decide (lmd ∈ Lf)). (* this gets us lmd ∉ Lf, needed later *)
      { iDestruct (IList.pred_unique_cycle with "[Hil1 Hil2]") as "%H'"; 
        [apply e|apply H0|rewrite HLq; iFrame|done]. }
      iExists (L ∖ {[+ lmd +]}). rewrite -HLq. iFrame.
      iSplitR; [done|]. iSplitR; [done|]. destruct (decide (res < S (fbs))).
      { by iDestruct (PAlloc.page_res_geq_fbs with "Hp") as "Hcon". }
      assert (multiplicity lmd L > 1)by lia. 
      iSplitR. { iPureIntro. rewrite -Hdom. multiset_solver. }
      iSplitL "Hauth Hfrac". 
      { by iDestruct (my_auth_my_frac_dealloc with "Hauth Hfrac") as "H". }
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
  - iDestruct (IList.pred_unique with "Hil2") as "(Hil2 & %Hd)".
    apply NoDup_cons in Hd as [Hd1 Hd2].
    destruct (decide (lmd ∈ Lq)). (* this gets us lmd ∉ Lq, needed later *)
    { iDestruct (IList.pred_unique_cycle with "[Hil1 Hil2]") as "%H'"; 
      [apply H0|apply e|iFrame|done]. }
    destruct (list_elem_of_split _ _ H0) as (L1 & L2 & HLf). rewrite HLf. 
    iDestruct ((big_sepL_get_middle _ L1 L2 lmd) with "Hp2") 
    as "((%fbs & %Hm & Hfracp & %Ha & Hp & Hif & Hh) & Hp2)". 
    wp_load. wp_pures. wp_load. wp_pures. 
    wp_apply (IList.remove_hoare with "[Hil2]"); [by rewrite Z.add_0_r|].
    iIntros "(Hlmdl & Hil2)". wp_pures.
    wp_apply (IList.push_front_hoare with "[Hlmdl Hil1]"); [iFrame|].
    iIntros "Hil1". rewrite !Z.add_0_r. wp_store. iApply twp_fupd.
    wp_apply (PAlloc.page_free_hoare with "[Hp Hun Hvl]"); [iFrame|].
    iIntros "Hp". iApply "Hphi". iFrame "Hf".
    iExists (lmd::Lq), (L1 ++ L2), res.
    destruct (decide (res < S (fbs))).
    { by iDestruct (PAlloc.page_res_geq_fbs with "Hp") as "Hcon". }
    assert (multiplicity lmd L > 1) by lia. 
    iExists (L ∖ {[+ lmd +]}). rewrite Z.add_0_r. iFrame. 
    iSplitR; [done|]. iSplitR; [done|]. 
    iSplitR. 
    (* TODO(Ben): help multiset_solver here or remove for the easy proof*)
    { assert (dom L = list_to_set ((lmd :: Lq) ++ L1 ++ L2)) 
      by multiset_solver. rewrite -H2. iPureIntro. multiset_solver. }
    iSplitL "Hauth Hfrac".
    { by iDestruct (my_auth_my_frac_dealloc with "Hauth Hfrac") as "H". }
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
    [[{ is_heap_internal γ al Lq Lf }]]
      queue_alloc #(al + f_queue) #(al + f_full) 
    [[{ l, RET #l; 
      (∃ Lq' L Lf', ⌜l ≠ NULL⌝ ∗ 
        ⌜Lq = Lq' ++ L⌝ ∗ ⌜Lf' = L ++ Lf⌝ ∗
        ([∗ list] i ∈ seq 0 BLOCK_SIZE, ∃ v, (l + i)%Z ↦ v) ∗ 
        is_valid_loc γ l ∗
        is_heap_internal γ al Lq' Lf') 
      ∨
      (⌜l = NULL⌝ ∗ is_heap_internal γ al [] (Lq ++ Lf))
    }]].
  Proof. 
    revert Lf. induction Lq using rev_ind; iIntros (Lf φ) "(%res & %L & %Hr 
    & %Hr2 & %Hdom & Hauth & Hil1 & Hil2 & Hp1 & Hp2) Hphi"; 
    iUnfold queue_alloc; wp_pures;
    wp_apply (IList.is_empty_hoare with "Hil1"); iIntros "Hil1"; wp_pures. 
    { iApply "Hphi". iRight. iFrame. auto. }
    case_bool_decide.
    { specialize (app_nil_r_inv _ _ H) as H'. inversion H'. }
    wp_pures. wp_apply (IList.prev_hoare with "Hil1").
    iIntros "Hil1". 
    assert (((reverse (Lq ++ [x]) ++ [(al + f_queue)%Z]) !!! 0%nat) = x) 
    as Hind. 
    { rewrite reverse_snoc. rewrite lookup_total_app_l; simpl; [done|lia]. }
    rewrite Hind. wp_pures. 
    iDestruct (big_sepL_snoc with "Hp1") as "(Hp1 & Hpx)".
    iDestruct "Hpx" as "(%fbs & %Hml & Hfracx & %Hax & Hp & Hinf & Hal)".
    destruct (decide (res < fbs)).
    { by iDestruct (PAlloc.page_res_geq_fbs with "Hp") as "Hcon". }
    iDestruct (IList.pred_unique with "Hil1") as "(Hil1 & %Hnd)".  
    apply NoDup_cons_1_2 in Hnd. apply NoDup_snoc in Hnd as [Hnd1 Hnd2].
    destruct (decide (x ∈ Lf)).
    { iDestruct (IList.pred_unique_cycle with "[Hil1 Hil2]") as "H"; 
      [apply e| | iFrame|done]. apply elem_of_app. right. 
      by apply list_elem_of_singleton. }
    wp_apply (PAlloc.page_alloc_hoare with "Hp").
    iIntros (l) "[H | H]".
    - iDestruct "H" as "(%Hlnp & %Hfbs & Hun & Hvl & Hp)". 
      iDestruct (PAlloc.get_usefull_pure_facts with "Hp Hvl") 
      as "((%ld & %i & %Hld & %Hl & %Hi) & %Hlp' & %Hr0)".
      wp_pures. case_bool_decide; [simplify_eq|]. wp_pures.
      iApply "Hphi".  assert (down_align l PAGE_ALIGN = x) as Hx.
      { apply (down_align_location l x i); [lia|done|done|lia|lia]. }
      iLeft. iExists (Lq ++ [x]), [], Lf. iSplitR; [done|]. 
      iSplitR; [by rewrite app_nil_r|]. iSplitR; [by rewrite app_nil_l|].
      iSplitL "Hun"; [done|].
      iDestruct (my_auth_my_frac_alloc with "Hauth") as "Hauth".
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
          rewrite multiplicity_disj_union multiplicity_singleton_eq. lia. } 
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
      (* TODO(Ben): how to give everything except some hypothesis? *)
      iApply (IHLq with "[Hp1 Hp2 Hil1 Hil2 Hauth Hp Hinf Hal Hfracx]"). 
      { iFrame. iFrame. iSplitR; [iPureIntro; lia|]. 
        rewrite -app_assoc /= in Hdom. auto. }
      iIntros (l) "[H | H]". iApply "Hphi". 
      { iDestruct "H" as "(%Lq' & %Lf'' & %Lf' & %Hlnp & -> & -> &
        Hlbs & Hivl & Hal)". iLeft. iExists Lq', (Lf'' ++ [x]), 
        (Lf'' ++ [x] ++ Lf). iFrame. iSplitR; [done|]. 
        iSplitR; [by rewrite app_assoc|]. by rewrite app_assoc. }
      iApply "Hphi". iRight. by rewrite -app_assoc /=.
  Qed.

  Lemma alloc_new_page_hoare al lq L res : 
    res = Z.to_nat (PAGE_ALIGN `quot` BLOCK_SIZE - 1) → 
    [[{ IList.is_ilist lq L }]]
      alloc_new_page #lq #al 
    [[{ l, RET #l; ∃ lp, 
        IList.is_ilist lq (lp :: L) ∗ 
        PAlloc.is_page lp BLOCK_SIZE res (res - 1) ∗ 
        ⌜(PAGE_ALIGN | lp)%Z⌝ ∗
        (lp + f_in_full)%Z ↦ #false ∗
        (lp + f_heap)%Z ↦ #al ∗
        ⌜l ≠ NULL⌝ ∗
        ([∗ list] i ∈ seq 0 BLOCK_SIZE, ∃ v, (l + i)%Z ↦ v) ∗ 
        PAlloc.is_valid_loc lp l
    }]].
  Proof. 
    iIntros (Hr φ) "Hlq Hphi". iUnfold alloc_new_page. wp_pures.
    wp_apply (PAlloc.page_new_alloc_hoare _ BLOCK_SIZE PAGE_ALIGN).
    { iPureIntro. rewrite /BLOCK_SIZE /PAGE_ALIGN. 
      split; [|lia]. replace (Z.of_nat 128) with (8 * 16)%Z by lia. 
      rewrite Z.quot_mul; lia. }
    iIntros (lp) "(Hp & Hf & %Halp)". rewrite !array_cons.
    iDestruct "Hf" as "(Hf1 & Hf2 & Hinf & Hheap & _)". 
    rewrite <-2Z.add_assoc. wp_pures.
    wp_apply (IList.push_front_hoare with "[Hlq Hf1 Hf2]"); 
    [iFrame; by rewrite array_nil|]. iIntros "Hil1". wp_pures. 
    wp_apply (PAlloc.page_alloc_hoare with "[Hp]"); [done|].
    (* in right branch contradiction res = 0 ∧ res > 0 *)
    iIntros (l) "[H | (-> & %Hr_0 & (%a&%b&%c&%d&?& %Hr_not_0 &?))]"; [|lia].
    iDestruct "H" as "(%Hlnp & Hfbs & Hun & Hvl & Hp)". wp_pures. 
    wp_store. wp_store. iApply "Hphi". rewrite Hr. by iFrame.
  Qed.

  Lemma heap_alloc_hoare γ al n : 
    {{{ is_allocator γ al false }}} 
      heap_alloc #al #n
    {{{ l, RET #l; 
       (⌜l ≠ NULL⌝ ∗ ⌜n ≤ BLOCK_SIZE⌝ ∗
          ([∗ list] i ∈ seq 0 BLOCK_SIZE, ∃ v, (l + i)%Z ↦ v) ∗ 
          is_valid_loc γ l ∗ is_allocator γ al false) 
      ∨
      ⌜l = NULL⌝ ∗ ⌜BLOCK_SIZE < n⌝ ∗ is_allocator γ al false
    }}}.
  Proof. 
    iIntros (φ) "[Hh Hf] Hphi". iUnfold heap_alloc. 
    iDestruct "Hh" as (Lq Lf res L) "(%Hr & %Hr' & %Hdom & 
    Hauth & Hil1 & Hil2 & Hp1 & Hp2)".
    wp_pures. case_bool_decide.
    { wp_pures. iApply "Hphi". iRight. iSplitR; [done|]. 
      iSplitR; [iPureIntro; lia|]. iFrame. auto. }
    wp_pures. iDestruct "Hf" as "[Hf | (%f & Hf & #Hwp)]"; 
    wp_load; wp_pures. 
    (* callback none case *)
    { wp_apply twp_wp.
      wp_apply (queue_alloc_hoare with "[$Hauth $Hil1 $Hil2 $Hp1 $Hp2]"); 
      [auto|]. iIntros (v) "[H | H]".
      { iDestruct "H" as "(%Lq1 & %Ld & %Lf1 & %Hlnp & -> & -> & Hl &Hlv & Hh)".
        wp_pures. case_bool_decide; [simplify_eq|]. wp_pures.
        iApply "Hphi". iLeft. iFrame. iSplitR; [done|]. 
        iPureIntro. lia. }
      iDestruct "H" as "(-> & %res2 & %L2 & %Hr2 & %Hr'2 & %Hdom2 & 
      Hauth & Hil1 & Hil2 & Hp1 & Hp2)". wp_pures. iApply twp_fupd. 
      wp_apply (alloc_new_page_hoare with "Hil1"); [apply Hr'|..].
      iIntros (l) "(%lp & Hil1 & Hlp & %Hal & Hinf & Hh & %Hlnp & Hun & Hvl)". 
      iApply "Hphi". iLeft.  
      iSplitR; [done|]. iSplitR; [iPureIntro; lia|]. iSplitL "Hun"; [done|].
      iDestruct (my_auth_my_frac_alloc with "Hauth") as "Hauth".
      iMod "Hauth" as "(Hauth & Hfrac)".
      iDestruct (PAlloc.get_usefull_pure_facts with "Hlp Hvl") 
      as "((%ld & %i & %Hld & %Hl & %Hi) & %Hlp' & %Hr0)".
      assert (down_align l PAGE_ALIGN = lp) as Hlp.
      { apply (down_align_location l lp i); [lia|done|done|lia|lia]. }
      iSplitL "Hfrac Hvl"; [iFrame; by rewrite Hlp|].
      iSplitR "Hf"; [|by iLeft].
      destruct (decide (lp ∈ (Lq ++ Lf))). 
      { iDestruct (IList.pred_unique_cycle with "[Hil1 Hil2]") as "%H'"; 
        [apply e| |iFrame|done]. by rewrite list_elem_of_singleton.  }
      rewrite Hlp. simpl in Hdom2. 
      iExists [lp], (Lq ++ Lf), res, (L2 ⊎ (2 *: {[+ lp +]})). 
      iDestruct ((my_auth_my_frac_alloc _ _ lp) with "Hauth") as "Hauth".
      iMod "Hauth" as "(Hauth & Hfrac)".
      iFrame. iSplitR; [done|]. iSplitR; [done|].
      assert (({[+ lp; lp +]} : gmultiset loc) = 2 *: {[+ lp +]}) as Hmlp
      by multiset_solver. iSplitR. 
      { iPureIntro. apply set_eq. intros. rewrite -Hmlp. set_solver. }
      iSplitL "Hauth"; [by rewrite -Hmlp gmultiset_disj_union_assoc|].
      iSplitR "Hp2".
      { iPureIntro. split; [|done]. assert (lp ∉ L2) by set_solver.
        assert (multiplicity lp L2 = 0) as HmL'; 
        [by apply not_elem_of_multiplicity|].
        rewrite multiplicity_disj_union HmL' /= multiplicity_scalar_mul 
        multiplicity_singleton_eq. lia. }
      iApply big_sepL_mono; [|done]. 
      iIntros (k y Hl') "(%fbs & %Hmult & Ha & Hp & Hf & Hh)". 
      simplify_eq. iFrame. iPureIntro.
      apply list_elem_of_lookup_2 in Hl'. 
      rewrite multiplicity_disj_union.
      rewrite multiplicity_scalar_mul multiplicity_singleton_ne; 
      [lia|set_solver]. }
    (* callback some case *) 
    iAssert ((is_heap γ al)%I) with "[Hauth Hil1 Hil2 Hp1 Hp2]" as "Hh".
    { iFrame. auto. }
    iPoseProof "Hwp" as "Hwp2".
    iSpecialize ("Hwp2" with "Hh"). 
    wp_apply (wp_wand with "Hwp2") as (v) "[-> Hh]". wp_pures.
    clear Hdom Lq Lf Hr' res L Hr.
    iDestruct "Hh" as (Lq Lf res L) "(%Hr & %Hr' & %Hdom & 
    Hauth & Hil1 & Hil2 & Hp1 & Hp2)".
    (* basically all repetition *)
    wp_apply twp_wp.
    wp_apply (queue_alloc_hoare with "[$Hauth $Hil1 $Hil2 $Hp1 $Hp2]"); 
    [auto|]. iIntros (l) "[H | H]".
    { iDestruct "H" as "(%Lq1 & %Ld & %Lf1 & %Hlnp & -> & -> & Hl &Hlv & Hh)".
      wp_pures. case_bool_decide; [simplify_eq|]. wp_pures.
      iApply "Hphi". iLeft. iFrame. iSplitR; [done|]. 
      iSplitR; [iPureIntro; lia|]. iRight. auto. }
    iDestruct "H" as "(-> & %res2 & %L2 & %Hr2 & %Hr2' & %Hdom2 & 
    Hauth & Hil1 & Hil2 & Hp1 & Hp2)". wp_pures. iApply twp_fupd. 
    wp_apply (alloc_new_page_hoare with "Hil1"); [apply Hr'|..].
    iIntros (l) "(%lp & Hil1 & Hlp & %Hal & Hinf & Hh & %Hlnp & Hun & Hvl)". 
    iApply "Hphi". iLeft.  
    iSplitR; [done|]. iSplitR; [iPureIntro; lia|]. iSplitL "Hun"; [done|].
    iDestruct (my_auth_my_frac_alloc with "Hauth") as "Hauth".
    iMod "Hauth" as "(Hauth & Hfrac)".
    iDestruct (PAlloc.get_usefull_pure_facts with "Hlp Hvl") 
    as "((%ld & %i & %Hld & %Hl & %Hi) & %Hlp' & %Hr0)".
    assert (down_align l PAGE_ALIGN = lp) as Hlp.
    { apply (down_align_location l lp i); [lia|done|done|lia|lia]. }
    iSplitL "Hfrac Hvl"; [iFrame; by rewrite Hlp|].
    iSplitR "Hf"; [|iRight; auto].
    destruct (decide (lp ∈ (Lq ++ Lf))). 
    { iDestruct (IList.pred_unique_cycle with "[Hil1 Hil2]") as "%H'"; 
      [apply e| |iFrame|done]. by rewrite list_elem_of_singleton.  }
    rewrite Hlp. simpl in Hdom2. 
    iExists [lp], (Lq ++ Lf), res, (L2 ⊎ (2 *: {[+ lp +]})). 
    iDestruct ((my_auth_my_frac_alloc _ _ lp) with "Hauth") as "Hauth".
    iMod "Hauth" as "(Hauth & Hfrac)".
    iFrame. iSplitR; [done|]. iSplitR; [done|].
    assert (({[+ lp; lp +]} : gmultiset loc) = 2 *: {[+ lp +]}) as Hmlp
    by multiset_solver. iSplitR. 
    { iPureIntro. apply set_eq. intros. rewrite -Hmlp. set_solver. }
    iSplitL "Hauth"; [by rewrite -Hmlp gmultiset_disj_union_assoc|].
    iSplitR "Hp2".
    { iPureIntro. split; [|done]. assert (lp ∉ L2) by set_solver.
      assert (multiplicity lp L2 = 0) as HmL'; 
      [by apply not_elem_of_multiplicity|].
      rewrite multiplicity_disj_union HmL' /= multiplicity_scalar_mul 
      multiplicity_singleton_eq. lia. }
    iApply big_sepL_mono; [|done]. 
    iIntros (k y Hl') "(%fbs & %Hmult & Ha & Hp & Hf & Hh)". 
    simplify_eq. iFrame. iPureIntro.
    apply list_elem_of_lookup_2 in Hl'. 
    rewrite multiplicity_disj_union.
    rewrite multiplicity_scalar_mul multiplicity_singleton_ne; 
    [lia|set_solver].
  Qed.
  
End HAlloc. End HAlloc.
