From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.
From AllSrc.allocator Require Import page_allocator.
From AllSrc.intrusive_list Require Import ilist.
From AllSrc.allocator Require Import utils.

(* Heap allocator

*)

Module HAlloc. Section HAlloc.
  Context `{!heapGS_gen hlc Σ}.
 
  Implicit Types al l lq lf : loc.
  Implicit Types res bs fbs i n : nat.
  Implicit Types Lq Lf : list loc.

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
        NONE => #() (*should not happen*)
      | SOME "lp" => 
        IList.push_front ("heap" + #f_queue) "lp" ;;
        ("lp" + #f_in_full) <- #false ;;
        PAlloc.page_free "lmd" "l"
      end
    else  
      PAlloc.page_free "lmd" "l".

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
            PAlloc.page_new_alloc "al" "res" #BLOCK_SIZE #PAGE_ALIGN in 
          IList.push_front "bsq" "lp" ;;
          PAlloc.page_alloc "lp"
      | SOME "l" => SOME "l"
      end.

  (* 
    Representation
  *)

  Definition is_heap_internal al Lq Lf : iProp Σ :=
    ∃ res, 
      ⌜PAlloc.MDSIZE < BLOCK_SIZE⌝ ∗
      ⌜res = Z.to_nat (PAGE_ALIGN `quot` BLOCK_SIZE - 1)%Z⌝ ∗
      ⌜(res * BLOCK_SIZE + PAlloc.MDSIZE < PAGE_ALIGN)%Z⌝ ∗
      IList.is_ilist (al + f_queue)%Z Lq ∗ 
      IList.is_ilist (al + f_full)%Z Lf ∗
      ([∗ list] lp ∈ Lq,  
          ∃ fbs,
          ⌜(PAGE_ALIGN | lp)%Z⌝ ∗
          PAlloc.is_page lp BLOCK_SIZE res fbs ∗ 
          (lp + f_in_full)%Z ↦ #false ∗
          (lp + f_heap)%Z ↦{#page_frac res fbs} #al) ∗
      ([∗ list] lp ∈ Lf, 
          ∃ fbs,
          ⌜(PAGE_ALIGN | lp)%Z⌝ ∗
          PAlloc.is_page lp BLOCK_SIZE res fbs ∗ 
          (lp + f_in_full)%Z ↦ #true ∗
          (lp + f_heap)%Z ↦{#page_frac res fbs} #al).

  Definition is_heap al : iProp Σ := 
    ∃ Lq Lf, is_heap_internal al Lq Lf.

  Definition is_valid_loc l al : iProp Σ := 
    ∃ bs res,
    let lmd := down_align l PAGE_ALIGN in 
    (lmd + PAlloc.f_bs)%Z ↦{#free_frac res} #bs ∗
    (lmd + PAlloc.f_res)%Z ↦{#free_frac res} #res ∗
    PAlloc.is_valid_loc_internal l lmd bs res ∗ 
    (lmd + f_heap)%Z ↦{#free_frac res} #al.

  (*
    Hoare triples and proofs
  *)
  Lemma in_internal_lists al l Lq Lf : 
    is_heap_internal al Lq Lf ∗ is_valid_loc l al 
    ⊢ (*is_heap_internal al Lq Lf ∗ is_valid_loc l al 
    ∗*) ⌜down_align l PAGE_ALIGN ∈ (Lq ++ Lf)⌝.
  Proof. Admitted.
    (*
    iIntros "(Hh & Hvl)".
    iDestruct "Hh" as "(%res & %Hr1 & %Hr2 & %Hr3 & Hil1 & Hil2 & Hp1 & 
    Hp2)".
    iDestruct "Hvl" as "(%bs' & %res' & Hbs' & Hres' & Hvli & Hal)".
    destruct 
  Qed.
*)
 

  Lemma heap_new_alloc_hoare :
    {{{ emp }}}
      heap_new_alloc #() 
    {{{ al, RET #al; is_heap al }}}.
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
    iFrame. simpl. iExists _. iSplitR; [|auto].
    rewrite /PAlloc.MDSIZE /BLOCK_SIZE. iPureIntro. lia.
  Qed.
 
  Lemma big_sepL_get_middle (Q : loc -> iProp Σ) (ls ls' : list loc) l : 
    ([∗ list] y ∈ ls ++ [l] ++ ls', Q y) ⊢ 
    Q l ∗ [∗ list] y ∈ ls ++ ls', Q y.
  Proof.
    iInduction ls as [|l' ls IH]; simpl; iIntros "H"; [done|].
    iDestruct "H" as "(Hq & Hr)". iFrame "Hq". 
    by iApply "IH".
  Qed.

  Lemma heap_free_hoare l al : 
    {{{ 
      is_heap al ∗ ([∗ list] i ∈ seq 0 BLOCK_SIZE, ∃ v, (l + i)%Z ↦ v) ∗ 
      is_valid_loc l al
    }}}
      heap_free #l 
    {{{ RET #(); is_heap al }}}.
  Proof. 
    iIntros (φ) "((%Lq & %Lf & %res & %Hr1 & %Hr2 & %Hr3 & Hil1 & 
    Hil2 & Hp1 & Hp2) & Hun & Hvl) Hphi". iUnfold heap_free. wp_pures.
    unfold is_valid_loc. remember (down_align l PAGE_ALIGN) as lmd.
    assert (l `quot` PAGE_ALIGN * PAGE_ALIGN = lmd)%Z by done. 
    rewrite H. 
    iDestruct "Hvl" as "(%bs' & %res' & Hbs' & Hres' & Hvli & Hal & H)"
    (*how do we establish lmd from in is_valid_loc l al 
    is in one of the lists?
    - we know from things in the list that 
       is_page lp BLOCK_SIZE res fbs and 
       thtat lp is at PAGE_ALIGN boundary 
   
    Definition is_valid_loc l al : iProp Σ := 
      ∃ res,
      let lmd := down_align l PAGE_ALIGN in 
      PAlloc.is_valid_loc l lmd ∗ 
      (lmd + PAlloc.f_res)%Z ↦{#free_frac res} #res ∗
      (lmd + f_heap)%Z ↦{#free_frac res} #al.
 
    Definition is_valid_loc_internal l al bs res : iProp Σ := 
      ∃ ld i, ⌜ld = (al + MDSIZE)%Z⌝ ∗ ⌜l = (ld + (i * bs))%Z⌝ ∗ ⌜i < res⌝.
    
    Definition is_valid_loc l al : iProp Σ := 
      ∃ bs res, 
        (al + f_bs)%Z ↦{#free_frac res} #bs ∗ 
        (al + f_res)%Z ↦{#free_frac res} #res ∗ 
        is_valid_loc_internal l al bs res.

    *)

    (* old 
    About elem_of_app. apply elem_of_app in HinL. destruct HinL.
    - iPoseProof (big_sepL_elem_of_acc _ Lq lmd $ H0 with "Hp1") as "H".
      iDestruct "H" as "((%bf & Hp & Hpif & Hph) & Hrp1)".
      iDestruct "Hp" as "(%res' & %cap & %a & %ld & %b1 & %b2 & %Hal & %Hr & %Hbs 
      & %Ha & %Hcr & %Haal & -> & %Hf & Hcap & #Hres & #Hbs & #Ha & Hfl & Hfl2 
      & Hun)". wp_load. wp_pures.
      wp_apply (PAlloc.page_free_hoare with "[Hcap Hfl Hfl2 Hun Hl]").
      { iFrame. iFrame "Hlvl Ha Hres Hbs". iSplitR; auto. }
      iIntros "Hp". iApply "Hphi". iFrame. iSplitR; [done|].
      iSplitR; [done|]. iApply "Hrp1". iFrame. 
    - iPoseProof (IList.pred_unique with "Hil2") as "(Hil2 & %Hd)".
      apply NoDup_cons in Hd as [Hd1 Hd2].
      destruct (list_elem_of_split _ _ H0) as (L1 & L2 & HLf).
      rewrite HLf. iPoseProof ((big_sepL_get_middle _ L1 L2 lmd) with "Hp2") 
      as "((Hlmdp & Hlmdif & Hlmdh & Hlmdr & Hldmbs) & Hp2)". wp_load. 
      wp_load. wp_pures.
      wp_apply (IList.remove_hoare with "[Hil2]"); [by rewrite Z.add_0_r|].
      iIntros "(Hlmdl & Hil2)". wp_pures.
      wp_apply (IList.push_front_hoare with "[Hlmdl Hil1]"); [iFrame|].
      iIntros "Hil1". rewrite !Z.add_0_r. wp_store. 
      wp_apply (PAlloc.page_free_hoare with "[Hlmdp Hl]"); [by iFrame|].
      iIntros "Hlmdp". iApply "Hphi". iExists (lmd::Lq), (L1 ++ L2). 
      iFrame. iSplitR; [done|]. iSplitR; [done|]. by rewrite Z.add_0_r. 
    *)
  Qed.

  Local Lemma down_align_location l l' i : 
    (PAlloc.MDSIZE < BLOCK_SIZE)%Z ->
    (0 < l')%Z ->
    (PAGE_ALIGN | l')%Z ->
    i < Z.to_nat (PAGE_ALIGN `quot` BLOCK_SIZE - 1) -> 
    l = (l' + PAlloc.MDSIZE + i * BLOCK_SIZE)%Z -> 
    down_align l PAGE_ALIGN = l'.
  Proof. Admitted.
  (*
    intros Hbs Hl Hla Hi Heql.
    apply down_align_in_range; try done. rewrite Heql.  
    assert (PAlloc.MDSIZE + i * bs > 0); [simpl; lia|].
    assert (PAlloc.MDSIZE + i * bs < PAGE_ALIGN); [|lia].
    assert (PAGE_ALIGN `quot` bs * bs ≤ PAGE_ALIGN)%Z; [|nia].
    apply quot_helper; unfold PAGE_ALIGN; lia.
  Qed.
   *)

  Local Lemma queue_alloc_hoare al Lq Lf : 
    {{{ is_heap_internal al Lq Lf }}} 
      queue_alloc #(al + f_queue) #(al + f_full) 
    {{{ vret, RET vret; 
      (∃ Lq' L Lf' l, ⌜vret = SOMEV #l⌝ ∗ 
        ⌜Lq = Lq' ++ L⌝ ∗ ⌜Lf' = L ++ Lf⌝ ∗
        ([∗ list] i ∈ seq 0 BLOCK_SIZE, ∃ v, (l + i)%Z ↦ v) ∗ 
        is_valid_loc l al ∗
        is_heap_internal al Lq' Lf') 
      ∨
      (⌜vret = NONEV⌝ ∗ is_heap_internal al [] (Lq ++ Lf))
    }}}.
  Proof. Admitted.
  (*
  Proof. 
    revert Lf. induction Lq using rev_ind; iIntros (Lf).
    { iIntros (φ) "(%res & %HB & %HR & Hil1 & Hil2 & Hp1 & Hp2) Hphi". 
      iUnfold queue_alloc. wp_pures.
      wp_apply (IList.is_empty_hoare with "Hil1").
      iIntros "Hil1". wp_pures. iApply "Hphi". iRight. by iFrame. }
    iIntros (φ) "(%res & %HB & %HR & Hil1 & Hil2 & Hp1 & Hp2) Hphi".
    iUnfold queue_alloc. wp_pures.
    wp_apply (IList.is_empty_hoare with "Hil1").
    iIntros "Hil1". case_bool_decide.
    { specialize (app_nil_r_inv _ _ H) as H'. inversion H'. }
    wp_pures. wp_apply (IList.prev_hoare with "Hil1").
    iIntros "Hil1". 
    assert (((reverse (Lq ++ [x]) ++ [(al + f_queue)%Z]) !!! 0%nat) = x) as Hind. 
    { rewrite reverse_snoc. Search ((_ ++ _) !!! _).
      rewrite lookup_total_app_l; simpl; [done|lia]. }
    rewrite Hind. wp_pures. Search big_sepL "snoc".
    iPoseProof (big_sepL_snoc with "Hp1") as "(Hp1 & Hpx)".
    iDestruct "Hpx" as "(%bf & Hp & Hpf & Hph & #Hres & #Hbs & #Ha)".
    wp_apply (PAlloc.page_alloc_hoare with "Hp").
    iIntros (v) "[H | H]".
    - iDestruct "H" as "(%l & %bf' & -> & Hlbs & #Hvl & Hp)". 
      wp_pures. iApply "Hphi". 
      iPoseProof (get_page_alignment_facts with "Hp") as 
      "(%a' & %Hx & %Ha' & %Hax & #Ha'' & Hp)".
      iLeft. iExists (Lq ++ [x]), []. 
      iFrame. iSplitR; [done|]. iSplitR; [by rewrite app_nil_r|].
      iSplitR; [by rewrite app_nil_l|].
      iSplitR.
      * iUnfold is_valid_loc. unfold PAlloc.is_valid_loc. 
        iDestruct "Hvl" as "(%ld & %res' & %bs' & %i & #Hres' & #Hbs' & 
        -> & -> & %Hr')". 
        iCombine "Hres'" "Hres" gives %[_ H2]. 
        iCombine "Hbs'" "Hbs" gives %[_ H2'].
        iCombine "Ha''" "Ha" gives %[_ H2'']. simplify_eq.
        remember (x + PAlloc.MDSIZE + i * bs)%Z as l. 
        assert (down_align l PAGE_ALIGN = x).
        { apply (down_align_location _ _ i bs); try done. lia. }
        rewrite H0. iFrame "Hres Hbs". iSplitR; [auto|]. iPureIntro.
        apply elem_of_app. left. apply elem_of_app. right. 
        by apply list_elem_of_singleton. 
      * iSplitR; [done|by iFrame "Hres Hbs Ha"; rewrite big_sepL_nil].
    - iDestruct "H" as "(-> & Hp)". wp_pures.
      wp_apply (IList.pop_back_hoare with "Hil1"). 
      iIntros (v1 v2) "(Hil1 & Hx)". wp_pures.
      wp_apply (IList.push_front_hoare with "[Hil2 Hx]"); [iFrame|].
      iIntros "Hil2". wp_pures. wp_store. fold queue_alloc.
      iApply (IHLq with "[Hp1 Hp2 Hil1 Hil2 Hpf Hph Hp]"). 
      { iFrame. iFrame. by iFrame "Hres Hbs Ha". }
      iNext. iIntros (v) "[H | H]". iApply "Hphi". 
      { iDestruct "H" as "(%Lq' & %L & %Lf' & %l & -> & -> & -> &
        Hlbs & #Hivl & Hal)". iLeft. iExists Lq', (L ++ [x]), 
        (L ++ [x] ++ Lf). iFrame. iSplitR; [done|]. 
        iSplitR; [by rewrite app_assoc|]. iSplitR; [by rewrite app_assoc|].
        by simpl. }
      iApply "Hphi". iRight. by rewrite -app_assoc /=.
  Qed.
  *)
  
  Lemma heap_alloc_hoare al n : 
    {{{ is_heap al }}} 
      heap_alloc #al #n
    {{{ vret, RET vret; 
       (∃ l, ⌜vret = SOMEV #l⌝ ∗ 
          ([∗ list] i ∈ seq 0 BLOCK_SIZE, ∃ v, (l + i)%Z ↦ v) ∗ 
          is_valid_loc l al ∗ is_heap al)
        ∨ 
      ⌜vret = NONEV⌝ ∗ is_heap al 
    }}}.
  Proof. Admitted.
  (*
  Proof. 
    iIntros (φ) "(%Lq & %Lf & %res & %HB & %HR & Hil1 & Hil2 & Hp1 & Hp2) Hphi".  
    iUnfold heap_alloc. wp_pures. case_bool_decide.
    { wp_pures. iApply "Hphi". iRight. by iFrame. }
    wp_pures. 
    wp_apply (queue_alloc_hoare with "[Hil1 Hil2 Hp1 Hp2]"); [by iFrame|].
    iIntros (v) "[H | H]".
    { iDestruct "H" as "(%Lq' & %L & %Lf' & %l & -> & -> & -> & Hl &Hlv & Hh)".
      wp_pures. iApply "Hphi". iLeft. iExists l, Lq', (L ++ Lf). 
      by iFrame. } 
    iDestruct "H" as "(-> & %res' & %HB' & %HR' & Hil1 & Hil2 & Hp1 & Hp2)". 
    wp_pures. wp_apply (PAlloc.page_new_alloc_hoare al _ BLOCK_SIZE PAGE_ALIGN).
    { iPureIntro. rewrite /BLOCK_SIZE /PAGE_ALIGN. 
      split; [|lia]. replace (Z.of_nat 128) with (8 * 16)%Z by lia. 
      rewrite Z.quot_mul; lia. }
    (* is not having Hres and #Hbs a problem?*)
    iIntros (lp) "(Hp & Hfn & Hfp & Hfinf & Hfh & #Hres & #Hbs & #Ha)". 
    wp_pures. wp_apply (IList.push_front_hoare with "[Hil1 Hfn Hfp]").
    { iFrame "Hil1". rewrite Z.add_0_r. iFrame. by iApply array_nil. }
    iIntros "Hil1". wp_pures. 
    wp_apply (PAlloc.page_alloc_hoare with "[Hp]"); [done|].
    iIntros (v) "[H | H]".
    - iDestruct "H" as "(%l & %b & -> & Hl & #Hlv & Hp)". 
      iApply "Hphi". iLeft. iExists l, [lp], (Lq ++ Lf).
      iSplitR; [done|]. iFrame "Hl". 
      iUnfold is_valid_loc.
      iDestruct "Hlv" as "(%ld & %res''' & %bs' & %i & #Hres'' & 
          #Hbs'' & %Hld & %Hl & %Hir)".
      iCombine "Hres''" "Hres" gives %[_ Hreq].
      iCombine "Hbs''" "Hbs" gives %[_ Hbeq]. 
      simplify_eq.
      iPoseProof (get_page_alignment_facts with "Hp") as "(%a & %Hlp & %Ha' 
      & %Halp & #Ha' & Hp)". 
      iCombine "Ha'" "Ha" gives %[_ Hbeq]. simplify_eq.
      iSplitR.
      + remember (lp + PAlloc.MDSIZE + i * BLOCK_SIZE)%Z as l.
        assert (down_align l PAGE_ALIGN = lp).
        { apply (down_align_location _ _ i BLOCK_SIZE); try done. }
        rewrite H0. iSplitR; [|iPureIntro; simpl; apply list_elem_of_here].
        iFrame "Hres Hbs". iExists (lp + PAlloc.MDSIZE)%Z, i. auto.
      + unfold is_heap_internal.
        remember (Z.to_nat (PAGE_ALIGN `quot` BLOCK_SIZE - 1)) as res.
        iExists res. iFrame. iFrame "Hbs Hres Ha". auto.
    - iDestruct "H" as "(-> & Hp)".
      iApply "Hphi". iRight. iSplitR; [done|].
      iUnfold is_heap. iExists [lp], (Lq ++ Lf). simplify_eq. 
      iFrame. iFrame "Hres Hbs Ha". auto.
  Qed.
  *)

  (* TODO(Ben): move to test.v later *)

  (*From AllSrc.iris_heap_lang_asm.lib Require Import unwrap.*)
  From AllSrc.iris_heap_lang_asm.lib Require Import diverge.
  
  Definition unwrap: val := λ: "x",
    match: "x" with SOME("v") => "v" | NONE => diverge #()
    end.

  (* this one does work how about the other..?*)
  Lemma unwrap_hoare (v: val) (x: val):
  {{{ ⌜x = SOMEV(v) ∨ x = NONEV⌝ }}}
    unwrap x
  {{{ RET v; ⌜x = NONEV-> False⌝ }}}.
  Proof.
    iIntros (Φ) "%lx HY".
    destruct lx; rewrite H; wp_lam; wp_pure; wp_pure.
    * wp_pures. by iApply "HY".
    * wp_pure. iLöb as "IH". wp_lam. by wp_apply "IH".
  Qed. 
  Local Definition test_program : val := λ: "_", 
    let: "al" := heap_new_alloc #() in
    let: "l1" := unwrap (heap_alloc "al" #(BLOCK_SIZE - 1)%nat) in
    let: "l2" := unwrap (heap_alloc "al" #(BLOCK_SIZE - 3)%nat) in
    "l1" <- #1 ;;
    ("l1" + #1) <- #2 ;;
    "l2" <- #3 ;; 
    ("l2" + #1) <- #4 ;;
    heap_free "l1" ;;
    heap_free "l2". 
    (*TODO(Ben): heap_dealloc "al".*)
  
  Local Lemma test_progam_hoare :
    {{{ emp }}} 
      test_program #() 
    {{{ RET #(); emp }}}.
  Proof. 
    iIntros (φ) "_ Hphi". iUnfold test_program.
    wp_pures. wp_apply (heap_new_alloc_hoare); [done|].
    iIntros (al) "Hp". wp_pures.
    wp_apply (heap_alloc_hoare with "Hp"). 
    iIntros (v) "[(%l & -> & Hun & Hv & Hp)|(-> & H)]"; 
    wp_apply unwrap_hoare;
    [iPureIntro; by left| 
    |iPureIntro; by right|iIntros; by specialize (H eq_refl)].
    (* why does this unwrap shelve things?*)
    iIntros. wp_pures.
    wp_apply (heap_alloc_hoare with "Hp"). 
    iIntros (v) "[(%l' & -> & Hun' & Hv' & Hp)|(-> & H)]"; 
    wp_apply unwrap_hoare;
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
    Unshelve.
  Admitted.

End HAlloc. End HAlloc.
