From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.
From AllSrc.iris_heap_lang_asm.lib Require Import array.
From AllSrc.intrusive_list Require Import seq.
From AllSrc.allocator Require Import utils.

(* Page allocator
    A lazy slab allocator
    
  Design:
   |-------------------|
   |       next*       |  ~ intrusive not owned
   |-------------------|
   |       prev*       |  ~ intrusive not owned
   |-------------------|
   |       heap        |  ~ pointer to (a) heap 
   |-------------------|
   |      in_full      |  ~ page in full list or not
   |-------------------|
   |     capacity      |  ~ #Blocks initialized
   |-------------------|
   |     reserved      |  ~ total #Blocks in page
   |-------------------|
   |    block size     |  ~ size of block
   |-------------------|
   |       free        |  ~ freelist #1: allocates from this list
   |-------------------|
   |    local_free     |  ~ freelist #2: frees to this list
   |-------------------|
   |       Data        |
   |     res * bs      | 
   |-------------------|
*)

Module PAlloc. Section PAlloc.
  Context `{!heapGS_gen hlc Σ}.

  Implicit Types al l lbase fl lmd ld lh : loc.
  Implicit Types n i res cap size bs fbs : nat.
  Implicit Types full : bool.
  Implicit Types v w : val.

  (* field offsets *)
  Definition f_cap : nat := 4.
  Definition f_res : nat := 5.
  Definition f_bs : nat := 6.
  Definition f_free : nat := 7.
  Definition f_free_local : nat := 8.

  Definition MDSIZE : nat := 9. 
  Definition NULL : loc := 0.

  (* 
    function definitions 
  *)

  Local Definition freelist_pop : val := λ: "fl", 
    if: !"fl" = #NULL then NONE 
    else let: "l" := Seq.pop "fl" in SOME "l".
    
  Local Definition freelist_push : val := Seq.push. 

  Local Definition freelist_free_rec : val := rec: "rec" "l" "bs" :=
    array_free ("l" + #1) ("bs" - #1) ;;
    let: "lv" := !"l" in
    Free "l" ;;
    if: "lv" = #NULL then #() 
    else "rec" "lv" "bs".
        
  Local Definition freelist_free : val := λ: "fl" "bs", 
    let: "flv" := !"fl" in
    Free "fl" ;; 
    if: "flv" = #NULL then #() 
    else freelist_free_rec "flv" "bs".
   
  Definition page_new_alloc : val := λ: "res" "bs" "a", 
    let: "al" := AllocN (#MDSIZE + "res" * "bs") "a" NONE in 
    "al" + #f_cap <- #0 ;;
    "al" + #f_res <- "res" ;;
    "al" + #f_bs <- "bs" ;;
    Seq.new ("al" + #f_free) #NULL ;;
    Seq.new ("al" + #f_free_local) #NULL ;;
    "al".

  Definition page_free : val := λ: "al" "l", 
    freelist_push ("al" + #f_free_local) "l".
    
  Definition page_dealloc : val := λ: "al",
    Free ("al" + #f_cap) ;; 
    Free ("al" + #f_res) ;; 
    let: "bs" := !("al" + #f_bs) in
    Free ("al" + #f_bs) ;; 
    freelist_free ("al" + #f_free) "bs" ;;
    freelist_free ("al" + #f_free_local) "bs" ;;
    #().

  Local Definition freelist_extend : val := rec: "rec" "fl" "lb" "bs" "n" "c" :=
    if: "c" + #1 ≤ "n"
    then freelist_push "fl" ("lb" + ("c" * "bs")) ;;
         "rec" "fl" "lb" "bs" "n" ("c" + #1)
    else #().
    
  Local Definition page_extend : val := λ: "lmd" "ld", 
    let: "res" := !("lmd" + #f_res) in 
    let: "cap" := !("lmd" + #f_cap) in 
    let: "bs" :=  !("lmd" + #f_bs) in
    let: "mext" := if: "cap" = #0 then #1 else "cap" in
    let: "ext" := if: "mext" ≤ "res" - "cap" then "mext" else "res" - "cap" in 
    if: "ext" = #0 then NONE 
    else 
      freelist_extend ("lmd" + #f_free) ("ld" + "cap" * "bs") "bs" ("ext" - #1) #0 ;;
      ("lmd" + #f_cap) <- ("cap" + "ext") ;;
      SOME ("ld" + ("cap" + "ext" - #1) * "bs").

  Definition page_alloc : val := λ: "al", 
    let: "ld" := "al" + #MDSIZE in
    match: freelist_pop ("al" + #f_free) with 
      NONE => 
        match: freelist_pop ("al" + #f_free_local) with 
          NONE => page_extend "al" "ld" 
        | SOME "l" => 
            Seq.swap ("al" + #f_free) ("al" + #f_free_local) ;; 
            SOME "l"
        end
    | SOME "l" => SOME "l"
    end.

  (*
    Representation
  *)
    
  Definition is_valid_loc_internal l al bs res : iProp Σ := 
    ∃ ld i, ⌜ld = (al + MDSIZE)%Z⌝ ∗ ⌜l = (ld + (i * bs))%Z⌝ ∗ ⌜i < res⌝.

  Global Instance is_valid_loc_internal_presist l al bs res : 
    Persistent (is_valid_loc_internal l al bs res).
  Proof. apply _. Qed.
    
  Definition is_valid_loc l al : iProp Σ := 
    ∃ bs res, 
      (al + f_bs)%Z ↦{#free_frac res} #bs ∗ 
      (al + f_res)%Z ↦{#free_frac res} #res ∗ 
      is_valid_loc_internal l al bs res.
  
  Definition is_freelist fl al bs res size : iProp Σ := 
    ∃ L, ⌜length L = size⌝ ∗ ⌜NULL ∉ (fl::L)⌝ ∗ Seq.pred fl L NULL ∗ 
      [∗ list] l ∈ L, 
        ([∗ list] i ∈ seq 1 (bs - 1), ∃ v, (l + i)%Z ↦  v) ∗
        is_valid_loc_internal l al bs res.
    
  Definition is_page (al : loc) (bs res fbs : nat) : iProp Σ := 
    ∃ cap ld size1 size2 , 
      ⌜(0 < al)%Z⌝ ∗  ⌜0 < res⌝ ∗ ⌜0 < bs⌝ ∗ ⌜cap ≤ res⌝ ∗ 
      ⌜ld = (al + MDSIZE)%Z⌝ ∗
      ⌜(fbs = size1 + size2 + (res - cap))%nat⌝ ∗
      (al + f_cap)%Z ↦ #cap ∗ 
      (al + f_res)%Z ↦{#page_frac fbs res} #res ∗ 
      (al + f_bs)%Z ↦{#page_frac fbs res} #bs ∗ 
      is_freelist (al + f_free)%Z al bs res size1 ∗ 
      is_freelist (al + f_free_local)%Z al bs res size2 ∗
      (ld + cap * bs)%Z ↦∗ replicate ((res - cap) * bs) NONEV. 

  (*
     Hoare tripples and Proofs
  *)

  Lemma page_new_alloc_hoare res bs a : 
    {{{ ⌜0 < res⌝ ∗ ⌜0 < bs⌝ ∗ ⌜0 < a⌝ }}} 
      page_new_alloc #res #bs #a 
    {{{ al, RET #al; 
        is_page al bs res res ∗ 
        al ↦∗ [NONEV; NONEV; NONEV; NONEV] ∗ 
        ⌜Z.divide a al⌝
    }}}.
  Proof. 
    iIntros (φ) "(%Hn & %Hbs & %Ha) Hphi". iUnfold page_new_alloc. 
    wp_pures. wp_apply wp_allocN; [lia|lia|done|]. 
    iIntros "%al (%Hl & Ha & HalN & _)". 
    replace (Z.to_nat (MDSIZE + res * bs)) 
    with (S (S (S (S (S (S (S (S (S (res * bs)))))))))) by (unfold MDSIZE; lia). 
    simpl. rewrite !array_cons. rewrite <- !Z.add_assoc. 
    iDestruct "HalN" as "(Hal & Hal1 & Hal2 & Hal3 & Hal4 & Hal5 & Hal6 & Hal7 & 
    Hal8 & HalN)". wp_store. wp_store. wp_store. wp_pures.
    wp_apply (Seq.new_spec with "Hal7"). iIntros "Hfl1". wp_pures.
    wp_apply (Seq.new_spec with "Hal8"). iIntros "Hfl2". wp_pures.
    iApply "Hphi". rewrite 3!Z.add_assoc. iFrame "Hal Hal1 Hal2 Hal3 Ha".
    rewrite array_nil. iSplitL; [|done]. 
    iFrame. iExists 0, (al + MDSIZE)%Z, 0, 0.
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [iPureIntro; lia|]. iSplitR; [done|]. iSplitR; [iPureIntro; lia|].
    rewrite page_frac_own; [|done]. iFrame. rewrite /MDSIZE Z.mul_0_l 
    Nat.sub_0_r Z.add_assoc Z.add_0_r big_sepL_nil length_nil /f_free 
    /f_free_local /NULL. iFrame. iPureIntro. repeat split; 
    apply not_elem_of_cons; split; try lia; apply not_elem_of_nil.
  Qed.

  Local Lemma freelist_pop_hoare al fl bs res size : 
    {{{ is_freelist fl al bs res size }}} 
      freelist_pop #fl
    {{{ vret, RET vret; 
      (⌜vret = NONEV⌝ ∗ ⌜size = 0⌝ ∗ is_freelist fl al bs res size 
        ∨ 
      ∃ l s, ⌜vret = SOMEV #l⌝ ∗ ⌜S s = size⌝ ∗
        ([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v) ∗ 
        is_valid_loc_internal l al bs res ∗ is_freelist fl al bs res s)
    }}}. 
  Proof.
    iIntros (φ) "(%L & %Hlen & %Hnp & Hseq & HbL) Hphi". 
    iUnfold freelist_pop. wp_pures.  
    destruct L; simpl.
    - iAssert (fl ↦ #NULL)%I with "Hseq" as "Hseq". 
      wp_load. wp_pures. iApply "Hphi". iLeft. 
      rewrite length_nil in Hlen. simplify_eq.
      iUnfold is_freelist. iSplitR; [done|]. iSplitR; [done|].
      iExists []. iSplitR; [by rewrite length_nil|]. iSplitR; [done|].
      rewrite big_sepL_nil. by iFrame.
    - iAssert (fl ↦ #l ∗ Seq.pred l L NULL)%I with "Hseq" as "(Hfl & Hseq)". 
      wp_load. wp_pures. apply not_elem_of_cons in Hnp as [H1 Hnp].
      apply not_elem_of_cons in Hnp as [H2 Hnp]. case_bool_decide; [inv H|].
      wp_pures. wp_apply (Seq.pop_spec with "[Hfl Hseq]"). 
      { iApply Seq.pred_cons. iFrame. }
      rewrite length_cons in Hlen.
      iIntros (v) "(Hl & Hseq)". wp_pures. iApply "Hphi".
      iRight. iExists l, (size - 1). iSplitR; [done|]. 
      iSplitR; [iPureIntro; lia|]. iDestruct "HbL" as "(HbL & Hlbs)".
      iFrame. destruct bs; simpl; iDestruct "HbL" as "(H1 & H2)".
      { iFrame. iPureIntro. split; [lia|]. by apply not_elem_of_cons. }
      rewrite Z.add_0_r Nat.sub_0_r. iFrame. iPureIntro. split; [lia|].
      by apply not_elem_of_cons.
  Qed.

  Local Lemma freelist_push_hoare l fl al bs res size : 
    {{{ 
      ⌜0 < bs⌝ ∗ ⌜l ≠ NULL⌝ ∗ is_freelist fl al bs res size ∗ 
      (([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v)) ∗ 
      is_valid_loc_internal l al bs res
    }}}
      freelist_push #fl #l
    {{{ RET #(); is_freelist fl al bs res (size + 1) }}}.
  Proof. 
    iIntros (φ) "(%Hbs & %Hlneq & Hfl & Hun & Hlv) Hphi".
    destruct bs; [lia|]. iDestruct "Hun" as "((%v & Hl) & Hl1bs)". fold seq.
    iDestruct "Hfl" as "(%L & %Hlen & %Hnp & Hcy & HbL)".
    iUnfold freelist_push. rewrite Z.add_0_r.
    wp_apply (Seq.push_spec with "[Hcy Hl]"); [iFrame|].
    iIntros "Hcy". iApply "Hphi". iFrame; simpl. 
    replace (S bs - 1) with bs by lia. iSplitR; [iPureIntro; lia|].
    iSplitR; [iPureIntro; set_solver|]. by rewrite Nat.sub_0_r.
  Qed.

  Local Lemma freelist_free_rec_hoare l L al bs res : 
    {{{ ⌜0 < bs⌝ ∗ ⌜NULL ∉ L⌝ ∗ Seq.pred l L NULL ∗ 
        [∗ list] l ∈ (l::L), 
          ([∗ list] i ∈ seq 1 (bs - 1), ∃ v, (l + i)%Z ↦  v) ∗
          is_valid_loc_internal l al bs res
    }}}
      freelist_free_rec #l #bs
    {{{ RET #(); emp }}}.
  Proof.
    iInduction L as [|l' L IH] forall (l); simpl; 
    iIntros (φ) "(%Hbs & %Hnp & H) Hphi"; iUnfold freelist_free_rec; wp_pures.
    - iDestruct "H" as "(Hl & (Hr & Hvl) & _)". 
      iPoseProof (seq_array_pointsto_eq_gen with "Hr") as "(%vs & %Hl & Hr)".
      wp_apply (wp_array_free with "Hr"); try (rewrite Hl; lia); iIntros; wp_pures. 
      iAssert (l ↦ #NULL)%I with "Hl" as "Hl".
      wp_load. wp_free. wp_pures. by iApply "Hphi".
    - iDestruct "H" as "(Hl & (Hr & Hvl1) & (H2 & Hvl2) & HL)".
      iPoseProof (seq_array_pointsto_eq_gen with "Hr") as "(%vs & %Hl & Hr)";
      wp_apply (wp_array_free with "Hr"); try (rewrite Hl; lia); iIntros; wp_pures. 
      iAssert (l ↦ #l' ∗ Seq.pred l' L NULL)%I with "Hl" as "(Hl & Hl')".
      wp_load. wp_pures. wp_free. wp_pures. 
      apply not_elem_of_cons in Hnp as [H1 H2]. case_bool_decide; [inv H0|].
      wp_pure. fold freelist_free_rec. iApply ("IH" with "[Hl' H2  Hvl2 HL]"); 
      [iFrame|iNext]; done.
  Qed.

  Local Lemma freelist_free_hoare fl al bs res size :
    {{{ ⌜0 < bs⌝ ∗ is_freelist fl al bs res size }}} 
      freelist_free #fl #bs
    {{{ RET #(); emp }}}.
  Proof.
    iIntros (φ) "(%Hbs & (%L & %Hlen & %Hnp & Hcy & HbL)) Hphi". 
    iUnfold freelist_free. destruct L; simpl in *; wp_pures.
    { iAssert (fl ↦ #NULL)%I with "Hcy" as "Hcy". 
      wp_load. wp_free. wp_pures. by iApply "Hphi". }
    iAssert (fl ↦ #l ∗ Seq.pred l L NULL)%I with "Hcy" as "(Hfl & Hcy)".
    wp_load. wp_pures. wp_free. wp_pures.
    apply not_elem_of_cons in Hnp as [H1 Hnp]. 
    apply not_elem_of_cons in Hnp as [H2 Hnp].
    case_bool_decide; [inv H|]. wp_pures. 
    by wp_apply (freelist_free_rec_hoare with "[Hcy HbL]"); [by iFrame|].
  Qed.

  Local Lemma valid_loc_not_null  l al bs res : 
    (0 < al)%Z → 
    is_valid_loc_internal l al bs res ⊢ ⌜l ≠ NULL⌝.
  Proof.
    iIntros (Hal) "(%ld & %i & %Hld & %Hl & %Hi)". iPureIntro. rewrite /NULL. lia.
  Qed.

  Lemma page_free_hoare l al bs res fbs : 
    {{{ 
      is_page al bs res fbs ∗ 
      (([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v)) ∗ 
      is_valid_loc l al 
    }}}
      page_free #al #l
    {{{ RET #(); is_page al bs res (S fbs) }}}.
  Proof.
    iIntros (φ) "((%cap & %ld & %b1 & %b2 & %Hal & %Hr & %Hbs & %Hcr & -> & 
    %Hfbs & Hcap & Hres & Hbs & Hfl & Hfl2 & Hun) & Hlbs & Hlv) Hphi". 
    iUnfold page_free. wp_pures. 
    iDestruct "Hlv" as "(%bs' & %res' & Hbs' & Hres' & Hlvi)".  
    iPoseProof (valid_loc_not_null with "Hlvi") as "%H"; [done|].
    iCombine "Hbs'" "Hbs" gives %[_ Heq1']. 
    iCombine "Hres'" "Hres" gives %[_ Heq2']. 
    specialize (inject_litint_nat _ _ Heq1') as Heq1. 
    specialize (inject_litint_nat _ _ Heq2') as Heq2. simplify_eq.
    iApply (freelist_push_hoare with "[Hfl2 Hlbs Hlvi]"); [iFrame; auto|]. 
    iNext. iIntros "Hfl2". iApply "Hphi". 
    iFrame. iSplitR; [done|]. iSplitR; [done|]. 
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR. { iPureIntro. lia. }
    iCombine "Hres" "Hres'" as "Hres". iCombine "Hbs" "Hbs'" as "Hbs". 
    rewrite -page_frac_to_free_frac. by iFrame.
  Qed.

  Lemma page_dealloc_hoare al bs res : 
    {{{ is_page al bs res res }}} 
      page_dealloc #al
    {{{ RET #(); emp }}}.
  Proof.
    iIntros (φ) "(%cap & %ld & %s1 & %s2 & %Hal & %Hr & %Hbs &
    %Hcr & -> & %Hfbs & Hcap & Hres & Hbs & Hfl & Hfl2 & Hun) Hphi".
    iUnfold page_dealloc. wp_free. rewrite page_frac_own; [|done].
    wp_free. wp_load. wp_free. wp_pures.
    wp_apply (freelist_free_hoare with "[Hfl]"); [auto|]. 
    iIntros. wp_pures.
    wp_apply (freelist_free_hoare with "[Hfl2]"); [auto|]. 
    iIntros. wp_pures. by iApply "Hphi".
  Qed.

  Local Lemma freelist_extend_hoare fl al ld res bs size lb cap n c d : 
    d = n - c →
    (0 < al)%Z →
    ld = (al + MDSIZE)%Z →
    lb = (ld + (cap * bs))%Z → 
    cap ≤ res →
    n ≤ res - cap → 
    bs > 0 →
    {{{ 
      is_freelist fl al bs res size ∗ (lb + (c * bs))%Z ↦∗ replicate (d * bs) NONEV 
    }}} 
      freelist_extend #fl #lb #bs #n #c
    {{{ RET #(); is_freelist fl al bs res (size + d) }}}. 
  Proof. 
    iInduction d as [|d IH] forall (size c); simpl; 
    iIntros (Hd Hal -> -> Hcr Hd2 Hbs φ) "(Hfl & Hun) Hphi";
    iUnfold freelist_extend; wp_pures. 
    { case_bool_decide; [lia|]. wp_pures. iApply "Hphi". by rewrite Nat.add_0_r. }
    case_bool_decide; [|lia]. wp_pures. 
    rewrite replicate_add array_app length_replicate. 
    iDestruct "Hun" as "(Hun1 & Hun2)". 
    wp_apply (freelist_push_hoare with "[Hfl Hun1]").
    { iFrame. iSplitR; [done|]. iSplitR; [iPureIntro; rewrite /NULL; lia|].
      iSplitL "Hun1". 
      - iApply big_sepL_mono; 
        [|iApply seq_array_pointsto_eq; iApply "Hun1"]. iIntros. auto.
      - iExists (al + MDSIZE)%Z, (cap + c). iPureIntro. split; 
        unfold MDSIZE; lia. }
    iIntros "Hfl". wp_pure. wp_pure. wp_pure. fold freelist_extend.  
    assert (Heq : (Z.of_nat c + 1)%Z = Z.of_nat (c + 1)) by lia. rewrite Heq. 
    iApply ("IH" with "[] [] [] [] [] [] [] [Hfl Hun2]"); try iPureIntro;
    [lia|done|done|done|done|lia|done| |].
    { iFrame. rewrite <-Z.add_assoc. 
      by rewrite Nat2Z.inj_add Z.mul_add_distr_r Z.mul_1_l !Z.add_assoc. }
    iNext. iIntros. iApply "Hphi". by rewrite -Nat.add_assoc Nat.add_1_l. 
  Qed. 

  Local Lemma page_extend_hoare al ld res cap bs fbs : 
    (0 < al)%Z →
    0 < res →
    0 < bs →
    cap ≤ res →
    ld = (al + MDSIZE)%Z →
    fbs = res - cap → 
    {{{ 
      (al + f_cap)%Z ↦ #cap ∗ 
      (al + f_res)%Z ↦{#page_frac fbs res} #res ∗ 
      (al + f_bs)%Z ↦{#page_frac fbs res} #bs ∗ 
      is_freelist (al + f_free)%Z al bs res 0 ∗ 
      is_freelist (al + f_free_local)%Z al bs res 0 ∗
      (ld + cap * bs)%Z ↦∗ replicate ((res - cap) * bs) NONEV 
    }}} 
      page_extend #al #ld 
    {{{ vret, RET vret; 
      ((∃ l, ⌜vret = SOMEV #l⌝ ∗ ⌜fbs > 0⌝ ∗ 
        (([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v)) ∗ 
        is_valid_loc l al ∗ is_page al bs res (fbs - 1)) 
        ∨  
      ⌜vret = NONEV⌝ ∗ ⌜fbs = 0⌝ ∗ is_page al bs res fbs) 
    }}}.
  Proof. 
    iIntros (Hal Hr Hbs Hcr Hld Hfbs φ) "(Hcap & Hres & Hbs & Hfl & Hfl2 & Hun) 
    Hphi". iUnfold page_extend. wp_pures. wp_load. wp_load. wp_load. 
    wp_pures. destruct (decide (cap = 0)) as [Hc | Hc]. 
    { rewrite Hc. wp_pures. case_bool_decide; [|lia].
      assert (fbs > 0) by lia. destruct fbs; [lia|]. wp_pures. 
      rewrite Z.mul_0_l Z.add_0_r.
      wp_apply ((freelist_extend_hoare (al + f_free)%Z al ld res bs 
      0 ld 0 0 0 0) with "[Hfl]"); try lia;
      [rewrite array_nil; iFrame|]. 
      rewrite Nat.sub_0_r. destruct res; [lia|]. simpl. 
      rewrite replicate_add array_app. iDestruct "Hun" as "(Hun1 & Hun2)". 
      iIntros "Hfl". wp_store. wp_pures. iApply "Hphi". iLeft.
      rewrite length_replicate Z.add_0_l Z.sub_diag Z.mul_0_l Z.add_0_r. 
      iExists ld. iSplitR; [done|]. iSplitR; [done|]. iSplitL "Hun1".
      { iApply big_sepL_mono; [|by iApply seq_array_pointsto_eq]. 
        iIntros. auto. }
      rewrite page_frac_to_free_frac.
      iDestruct "Hres" as "(Hresp & Hres1)".
      iDestruct "Hbs" as "(Hbsp & Hbs1)".
      iSplitL "Hres1 Hbs1". 
      { iFrame. iExists ld, 0. rewrite Z.mul_0_l Z.add_0_r. 
        iPureIntro. split; [done|]. split; [done|lia]. }
      rewrite Nat.sub_0_r. iFrame. iExists 1, ld. 
      rewrite Z.mul_1_l. replace (Z.of_nat 1) with (1%Z) by lia. 
      replace (S res - 1) with (res) by lia. iFrame. 
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
      iSplitR; [iPureIntro; lia|]. iPureIntro. lia. }
    case_bool_decide; [inv H; lia|]. wp_pures. case_bool_decide.
    { wp_pures. case_bool_decide; [inv H1; lia|]. wp_pures. 
      assert (Z.of_nat (cap - 1) = (Z.of_nat cap - 1)%Z) by lia. rewrite -H2.
      (*split: (cap - 1) * bs + (res - cap - (cap - 1)) * bs)*)
      assert ((res - cap) * bs = (cap - 1) * bs + (res - cap - (cap - 1)) * bs) 
      by lia. rewrite H3 replicate_add array_app. 
      iDestruct "Hun" as "(Hun1 & Hun2)". rewrite length_replicate.
      wp_apply (freelist_extend_hoare (al + f_free)%Z al ld res bs 0 
      (ld + (cap * bs))%Z cap (cap - 1) 0 (cap - 1) with "[Hfl Hun1]"); try lia.
      { iFrame. by rewrite Z.mul_0_l Z.add_0_r. }
      iIntros "Hfl". rewrite Nat.add_0_l. wp_store. wp_pures. iApply "Hphi".  
      (*split: bs of *)
      replace (res - cap - (cap - 1)) with (1 + (res - cap - cap)) by lia. 
      rewrite Nat.mul_add_distr_r Nat.mul_1_l replicate_add array_app.
      iDestruct ("Hun2") as "(Hun1 & Hun2)". iLeft. 
      rewrite length_replicate -!Z.add_assoc. iExists _. iSplitR; [done|]. 
      iSplitR; [iPureIntro; lia|].
      iSplitL "Hun1". 
      { replace ((5 + (cap + cap - 1) * bs)%Z)  (*relies on earlier asserts*)
        with (5 + cap * bs + ((cap - 1) * bs)%nat)%Z by lia. 
        iApply big_sepL_mono; [|iApply seq_array_pointsto_eq; iApply "Hun1"].
        iIntros. iExists NONEV. unfold MDSIZE.
        by replace (ld + (cap * bs + ((cap - 1) * bs)%nat))%Z 
        with (ld + (cap + cap - 1) * bs)%Z by lia. }
      assert (fbs > 0) by lia. destruct fbs; [lia|].
      rewrite page_frac_to_free_frac. 
      iDestruct "Hres" as "(Hresp & Hres1)".
      iDestruct "Hbs" as "(Hbsp & Hbs1)".
      iSplitL "Hres1 Hbs1". 
      { iFrame. iExists ld, (cap + cap - 1). 
        rewrite -Nat2Z.inj_add. iSplitR; [done|iPureIntro; lia]. }
      rewrite -Nat2Z.inj_add. replace (S fbs - 1) with fbs by lia. iFrame. 
      iExists ld. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
      iSplitR; [iPureIntro; lia|]. iSplitR; [done|].
      iSplitR; [iPureIntro; lia|].
      assert ((ld + cap * bs + (((cap - 1) * bs)%nat + bs))%Z 
      = (ld + (cap + cap)%nat * bs)%Z) by lia.
      assert ((res - cap - cap) * bs = (res - (cap + cap)) * bs) by lia.
      by rewrite -H5 H6 Z.add_assoc.  }
    wp_pures. destruct (decide (res - cap = 0)) as [Hcr2 | Hcr2]. 
    { rewrite -Nat2Z.inj_sub; [|done]. rewrite Hcr2. wp_pures. 
      iApply "Hphi". iRight. iSplitR; [done|]. iFrame. 
      replace fbs with 0 by lia. iFrame. iSplitR; [done|]. iExists ld. iSplitR; [done|].
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iSplitR; [|by rewrite Hcr2]. iPureIntro. lia. }
    case_bool_decide; [inv H1; lia|]. wp_pures.
    (* split (res - cap - 1) * bs + bs  *)
    assert (res - cap = (res - cap - 1) + 1) by lia. rewrite H2. 
    rewrite Nat.mul_add_distr_r Nat.mul_1_l replicate_add array_app 
    length_replicate. iDestruct "Hun" as "(Hun1 & Hun2)". 
    iPoseProof (freelist_extend_hoare (al + f_free)%Z al ld res bs 0 
    (ld + cap * bs)%Z cap (res - cap - 1) 0 (res - cap - 1)) as "H";
    [lia|done|done|lia|lia|lia|done| ]. 
    replace (Z.of_nat (res - cap - 1)) with (Z.of_nat res - Z.of_nat cap - 1)%Z 
    by lia. wp_apply ("H" with "[Hfl Hun1]"). 
    (*
    assert (Z.of_nat (res - cap - 1) = (Z.of_nat res - Z.of_nat cap - 1)%Z) 
    by lia. rewrite H3. wp_apply ("H" with "[Hfl Hun1]"). *)
    { rewrite -Z.add_assoc Z.mul_0_l Z.add_0_r. iFrame. }
    iIntros "Hfl". wp_store. wp_pures. iApply "Hphi". iLeft.
    assert ((ld + cap * bs + ((res - cap - 1) * bs)%nat)%Z 
    = (ld + (cap + (res - cap) - 1) * bs)%Z) by lia. rewrite H3. 
    iExists _. iSplitR; [done|]. iSplitR; [iPureIntro; lia|].
    iSplitL "Hun2".
    { iApply big_sepL_mono; [|by iApply seq_array_pointsto_eq]. iIntros. auto. }
    assert (fbs > 0) by lia. destruct fbs; [lia|].
    rewrite page_frac_to_free_frac. 
    iDestruct "Hres" as "(Hresp & Hres1)".
    iDestruct "Hbs" as "(Hbsp & Hbs1)".
    iSplitL "Hres1 Hbs1". 
    { iFrame. iExists _, (cap + (res - cap) - 1). iSplitR; [done|]. 
      iPureIntro. lia. }
    rewrite -Nat2Z.inj_sub; [|lia]. rewrite -Nat2Z.inj_add. 
    replace (S fbs - 1) with fbs by lia.
    iFrame. iExists _. iSplitR; [done|].
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [iPureIntro; lia|]. 
    iSplitR; [done|]. iSplitR.
    { iPureIntro. lia. }
    replace (res - (cap + (res - cap))) with 0 by lia. 
    rewrite Nat.mul_0_l. simpl. by rewrite array_nil.
  Qed.

  Lemma page_alloc_hoare al bs res fbs :
    {{{ is_page al bs res fbs }}}
      page_alloc #al
    {{{ vret, RET vret; 
      (∃ l, ⌜vret = SOMEV #l⌝ ∗ ⌜fbs > 0⌝ ∗
          ([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v) ∗ 
          is_valid_loc l al ∗ is_page al bs res (fbs - 1))
        ∨ 
        ⌜vret = NONEV⌝ ∗ ⌜fbs = 0⌝ ∗ is_page al bs res fbs
    }}}.
  Proof.
    iIntros (φ) "(%cap & %ld & %b1 & %b2 & %Hal & %Hr & %Hbs & %Hcr & -> & 
    %Hf & Hcap & Hres & Hbs & Hfl & Hfl2 & Hun) Hphi". 
    iUnfold page_alloc. wp_pures. 
    wp_apply (freelist_pop_hoare with "[Hfl]"); [by iFrame|].
    iIntros (v) "[(-> & -> & Hfl) | 
    (%l & %s & -> & %Hs & Hlbs & Hlv & Hfl)]"; wp_pures.
    { wp_apply (freelist_pop_hoare with "[Hfl2]"); [by iFrame|].
      iIntros (v) "[(-> & -> & Hfl2) | 
      (%l & %s' & -> & %Hs' & Hlbs & #Hlv & Hfl2)]"; wp_pures.
      { wp_apply ((page_extend_hoare al (al + MDSIZE)%Z res cap bs fbs) 
        with "[Hun Hcap Hres Hbs Hfl Hfl2]"); try (done || lia); iFrame. } 
      iDestruct "Hfl" as "(%L & %Hlen & %Hnp & Hfl & _)".
      apply nil_length_inv in Hlen. rewrite Hlen.
      rewrite -Hs' in Hf. destruct s'; simpl. 
      - iDestruct "Hfl2" as "(%L' & %Hlen' & %Hnp' & Hfl2 & _)". 
        apply nil_length_inv in Hlen'. rewrite Hlen'. rewrite Hlen' in Hnp, Hnp'.
        wp_apply (Seq.swap_spec with "[Hfl Hfl2]"); [iFrame|].
        iIntros "(Hfl1 & Hfl2)". wp_pures. iApply "Hphi". iLeft.
        iFrame. iSplitR; [done|]. destruct fbs; [lia|]. 
        rewrite page_frac_to_free_frac.
        iDestruct "Hres" as "(Hresp & Hres1)".
        iDestruct "Hbs" as "(Hbsp & Hbs1)".
        iSplitR; [iPureIntro; lia|].
        iSplitL "Hres1 Hbs1"; [by iFrame|].
        replace (S fbs - 1) with fbs by lia.
        iExists 0, 0. iFrame. rewrite length_nil big_sepL_nil. 
        iPureIntro. repeat (split; [done|]). simplify_eq. 
        split; [lia|]. auto. 
      - iDestruct "Hfl2" as "(%L' & %Hlen' & %Hnp' & Hfl2 & HL')". 
        wp_apply (Seq.swap_spec with "[Hfl Hfl2]"); [iFrame|].
        iIntros "(Hfl1 & Hfl2)". wp_pures. iApply "Hphi". iLeft.
        iFrame. iSplitR; [done|]. destruct fbs; [lia|]. 
        rewrite page_frac_to_free_frac.
        iDestruct "Hres" as "(Hresp & Hres1)".
        iDestruct "Hbs" as "(Hbsp & Hbs1)".
        iSplitR; [iPureIntro; lia|].
        iSplitL "Hres1 Hbs1"; [by iFrame|].
        replace (S fbs - 1) with fbs by lia.
        iExists (S s'), 0. iFrame. rewrite length_nil big_sepL_nil. 
        apply not_elem_of_cons in Hnp' as [H1 H2].
        apply not_elem_of_cons in Hnp as [H3 H4].
        iPureIntro. repeat (split; [done|]). simplify_eq. 
        split; [lia|]. repeat split; [done|..]; set_solver. }
    iApply "Hphi". iLeft. iFrame. iSplitR; [done|]. 
    destruct fbs; [lia|]. rewrite page_frac_to_free_frac.
    iDestruct "Hres" as "(Hresp & Hres1)".
    iDestruct "Hbs" as "(Hbsp & Hbs1)".
    iSplitR; [iPureIntro; lia|].
    iSplitL "Hres1 Hbs1"; [by iFrame|].
    replace (S fbs - 1) with fbs by lia.
    iFrame. iPureIntro. lia.
  Qed.

  Lemma page_res_geq_fbs al bs res fbs : 
    res < fbs → 
    is_page al bs res fbs ⊢ False.
  Proof.
    iIntros (Hgeq) "Hp".
    iDestruct "Hp" as "(%cap & %ld & %b1 & %b2 & %Hal & %Hr & %Hbs & 
    %Hcr & -> & %Hf & Hcap & Hres & Hbs & Hfl & Hfl2 & Hun)". 
    assert (fbs = res + (fbs - res)) by lia.
    remember (fbs - res) as d. destruct d; [lia|]. rewrite H. 
    rewrite page_frac_split page_frac_own; [|done].
    iDestruct (pointsto_valid with "Hres") as %Hv.
    apply dfrac_valid in Hv. by apply Qp.not_add_le_l in Hv.
  Qed.
   
  Lemma get_usefull_pure_facts al bs res fbs l : 
    PAlloc.is_page al bs res fbs -∗ 
    PAlloc.is_valid_loc l al -∗ 
    PAlloc.is_valid_loc_internal l al bs res ∗ ⌜(0 < al)%Z⌝ ∗ ⌜(0 < res)⌝.
  Proof.
    iIntros "(%cap & %ld & %b1 & %b2 & %Hal & %Hr & %Hbs & %Hcr & -> & 
    %Hfbs & Hcap & Hres & Hbs & Hfl & Hfl2 & Hun) (%bs' & %res' & Hbs' & Hres'
    & Hint)". 
    iSplitL; [|done]. 
    iCombine "Hres" "Hres'" gives %[_ Heqres].
    iCombine "Hbs" "Hbs'" gives %[_ Heqbs].
    apply inject_litint_nat in Heqres.
    apply inject_litint_nat in Heqbs.
    by simplify_eq.
  Qed.

End PAlloc. End PAlloc.
