From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.
From AllSrc.iris_heap_lang_asm.lib Require Import array.
From AllSrc.allocator Require Import utils.

(* Page allocator
  - A lazy slab allocator
  - TODO(Ben): segment index later?
  - TODO(Ben): in_full is only set when it is moved from and to full list 
      it is used in free function to check if we should move out of 
      the full list or not, for now we do nothing with it.
  
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

  (* 
    function definitions 
  *)

  Local Definition freelist_pop : val := λ: "fl",
    match: !"fl" with
      NONE => NONE
    | SOME "l" => "fl" <- !"l" ;; SOME "l" 
    end.

  Local Definition freelist_push : val := λ: "fl" "l",
    "l" <- !"fl" ;; 
    "fl" <- SOME "l".
  
  Local Definition freelist_free_rec : val := rec: "rec" "l" "bs" :=
    array_free ("l" + #1) ("bs" - #1) ;;
    let: "lv" := !"l" in
    Free "l" ;;
    match: "lv" with 
      NONE => #() 
    | SOME "ln" => "rec" "ln" "bs"
    end.
    
  Local Definition freelist_free : val := λ: "fl" "bs", 
    let: "flv" := !"fl" in
    Free "fl" ;; 
    match: "flv" with 
      NONE => #() 
    | SOME "ln" => freelist_free_rec "ln" "bs"
    end.
   
  Definition page_new_alloc : val := λ: "res" "bs" "a", 
    let: "al" := AllocN (#MDSIZE + "res" * "bs") "a" NONE in 
    "al" + #f_cap <- #0 ;;
    "al" + #f_res <- "res" ;;
    "al" + #f_bs <- "bs" ;;
    "al" + #f_free <- NONE ;;
    "al" + #f_free_local <- NONE ;;
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

  (*
  Definition page_try_free : val := λ: "al" "l", 
    page_free "al" "l" ;;
    if: (!("al" + #f_res) = !("al" + #f_cap)) &&   
        (!("al" + #f_free) = NONE) && 
        (!("al" + #f_free_local) = NONE)
    then page_dealloc "al" 
    else #().
  *)

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
          "al" + #f_free <- !("al" + #f_free_local) ;;
          "al" + #f_free_local <- NONE ;;
          SOME "l"
        end
    | SOME "l" => SOME "l"
    end.

  (*
    Representation
  *)
    
  Definition is_valid_loc_internal l al bs res : iProp Σ := 
    ∃ ld i, ⌜ld = (al + MDSIZE)%Z⌝ ∗ ⌜l = (ld + (i * bs))%Z⌝ ∗ ⌜i < res⌝.
    
  Definition is_valid_loc l al : iProp Σ := 
    ∃ bs res, 
      (al + f_bs)%Z ↦{#free_frac res} #bs ∗ 
      (al + f_res)%Z ↦{#free_frac res} #res ∗ 
      is_valid_loc_internal l al bs res.
  
  Fixpoint is_freelist_rec l al bs res size : iProp Σ := 
    match size with 
    | O => l ↦ NONEV ∗ ([∗ list] i ∈ seq 1 (bs - 1), ∃ v, (l + i)%Z ↦  v) ∗ 
           is_valid_loc_internal l al bs res
    | S s => ∃ l1, l ↦ SOMEV #l1 ∗ ([∗ list] i ∈ seq 1 (bs - 1), ∃ v, (l + i)%Z ↦  v) ∗
           is_valid_loc_internal l al bs res ∗ is_freelist_rec l1 al bs res s
    end.
    
  Definition is_freelist fl al bs res size : iProp Σ := 
    match size with 
    | 0 => fl ↦ NONEV 
    | S s => ∃ l1, fl ↦ SOMEV #l1 ∗ is_freelist_rec l1 al bs res s 
    end.
  
  (* TODO(Ben): now there is no point in is valid,  
     since all it needs is bs and res.. so could just pass 
     but without res deallocation becomes annoying 
     since you need to now fbs = res and doing 
     this in another way seems tedious *)
  Definition is_page al bs res fbs : iProp Σ := 
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
        is_page al bs res res ∗ al ↦∗ [NONEV; NONEV] ∗ ⌜Z.divide a al⌝
    }}}.
  Proof. 
    iIntros (φ) "(%Hn & %Hbs & %Ha) Hphi". iUnfold page_new_alloc. 
    wp_pures. wp_apply wp_allocN; [lia|lia|done|]. 
    iIntros "%al (Hl & Ha & HalN & _)". 
    replace (Z.to_nat (MDSIZE + res * bs)) 
    with (S (S (S (S (S (S (S (S (S (res * bs)))))))))) by (unfold MDSIZE; lia). 
    simpl. rewrite !array_cons. rewrite <- !Z.add_assoc. 
    iDestruct "HalN" as "(Hal & Hal1 & Hal2 & Hal3 & Hal4 & Hal5 & Hal6 & Hal7 & 
    Hal8 & HalN)". wp_store. wp_store. wp_store. wp_store. wp_store. 
    iApply "Hphi". iFrame "Hal Hal1 Ha". rewrite array_nil. iSplitL; [|done]. 
    iFrame. iExists 0, (al + MDSIZE)%Z, 0, 0.
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [iPureIntro; lia|]. 
    iSplitR; [done|]. iSplitR; [iPureIntro; lia|].
    rewrite page_frac_own; [|done]. iFrame.
    by rewrite /MDSIZE Z.mul_0_l Nat.sub_0_r Z.add_assoc Z.add_0_r.
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
    iIntros (φ) "Hfl Hphi". 
    destruct size; [|iDestruct "Hfl" as "(%l1 & Hfl & Hflr)"]; 
    iUnfold freelist_pop; wp_load; wp_pures.
    { iApply "Hphi". iFrame. by iLeft. } 
    destruct size; simpl.
    { iDestruct "Hflr" as "(Hl1 & Hl1r & Hl1v)".
      wp_load. wp_store. wp_pures. iApply "Hphi". 
      iRight. iExists l1. iFrame. iExists 0. 
      iSplitR; [done|]. iSplitR; [by iPureIntro|]. 
      destruct bs; simpl; [auto|].
      rewrite Nat.sub_0_r Z.add_0_r. by iFrame.  }
    iDestruct "Hflr" as "(%l & Hl1 & Hl1r & Hl1v & Hflr)". 
    wp_load. wp_store. wp_pures. iApply "Hphi". iRight. 
    iFrame. iExists (S size). iSplitR; [done|]. 
    iSplitR; [done|]. iFrame.
    destruct bs; simpl; [done|].
    rewrite Nat.sub_0_r Z.add_0_r. by iFrame. 
  Qed.

  Local Lemma freelist_push_hoare l fl al bs res size : 
    {{{ 
      ⌜bs > 0⌝ ∗ is_freelist fl al bs res size ∗ 
      (([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v)) ∗ 
      is_valid_loc_internal l al bs res
    }}}
      freelist_push #fl #l
    {{{ RET #(); is_freelist fl al bs res (size + 1) }}}.
  Proof. 
    simpl. iIntros (φ) "(%Hbs & Hfl & Hun & Hlv) Hphi".
    destruct bs; [lia|]. iDestruct "Hun" as "((%v & Hl) & Hl1bs)". fold seq.
    destruct size; [|iDestruct "Hfl" as "(%l1 & Hfl & Hflr)"]; 
    iUnfold freelist_push; wp_load; rewrite Z.add_0_r; wp_store; wp_store; 
    iApply "Hphi". 
    { iFrame. by replace (S bs - 1) with bs by lia. }
    replace (S size + 1) with (S (S (size))) by lia.
    simpl. iFrame. by rewrite Nat.sub_0_r. 
  Qed.

  Local Lemma freelist_free_rec_hoare l al bs res size : 
    {{{ ⌜bs > 0⌝ ∗ is_freelist_rec l al bs res size }}}
      freelist_free_rec #l #bs
    {{{ RET #(); emp }}}.
  Proof.
    iInduction size as [|size IH] forall (l); simpl; 
    iIntros (φ) "(%Hbs & H) Hphi"; iUnfold freelist_free_rec.
    - iDestruct "H" as "(Hl & Hr & Hv)". wp_pures.  
      iPoseProof (seq_array_pointsto_eq_gen with "Hr") as "(%vs & %Hl & Hr)".
      wp_apply (wp_array_free with "Hr"); [rewrite Hl; lia|]. 
      iIntros. wp_pures. wp_load. wp_free. wp_pures.
      iApply "Hphi". done.
    - iDestruct "H" as "(%l1 & Hl & Hr & Hv & Hflr)". wp_pures.
      iPoseProof (seq_array_pointsto_eq_gen with "Hr") as "(%vs & %Hl & Hr)".
      wp_apply (wp_array_free with "Hr"); [rewrite Hl; lia|]. 
      iIntros. wp_pures. wp_load. wp_free. wp_pure. wp_pure.
      wp_pure. wp_pure. wp_pure. fold freelist_free_rec. 
      iApply ("IH" with "[Hflr]"); auto.
  Qed.

  Local Lemma freelist_free_hoare fl al bs res size :
    {{{ ⌜bs > 0⌝ ∗ is_freelist fl al bs res size }}} 
      freelist_free #fl #bs
    {{{ RET #(); True }}}.
  Proof.
    destruct size; iIntros (φ) "(%Hbs & H) Hphi"; iUnfold freelist_free; 
    [|iDestruct "H" as "(%l1 & Hl & Hflr)"]; wp_pures; wp_load; wp_free; 
    wp_pures; [by iApply "Hphi"|].
    wp_apply (freelist_free_rec_hoare with "[Hflr]"); auto.
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
    rewrite -page_frac_to_free_fac. by iFrame.
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
    iIntros (Hd -> -> Hcr Hd2 Hbs φ) "(Hfl & Hun) Hphi";
    iUnfold freelist_extend; wp_pures. 
    { case_bool_decide; [lia|]. wp_pures. iApply "Hphi". by rewrite Nat.add_0_r. }
    case_bool_decide; [|lia]. wp_pures. 
    rewrite replicate_add array_app length_replicate. 
    iDestruct "Hun" as "(Hun1 & Hun2)". 
    wp_apply (freelist_push_hoare with "[Hfl Hun1]").
    { iFrame. iSplitR; [done|]. iSplitL "Hun1". 
      - iApply big_sepL_mono; 
        [|iApply seq_array_pointsto_eq; iApply "Hun1"]. iIntros. auto.
      - iExists (al + MDSIZE)%Z, (cap + c). iPureIntro. split; 
        unfold MDSIZE; lia. }
    iIntros "Hfl". wp_pure. wp_pure. wp_pure. fold freelist_extend.  
    assert (Heq : (Z.of_nat c + 1)%Z = Z.of_nat (c + 1)) by lia. rewrite Heq. 
    iApply ("IH" with "[] [] [] [] [] [] [Hfl Hun2]"); try iPureIntro;
    [lia|done|done|done|lia|done| |].
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
      ((∃ l, ⌜vret = SOMEV #l⌝ ∗ (([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v)) ∗ 
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
      iExists ld. iSplitR; [done|]. iSplitL "Hun1".
      { iApply big_sepL_mono; [|by iApply seq_array_pointsto_eq]. 
        iIntros. auto. }
      rewrite page_frac_to_free_fac.
      iDestruct "Hres" as "(Hresp & Hres1)".
      iDestruct "Hbs" as "(Hbsp & Hbs1)".
      iSplitL "Hres1 Hbs1". 
      { iFrame. iExists ld, 0. rewrite Z.mul_0_l Z.add_0_r. 
        iPureIntro. split; [done|]. split; [done|lia]. }
      rewrite Nat.sub_0_r. iFrame. iExists 1, ld, 0, 0. 
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
      iSplitL "Hun1". 
      { replace ((5 + (cap + cap - 1) * bs)%Z)  (*relies on earlier asserts*)
        with (5 + cap * bs + ((cap - 1) * bs)%nat)%Z by lia. 
        iApply big_sepL_mono; [|iApply seq_array_pointsto_eq; iApply "Hun1"].
        iIntros. iExists NONEV. unfold MDSIZE.
        by replace (ld + (cap * bs + ((cap - 1) * bs)%nat))%Z 
        with (ld + (cap + cap - 1) * bs)%Z by lia. }
      assert (fbs > 0) by lia. destruct fbs; [lia|].
      rewrite page_frac_to_free_fac. 
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
    [lia|done|done|lia|lia|done| ]. 
    replace (Z.of_nat (res - cap - 1)) with (Z.of_nat res - Z.of_nat cap - 1)%Z 
    by lia. wp_apply ("H" with "[Hfl Hun1]"). 
    (*
    assert (Z.of_nat (res - cap - 1) = (Z.of_nat res - Z.of_nat cap - 1)%Z) 
    by lia. rewrite H3. wp_apply ("H" with "[Hfl Hun1]"). *)
    { rewrite -Z.add_assoc Z.mul_0_l Z.add_0_r. iFrame. }
    iIntros "Hfl". wp_store. wp_pures. iApply "Hphi". iLeft.
    assert ((ld + cap * bs + ((res - cap - 1) * bs)%nat)%Z 
    = (ld + (cap + (res - cap) - 1) * bs)%Z) by lia. rewrite H3. 
    iExists _. iSplitR; [done|]. iSplitL "Hun2".
    { iApply big_sepL_mono; [|by iApply seq_array_pointsto_eq]. iIntros. auto. }
    assert (fbs > 0) by lia. destruct fbs; [lia|].
    rewrite page_frac_to_free_fac. 
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
      (∃ l, ⌜vret = SOMEV #l⌝ ∗ 
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
    iIntros (v) "[(-> & -> & Hfl) | (%l & %s & -> & %Hs & Hlbs & Hlv & Hfl)]"; 
    wp_pures.
    { wp_apply (freelist_pop_hoare with "[Hfl2]"); [by iFrame|].
      iIntros (v) "[(-> & -> & Hfl2) | 
      (%l & %s' & -> & %Hs' & Hlbs & #Hlv & Hfl2)]"; wp_pures.
      { wp_apply ((page_extend_hoare al (al + MDSIZE)%Z res cap bs fbs) 
        with "[Hun Hcap Hres Hbs Hfl Hfl2]"); try (done || lia); iFrame. }
      rewrite -Hs' in Hf. destruct s'; simpl; 
      [|iDestruct "Hfl2" as "(%l1 & Hfl2 & Hflr)"]; 
      wp_load; wp_store; wp_store; wp_pures; iApply "Hphi"; iLeft.
      - iFrame. iSplitR; [done|]. destruct fbs; [lia|]. 
        rewrite page_frac_to_free_fac.
        iDestruct "Hres" as "(Hresp & Hres1)".
        iDestruct "Hbs" as "(Hbsp & Hbs1)".
        iSplitL "Hres1 Hbs1"; [by iFrame|].
        replace (S fbs - 1) with fbs by lia.
        iExists 0, 0. iFrame. iPureIntro. lia.
      - iFrame.  
        iSplitR; [done|]. destruct fbs; [lia|]. 
        rewrite page_frac_to_free_fac.
        iDestruct "Hres" as "(Hresp & Hres1)".
        iDestruct "Hbs" as "(Hbsp & Hbs1)".
        iSplitL "Hres1 Hbs1"; [by iFrame|].
        replace (S fbs - 1) with fbs by lia.
        iExists (S s'), 0. iFrame. iPureIntro. lia. }
    iApply "Hphi". iLeft. iFrame. 
    iSplitR; [done|]. destruct fbs; [lia|]. 
    rewrite page_frac_to_free_fac.
    iDestruct "Hres" as "(Hresp & Hres1)".
    iDestruct "Hbs" as "(Hbsp & Hbs1)".
    iSplitL "Hres1 Hbs1"; [by iFrame|].
    replace (S fbs - 1) with fbs by lia.
    iFrame. iPureIntro. lia.
  Qed.
   
End PAlloc. End PAlloc.
