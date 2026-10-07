From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.

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
  Implicit Types n i res cap size bs : nat.
  Implicit Types in_full full : bool.
  Implicit Types v w : val.

  (* field offsets *)
  Definition f_list : nat := 0.
  Definition f_next : nat := 0.
  Definition f_prev : nat := 1.
  Definition f_in_full : nat := 2.
  Definition f_heap : nat := 3.
  Definition f_cap : nat := 4.
  Definition f_res : nat := 5.
  Definition f_bs : nat := 6.
  Definition f_align : nat := 7.
  Definition f_free : nat := 8.
  Definition f_free_local : nat := 9.

  Definition MDSIZE : nat := 10. 

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


  (* TODO(Ben): 
    in c implementaiton 
    paramaters: the memory, block size, segment index, heap and res/size 
     (global) 
    now we allocate our selves which is fine
  *)
  Definition page_new_alloc : val := λ: "heap" "res" "bs" "a", 
    let: "al" := AllocN (#MDSIZE + "res" * "bs") "a" NONE in 
    "al" + #f_heap <- "heap" ;;
    "al" + #f_in_full <- #false ;;
    "al" + #f_cap <- #0 ;;
    "al" + #f_res <- "res" ;;
    "al" + #f_bs <- "bs" ;;
    "al" + #f_align <- "a" ;;
    "al" + #f_free <- NONE ;;
    "al" + #f_free_local <- NONE ;;
    "al".

  (* TODO(Ben): should not have al as paramater! *)
  Definition page_free : val := λ: "al" "l", 
    freelist_push ("al" + #f_free_local) "l".

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
  
  Definition is_valid_loc l al : iProp Σ := 
    ∃ ld res bs i, (al + f_res)%Z ↦□ #res ∗ (al + f_bs)%Z ↦□ #bs ∗ 
      ⌜ld = (al + MDSIZE)%Z⌝ ∗ ⌜l = (ld + (i * bs))%Z⌝ ∗ ⌜i < res⌝.

  Global Instance is_valid_loc_presist l al : Persistent (is_valid_loc l al).
  Proof. apply _. Qed.

  Fixpoint is_freelist_rec l al size : iProp Σ := 
    ∃ bs, (al + f_bs)%Z ↦□  #(S bs) ∗
    match size with 
    | O => l ↦ NONEV ∗ ([∗ list] i ∈ seq 1 bs, ∃ v, (l + i)%Z ↦  v) ∗ 
           is_valid_loc l al
    | S s => ∃ l1, l ↦ SOMEV #l1 ∗ ([∗ list] i ∈ seq 1 bs, ∃ v, (l + i)%Z ↦  v) ∗
           is_valid_loc l al ∗ is_freelist_rec l1 al s
    end.
    
  Definition is_freelist fl al empty : iProp Σ := 
    match empty with 
    | true => fl ↦ NONEV  
    | false => ∃ l1 size, fl ↦ SOMEV #l1 ∗ is_freelist_rec l1 al size
    end. 

  Definition is_page al bs full : iProp Σ := 
    ∃ res cap a ld emp1 emp2 , 
      ⌜(0 < al)%Z⌝ ∗  ⌜0 < res⌝ ∗ ⌜0 < bs⌝ ∗ ⌜0 < a⌝ ∗ ⌜cap ≤ res⌝ ∗
      ⌜Z.divide a al⌝ ∗ ⌜ld = (al + MDSIZE)%Z⌝ ∗
      ⌜full = true <-> res = cap ∧ (emp1 = true) ∧ (emp2 = true)⌝ ∗ 
      (*(al + f_in_full)%Z ↦ #in_full ∗ managed by heap just like intrusive lists*)
      (*(al + f_heap)%Z ↦□ #lh ∗ heap can manage this makes it more modular *)
      (al + f_cap)%Z ↦ #cap ∗ 
      (al + f_res)%Z ↦□  #res ∗ 
      (al + f_bs)%Z ↦□  #bs ∗ 
      (al + f_align)%Z ↦□ #a ∗
      is_freelist (al + f_free)%Z al emp1 ∗ 
      is_freelist (al + f_free_local)%Z al emp2 ∗
      (ld + cap * bs)%Z ↦∗ replicate ((res - cap) * bs) NONEV. 

  (*
     Hoare tripples and Proofs
  *)

  Lemma page_new_alloc_hoare lh res bs a : 
    {{{ ⌜0 < res⌝ ∗ ⌜0 < bs⌝ ∗ ⌜0 < a⌝ }}} 
      page_new_alloc #lh #res #bs #a 
    {{{ al, RET #al; 
        is_page al bs false ∗ 
        (al + f_next)%Z ↦ NONEV ∗ (al + f_prev)%Z ↦ NONEV ∗ 
        (al + f_in_full)%Z ↦ #false ∗ (al + f_heap)%Z ↦ #lh ∗
        (al + f_res)%Z ↦□ #res ∗ 
        (al + f_bs)%Z ↦□ #bs ∗ 
        (al + f_align)%Z ↦□ #a
    }}}.
  Proof. 
    iIntros (φ) "(%Hn & %Hbs & %Ha) Hphi". iUnfold page_new_alloc. 
    wp_pures. wp_apply wp_allocN; [lia|lia|done|]. 
    iIntros "%al (Hl & Ha & HalN & _)". 
    unfold MDSIZE. replace (Z.to_nat (10%nat + res * bs)) 
    with (S (S (S (S (S (S (S (S (S (S (res * bs))))))))))) by lia. simpl. 
    rewrite !array_cons. rewrite <- !Z.add_assoc. 
    iDestruct "HalN" as "(Hal & Hal1 & Hal2 & Hal3 & Hal4 & Hal5 & Hal6 & Hal7 & 
    Hal8 & Hal9 & HalN)". wp_store. wp_store. wp_store. wp_store. wp_store. 
    wp_store. wp_store. wp_store.
    iApply "Hphi". rewrite Z.add_0_r. iFrame "Hal Hal1 Ha". 
    iMod (pointsto_persist with "Hal5") as "#Hal5". 
    iMod (pointsto_persist with "Hal6") as "#Hal6". 
    iMod (pointsto_persist with "Hal7") as "#Hal7". 
    iFrame "Hal3 Hal2 Hal5 Hal6 Hal7 Hl". iExists 0, (al + MDSIZE)%Z, true, true.
    iFrame. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
    iSplitR; [iPureIntro; lia|]. iSplitR; [done|]. iSplitR; [iPureIntro; lia|]. 
    by rewrite /MDSIZE Z.mul_0_l Nat.sub_0_r Z.add_assoc Z.add_0_r.
  Qed.

  Local Lemma freelist_pop_hoare al fl bs b : 
    {{{ (al + f_bs)%Z ↦□ #bs ∗ is_freelist fl al b }}} 
      freelist_pop #fl
    {{{ vret, RET vret; 
      (⌜vret = NONEV⌝ ∗ is_freelist fl al true
        ∨ 
      ∃ l b', ⌜vret = SOMEV #l⌝ ∗ 
        ([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v) ∗ 
        is_valid_loc l al ∗ is_freelist fl al b')
    }}}. 
  Proof.
    iIntros (φ) "(#Hfbs & Hfl) Hphi". 
    destruct b; [|iDestruct "Hfl" as "(%l1 & %s & Hfl & Hflr)"]; 
    iUnfold freelist_pop; wp_load; wp_pures.
    { iApply "Hphi". iFrame. by iLeft. } 
    destruct s; simpl.
    { iDestruct "Hflr" as "(%bs1 & #Hfbs' & Hl1 & Hl1r & #Hl1v)".
      simplify_eq. wp_load. wp_store. wp_pures. iApply "Hphi". 
      iCombine "Hfbs Hfbs'" gives %[_ Heq]. 
      simplify_eq. iRight. iExists l1, true. iFrame. iSplitR; [by iPureIntro|]. 
      iFrame "Hl1v". iExists NONEV. by rewrite Z.add_0_r. }
    iDestruct "Hflr" as "(%bs1 & #Hfbs' & %l & Hl1 & Hl1r & #Hl1v & Hflr)". 
    simplify_eq. wp_load. wp_store. wp_pures. iApply "Hphi". iRight. 
    iCombine "Hfbs Hfbs'" gives %[_ Heq]. simplify_eq. simpl. 
    iFrame "Hl1v Hl1r". iExists false. iSplitR; [by iPureIntro|]. 
    rewrite Z.add_0_r. iSplitL "Hl1"; [auto|]. by iFrame. 
  Qed.

  Local Lemma freelist_push_hoare l fl al b bs : 
    {{{ 
      ⌜bs > 0⌝  ∗ (al + f_bs)%Z ↦□ #bs ∗
      is_freelist fl al b ∗ (([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v)) ∗ 
      is_valid_loc l al 
    }}}
      freelist_push #fl #l
    {{{ RET #(); is_freelist fl al false }}}.
  Proof. 
    simpl. iIntros (φ) "(%Hbs & #Hal4 & Hfl & Hun & #Hlv) Hphi".
    destruct bs; [lia|]. iDestruct "Hun" as "((%v & Hl) & Hl1bs)".
    destruct b; [|iDestruct "Hfl" as "(%l1 & %s & Hfl & Hflr)"]; 
    iUnfold freelist_push; wp_load; rewrite Z.add_0_r; wp_store; wp_store; 
    iApply "Hphi". 
    { iFrame. iExists 0. iFrame. iFrame "Hlv Hal4". auto. }
    iExists l, (S s). iFrame. iFrame "Hlv Hal4". auto.
  Qed.

  Lemma page_free_hoare l al bs b : 
    {{{ 
      is_page al bs b ∗ (([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v)) ∗ 
      is_valid_loc l al 
    }}}
      page_free #al #l
    {{{ RET #(); is_page al bs false }}}.
  Proof.
    iIntros (φ) "((%res & %cap & %a & %ld & %b1 & %b2 & %Hal & %Hr & %Hbs & %Ha 
    & %Hcr & %Haal & -> & %Hf & Hcap & #Hres & #Hbs & #Ha & Hfl & Hfl2 & Hun) 
    & Hlbs & #Hlv) Hphi". 
    iUnfold page_free. wp_pures. 
    iApply (freelist_push_hoare with "[Hfl2 Hlbs]"); [iFrame; auto|].
    iNext. iIntros "Hfl2". iApply "Hphi". 
    iFrame. iFrame "Hres Hbs Ha". iSplitR; [done|]. iSplitR; [done|]. 
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
    iSplitR; [done|]. iPureIntro.  
    intuition; inversion H0.
  Qed.

  Local Lemma seq_array_pointsto_eq l dq v n :
    l ↦∗{dq} replicate n v ⊣⊢
    ([∗ list] i ∈ seq 0 n, (l + (i : nat))%Z ↦{dq} v).
  Proof.
    rewrite /array. revert l. 
    induction n as [|n' IH]=> l /=; [done|].
    f_equiv. rewrite -fmap_S_seq big_sepL_fmap. 
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
    setoid_rewrite Z.add_assoc. apply IH.
  Qed.

  Local Lemma freelist_extend_hoare fl al ld res bs b lb cap n c d : 
    d = n - c -> 
    ld = (al + MDSIZE)%Z -> 
    lb = (ld + (cap * bs))%Z ->
    cap ≤ res ->
    n ≤ res - cap ->
    bs > 0 ->
    {{{ 
      (al + f_res)%Z ↦□ #res ∗ (al + f_bs)%Z ↦□ #bs ∗
      is_freelist fl al b ∗ (lb + (c * bs))%Z ↦∗ replicate (d * bs) NONEV 
    }}} 
      freelist_extend #fl #lb #bs #n #c
    {{{ RET #(); is_freelist fl al (b && (d =? 0)) }}}. 
  Proof. 
    iInduction d as [|d IH] forall (b c); simpl; 
    iIntros (Hd -> -> Hcr Hd2 Hbs φ) "(#Hres & #Hbs & Hfl & Hun) Hphi";
    iUnfold freelist_extend; wp_pures. 
    { case_bool_decide; [lia|]. wp_pures. iApply "Hphi". by rewrite andb_true_r. }
    case_bool_decide; [|lia]. wp_pures. 
    rewrite replicate_add array_app length_replicate. 
    iDestruct "Hun" as "(Hun1 & Hun2)". 
    wp_apply (freelist_push_hoare with "[Hfl Hun1]").
    { iFrame "Hfl Hres Hbs". iSplitR; [done|]. iSplitL "Hun1". 
      - iApply big_sepL_mono; 
        [|iApply seq_array_pointsto_eq; iApply "Hun1"]. iIntros. auto.
      - iExists (al + MDSIZE)%Z, (cap + c). iPureIntro. split; 
        unfold MDSIZE; lia. }
    iIntros "Hfl". wp_pure. wp_pure. wp_pure. fold freelist_extend.  
    assert (Heq : (Z.of_nat c + 1)%Z = Z.of_nat (c + 1)) by lia. rewrite Heq. 
    iApply ("IH" with "[] [] [] [] [] [] [Hfl Hun2]"); try iPureIntro;
    [lia|done|done|done|lia|done| |].
    { iFrame "Hres Hbs Hfl". rewrite <-Z.add_assoc. 
      by rewrite Nat2Z.inj_add Z.mul_add_distr_r Z.mul_1_l !Z.add_assoc. }
    iNext. iIntros. iApply "Hphi". by rewrite andb_false_l andb_false_r.
  Qed. 

  Local Lemma page_extend_hoare al ld res cap bs a : 
    (0 < al)%Z ->
    0 < res-> 
    0 < bs -> 
    0 < a -> 
    cap ≤ res -> 
    Z.divide a al ->
    ld = (al + MDSIZE)%Z ->
    {{{ 
      (al + f_cap)%Z ↦ #cap ∗ (al + f_res)%Z ↦□  #res ∗ 
      (al + f_bs)%Z ↦□  #bs ∗ (al + f_align)%Z ↦□  #a ∗ 
      is_freelist (al + f_free)%Z al true ∗ 
      is_freelist (al + f_free_local)%Z al true ∗
      (ld + cap * bs)%Z ↦∗ replicate ((res - cap) * bs) NONEV 
    }}} 
      page_extend #al #ld 
    {{{ vret, RET vret; 
      ((∃ l, ⌜vret = SOMEV #l⌝ ∗ (([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v)) ∗ 
        is_valid_loc l al ∗ is_page al bs (res - cap =? 1))  
        ∨  
      ⌜vret = NONEV⌝ ∗ is_page al bs true) 
    }}}.
  Proof. 
    iIntros (Hal Hr Hbs Ha Hcr Haal Hld φ) "(Hcap & #Hres & #Hbs & #Ha & Hfl & 
    Hfl2 & Hun) Hphi". 
    iUnfold page_extend. wp_pures. wp_load. wp_load. wp_load. 
    wp_pures. destruct (decide (cap = 0)) as [Hc | Hc]. 
    { rewrite Hc. wp_pures. case_bool_decide; [|lia]. wp_pures. 
      rewrite Z.mul_0_l Z.add_0_r.
      wp_apply ((freelist_extend_hoare (al + f_free)%Z al ld res bs 
      true ld 0 0 0 0) with "[Hfl]"); try lia;
      [rewrite array_nil; iFrame "Hres Hbs Hfl"|]. 
      rewrite Nat.sub_0_r. destruct res; [lia|]. simpl. 
      rewrite replicate_add array_app. iDestruct "Hun" as "(Hun1 & Hun2)". 
      iIntros "Hfl". wp_store. wp_pures. iApply "Hphi". iLeft.
      rewrite length_replicate Z.add_0_l Z.sub_diag Z.mul_0_l Z.add_0_r. 
      iExists ld. iSplitR; [done|]. iSplitL "Hun1".
      { iApply big_sepL_mono; [|by iApply seq_array_pointsto_eq]. 
        iIntros. auto. }
      iSplitR. 
      { iFrame "Hres Hbs". iExists ld, 0. rewrite Z.mul_0_l Z.add_0_r. 
        iPureIntro. split; [done|]. split; [done|lia]. }
      iFrame. iFrame "Hres Hbs Ha". iExists 1, ld, true, true. 
      rewrite Z.mul_1_l. replace (Z.of_nat 1) with (1%Z) by lia. 
      replace (S res - 1) with (res) by lia. iFrame "Hcap Hfl Hfl2 Hun2". 
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
      iSplitR; [iPureIntro; lia|]. iSplitR; [done|]. iSplitR; [done|].
      rewrite Nat.eqb_eq. iPureIntro. intuition. }
    case_bool_decide; [inv H; lia|]. wp_pures. case_bool_decide.
    { wp_pures. case_bool_decide; [inv H1; lia|]. wp_pures. 
      assert (Z.of_nat (cap - 1) = (Z.of_nat cap - 1)%Z) by lia. rewrite -H2.
      (*split: (cap - 1) * bs + (res - cap - (cap - 1)) * bs)*)
      assert ((res - cap) * bs = (cap - 1) * bs + (res - cap - (cap - 1)) * bs) 
      by lia. rewrite H3 replicate_add array_app. 
      iDestruct "Hun" as "(Hun1 & Hun2)". rewrite length_replicate.
      wp_apply (freelist_extend_hoare (al + f_free)%Z al ld res bs true 
      (ld + (cap * bs))%Z cap (cap - 1) 0 (cap - 1) with "[Hfl Hun1]"); try lia.
      { iFrame "Hres Hfl Hbs". by rewrite Z.mul_0_l Z.add_0_r. }
      iIntros "Hfl". rewrite andb_true_l. wp_store. wp_pures. iApply "Hphi".  
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
      iSplitR. 
      { iFrame "Hres Hbs". iExists ld, (cap + cap - 1). 
        rewrite -Nat2Z.inj_add. iSplitR; [done|iPureIntro; lia]. }
      rewrite -Nat2Z.inj_add. iFrame "Hfl2 Hres Hbs Ha Hfl Hcap".
      iExists ld. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
      iSplitR; [done|]. iSplitR; [iPureIntro; lia|]. iSplitR; [done|]. 
      iSplitR; [done|].
      iSplitR; [iPureIntro; rewrite !Nat.eqb_eq; lia|]. 
      assert ((ld + cap * bs + (((cap - 1) * bs)%nat + bs))%Z 
      = (ld + (cap + cap)%nat * bs)%Z) by lia.
      assert ((res - cap - cap) * bs = (res - (cap + cap)) * bs) by lia.
      by rewrite -H4 H5 Z.add_assoc.  }
    wp_pures. destruct (decide (res - cap = 0)) as [Hcr2 | Hcr2]. 
    { rewrite -Nat2Z.inj_sub; [|done]. rewrite Hcr2. wp_pures. 
      iApply "Hphi". iRight. iSplitR; [done|]. 
      iFrame "Hres Hbs Hcap Ha Hfl2 Hfl". iExists ld. iSplitR; [done|].
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iSplitR; [done|]. iSplitR; [done|].
      iSplitR; [|by rewrite Hcr2]. iPureIntro. intuition. lia. }
    case_bool_decide; [inv H1; lia|]. wp_pures.
    (* split (res - cap - 1) * bs + bs  *)
    assert (res - cap = (res - cap - 1) + 1) by lia. rewrite H2. 
    rewrite Nat.mul_add_distr_r Nat.mul_1_l replicate_add array_app 
    length_replicate. iDestruct "Hun" as "(Hun1 & Hun2)". 
    iPoseProof (freelist_extend_hoare (al + f_free)%Z al ld res bs true 
    (ld + cap * bs)%Z cap (res - cap - 1) 0 (res - cap - 1)) as "H"; 
    [lia|done|done|lia|lia|done| ]. 
    replace (Z.of_nat (res - cap - 1)) with (Z.of_nat res - Z.of_nat cap - 1)%Z 
    by lia. wp_apply ("H" with "[Hfl Hun1]"). 
    (*
    assert (Z.of_nat (res - cap - 1) = (Z.of_nat res - Z.of_nat cap - 1)%Z) 
    by lia. rewrite H3. wp_apply ("H" with "[Hfl Hun1]"). *)
    { rewrite -Z.add_assoc Z.mul_0_l Z.add_0_r. iFrame "Hres Hbs Hun1 Hfl". }
    iIntros "Hfl". wp_store. wp_pures. iApply "Hphi". iLeft.
    assert ((ld + cap * bs + ((res - cap - 1) * bs)%nat)%Z 
    = (ld + (cap + (res - cap) - 1) * bs)%Z) by lia. rewrite H3. 
    iExists _. iSplitR; [done|]. iSplitL "Hun2".
    { iApply big_sepL_mono; [|by iApply seq_array_pointsto_eq]. iIntros. auto. }
    iSplitR.
    { iFrame "Hres Hbs". iExists _, (cap + (res - cap) - 1). iSplitR; [done|]. 
      iPureIntro. lia. }
    rewrite -Nat2Z.inj_sub; [|lia]. rewrite -Nat2Z.inj_add. 
    iFrame "Hres Hbs Ha Hcap Hfl2 Hfl". iExists _. iSplitR; [done|].
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
    iSplitR; [iPureIntro; lia|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR.
    { iPureIntro. rewrite -H2 !Nat.eqb_eq. intuition; try lia. }
    replace (res - (cap + (res - cap))) with 0 by lia. 
    rewrite Nat.mul_0_l. simpl. by rewrite array_nil.
  Qed.

  Lemma page_alloc_hoare al bs b :
    {{{ is_page al bs b }}}
      page_alloc #al
    {{{ vret, RET vret; 
      (∃ l b', ⌜vret = SOMEV #l⌝ ∗ 
          ([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v) ∗ 
          is_valid_loc l al ∗ is_page al bs b')
        ∨ 
      ⌜vret = NONEV⌝ ∗ is_page al bs true
    }}}.
  Proof.
    iIntros (φ) "(%res & %cap & %a & %ld & %b1 & %b2 & %Hal & %Hr & %Hbs & %Ha 
    & %Hcr & %Haal & -> & %Hf & Hcap & #Hres & #Hbs & #Ha & Hfl & Hfl2 & Hun) 
    Hphi". iUnfold page_alloc. wp_pures. 
    wp_apply (freelist_pop_hoare with "[Hfl]"); [by iFrame "Hfl Hbs"|].
    iIntros (v) "[(-> & Hfl) | (%l & %b' & -> & Hlbs & #Hlv & Hfl)]"; wp_pures.
    { wp_apply (freelist_pop_hoare with "[Hfl2]"); [by iFrame "Hfl2 Hbs"|].
      iIntros (v) "[(-> & Hfl2) | (%l & %b'' & -> & Hlbs & #Hlv & Hfl2)]"; 
      wp_pures.
      - wp_apply ((page_extend_hoare al (al + MDSIZE)%Z res cap bs a) 
        with "[Hun Hcap Hfl Hfl2]"); try (done || lia);
        [iFrame; iFrame "Hres Hbs Ha"|].
        iIntros (v) "[(%l & -> & Hlbs & #Hvl & Hal) | (-> & Hal)]".
        + iApply "Hphi". iLeft. by iFrame "Hlbs Hal Hvl". 
        + iApply "Hphi". iRight. auto. 
      - destruct b''; [|iDestruct "Hfl2" as "(%l1 & %s & Hfl2 & Hflr)"]; 
        wp_load;  wp_pures; wp_store; wp_store; wp_pures; 
        iApply "Hphi"; iLeft; iFrame "Hlbs Hlv".
        + iExists (res =? cap). iSplitR; [done|]. iFrame. 
          iExists a, true, true. iFrame "Hres Hbs Ha Hfl Hfl2". 
          iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
          iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
          iSplitR; [done|]. iPureIntro. rewrite Nat.eqb_eq. tauto.
        + iExists false. iSplitR; [done|]. iFrame. iExists a, false, true.
          iFrame "Hres Hbs Ha Hfl Hfl2 Hflr". iSplitR; [done|]. 
          iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
          iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
          iPureIntro. intuition; inversion H0. }
    iApply "Hphi". iLeft. iFrame. iExists ((res =? cap) && b' && b2). 
    iFrame "Hlv Hres Ha Hbs". iSplitR; [done|]. 
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
    by rewrite !andb_true_iff Nat.eqb_eq Logic.and_assoc.
  Qed.
 
End PAlloc. End PAlloc.
