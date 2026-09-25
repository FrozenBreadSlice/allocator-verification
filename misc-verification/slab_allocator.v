From iris.heap_lang Require Import lang proofmode notation.

Definition freelist_pop : val := λ: "fl",
  match: !"fl" with
    NONE => NONE
  | SOME "l" => "fl" <- !"l" ;; SOME "l" 
  end.

Definition freelist_push : val := λ: "fl" "l",
  "l" <- !"fl" ;; 
  "fl" <- SOME "l".

Definition new_alloc : val := λ: "n" "bs", 
  let: "al" := AllocN ("n" * "bs" + #5) NONE in 
  "al" <- NONE ;;
  "al" +ₗ #1 <- NONE ;;
  "al" +ₗ #2 <- "n" ;;
  "al" +ₗ #3 <- #0 ;;
  "al" +ₗ #4 <- "bs" ;;
  "al".

Definition free : val := λ: "al" "l", freelist_push ("al" +ₗ #1) "l".

Definition freelist_extend : val := rec: "rec" "fl" "lb" "bs" "n" "c" :=
  if: "c" + #1 ≤ "n"
  then freelist_push "fl" ("lb" +ₗ ("c" * "bs")) ;;
       "rec" "fl" "lb" "bs" "n" ("c" + #1)
  else #().
  
Definition extend : val := λ: "al", 
  let: "fl" := "al" in
  let: "res" := !("al" +ₗ #2) in 
  let: "cap" := !("al" +ₗ #3) in 
  let: "bs" := !("al" +ₗ #4) in
  let: "mext" := if: "cap" = #0 then #1 else "cap" in
  let: "ext" := if: "mext" ≤ "res" - "cap" then "mext" else "res" - "cap" in 
  if: "ext" = #0 then NONE 
  else 
  freelist_extend "fl" ("al" +ₗ (#5 + "cap" * "bs")) "bs" ("ext" - #1) #0 ;;
    ("al" +ₗ #3) <- ("cap" + "ext") ;;
    SOME ("al" +ₗ (#5 + ("cap" + "ext" - #1) * "bs")).

Definition alloc : val := λ: "al", 
  match: freelist_pop "al" with 
    NONE => 
      match: freelist_pop ("al" +ₗ #1) with 
        NONE => extend "al" 
      | SOME "l" => 
        "al" <- !("al" +ₗ #1) ;;
        "al" +ₗ #1 <- NONE ;;
        SOME "l"
        end
  | SOME "l" => SOME "l"
  end.
  
Section Hoare.
  Context `{!heapGS_gen hlc Σ}.

  Implicit Types l lbase al fl : loc.
  Implicit Types n i res cap size bs : nat.
  Implicit Types v w : val.
  
  Definition is_valid_loc l al : iProp Σ := 
    ∃ (res bs i : nat), (al +ₗ 2) ↦□ #res ∗ (al +ₗ 4) ↦□ #bs ∗ 
      ⌜l = (al +ₗ (5 + i * bs))⌝ ∗ ⌜i < res⌝.

  Global Instance is_valid_loc_presist l al : Persistent (is_valid_loc l al).
  Proof. apply _. Qed.

  Fixpoint is_freelist_rec l al size : iProp Σ := 
    ∃ bs, (al +ₗ 4) ↦□  #(S bs) ∗
    match size with 
    | O => l ↦ NONEV ∗ ([∗ list] i ∈ seq 1 bs, ∃ v, (l +ₗ i) ↦  v) ∗ is_valid_loc l al 
    | S s => ∃ l1, l ↦ SOMEV #l1 ∗ ([∗ list] i ∈ seq 1 bs, ∃ v, (l +ₗ i) ↦  v) ∗
          is_valid_loc l al ∗ is_freelist_rec l1 al s
    end.
    
  Definition is_freelist fl al (empty : bool) : iProp Σ := 
    match empty with 
    | true => fl ↦ NONEV  
    | false => ∃ l1 size, fl ↦ SOMEV #l1 ∗ is_freelist_rec l1 al size
    end. 

  Definition is_allocator al bs full: iProp Σ := 
    ∃ res cap bfl1 bfl2, 
      ⌜res > 0⌝ ∗ ⌜cap ≤ res⌝ ∗ ⌜bs > 0⌝ ∗ 
      ⌜full = true <-> res = cap ∧ (bfl1 = true) ∧ (bfl2 = true)⌝ ∗ 
      (al +ₗ 2) ↦□  #res ∗ 
      (al +ₗ 3) ↦ #cap ∗ 
      (al +ₗ 4) ↦□  #bs ∗ 
      is_freelist al al bfl1 ∗ 
      is_freelist (al +ₗ 1) al bfl2 ∗
      (al +ₗ (5 + cap * bs)) ↦∗ replicate ((res - cap) * bs) NONEV. 

  Lemma new_alloc_hoare res bs : 
    {{{ ⌜res > 0⌝ ∗ ⌜bs > 0⌝ }}} 
      new_alloc #res #bs 
    {{{ al, RET #al; is_allocator al bs false }}}.
  Proof. 
    iIntros (φ) "(%Hn & %Hbs) Hphi". iUnfold new_alloc. wp_pures.
    wp_apply wp_allocN; [lia|done|]. iIntros "%al (HalN & _)". 
    assert (Heq : Z.to_nat (res * bs + 5) = S (S (S (S (S (res * bs)))))) by lia.
    rewrite Heq. simpl. rewrite 5!array_cons.
    iDestruct "HalN" as "(Hal & Hal1 & Hal2 & Hal3 & Hal4 & HalN)". wp_store. 
    wp_store. rewrite !Loc.add_assoc. wp_store. wp_store. wp_store. iApply "Hphi". 
    iExists res, 0. 
    iMod (pointsto_persist with "Hal2") as "#Hal2". 
    iMod (pointsto_persist with "Hal4") as "#Hal4". iExists true, true. 
    iFrame "Hal Hal1 Hal2 Hal3 Hal4". iSplitR; [by iPureIntro|]. iSplitR; 
    [iPureIntro; lia|]. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro; lia|]. 
    by rewrite Z.mul_0_l Nat.sub_0_r.
  Qed.

  Lemma freelist_pop_hoare al fl bs b : 
    {{{ (al +ₗ 4) ↦□ #bs ∗ is_freelist fl al b }}} 
      freelist_pop #fl
    {{{ vret, RET vret; 
      (⌜vret = NONEV⌝ ∗ is_freelist fl al true
        ∨ 
      ∃ l b', ⌜vret = SOMEV #l⌝ ∗ 
        ([∗ list] i ∈ seq 0 bs, ∃ v, (l +ₗ i) ↦ v) ∗ 
        is_valid_loc l al ∗ is_freelist fl al b')
    }}}. 
  Proof.
    iIntros (φ) "(#Hal4 & Hfl) Hphi". 
    destruct b; [|iDestruct "Hfl" as "(%l1 & %s & Hfl & Hflr)"]; 
    iUnfold freelist_pop; wp_load; wp_pures.
    { iApply "Hphi". iFrame. by iLeft. }
    destruct s; simpl.
    { iDestruct "Hflr" as "(%bs1 & #Hal4' & Hl1 & Hl1r & #Hl1v)". 
      iCombine "Hal4 Hal4'" gives %[_ Heq]. simplify_eq.
      wp_load. wp_store. wp_pures. iApply "Hphi". iRight. iExists l1, true. iFrame. 
      iSplitR; [by iPureIntro|]. iFrame "Hl1v". iExists NONEV. by rewrite Loc.add_0. }
    iDestruct "Hflr" as "(%bs1 & #Hal4' & %l & Hl1 & Hl1r & #Hl1v & Hflr)". 
    wp_load. wp_store. wp_pures. iApply "Hphi". 
    iRight. iCombine "Hal4 Hal4'" gives %[_ Heq]. simplify_eq. simpl. 
    iFrame "Hl1v Hl1r". iExists false. iSplitR; [by iPureIntro|]. rewrite Loc.add_0. 
    iSplitL "Hl1"; [auto|]. by iFrame. 
  Qed.

  Lemma freelist_push_hoare l fl al b : 
    {{{ 
      ∃ bs, (al +ₗ 4) ↦□ #(S bs) ∗
      is_freelist fl al b ∗ (([∗ list] i ∈ seq 0 (S bs), ∃ v, (l +ₗ i) ↦ v)) ∗ 
      is_valid_loc l al 
    }}}
      freelist_push #fl #l
    {{{ RET #(); is_freelist fl al false }}}.
  Proof. 
    simpl. rewrite Loc.add_0. iIntros (φ) "(%bs&#Hal4&Hfl&((%v & Hl)&Hl1bs)&#Hlv)Hphi".
    destruct b; [|iDestruct "Hfl" as "(%l1 & %s & Hfl & Hflr)"]; iUnfold freelist_push; 
    wp_load; wp_store; wp_store. 
    { iApply "Hphi". iFrame. iExists 0. iFrame. by iFrame "Hlv Hal4". }
    iApply "Hphi". iExists l, (S s). iFrame. by iFrame "Hlv Hal4".
  Qed.

  Lemma free_hoare l al bs b : 
    {{{ 
      is_allocator al (S bs) b ∗ (([∗ list] i ∈ seq 0 (S bs), ∃ v, (l +ₗ i) ↦ v)) ∗ 
      is_valid_loc l al 
    }}}
      free #al #l
    {{{ RET #(); is_allocator al (S bs) false }}}.
  Proof.
    iIntros (φ) "((%res&%cap&%b1&%b2&%Hr&%Hcr&%Hbs&%Hf&#Hal2&Hal3&#Hal4&Hfl&Hfl2&Hun)
    &Hlbs&#Hlv)Hphi". iUnfold free. wp_pures. 
    iApply (freelist_push_hoare with "[Hfl2 Hlbs]").
    - iFrame. auto. 
    - iNext. iIntros "Hfl2". iApply "Hphi". iFrame. iFrame "Hal2 Hal4". 
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iPureIntro.  
      intuition; inversion H0.
  Qed.

  Lemma seq_array_pointsto_eq l dq v n :
    l ↦∗{dq} replicate n v ⊣⊢
    ([∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦{dq} v).
  Proof.
    iIntros. iSplit;
    rewrite /array; iInduction n as [|n' IH] forall (l); simpl; [done| |done|];
    iIntros "[$ Hl]"; rewrite -fmap_S_seq big_sepL_fmap;
    setoid_rewrite Nat2Z.inj_succ; setoid_rewrite <-Z.add_1_l;
    setoid_rewrite <-Loc.add_assoc; iApply "IH"; done.
  Qed.

  Lemma freelist_extend_hoare fl al res bs b lb cap n c d : 
    d = n - c -> 
    lb = (al +ₗ (5 + cap * bs)) ->
    cap ≤ res ->
    n ≤ res - cap ->
    bs > 0 ->
    {{{ 
      (al +ₗ 2) ↦□ #res ∗ (al +ₗ 4) ↦□ #bs ∗
      is_freelist fl al b ∗ (lb +ₗ (c * bs)) ↦∗ replicate (d * bs) NONEV 
    }}} 
      freelist_extend #fl #lb #bs #n #c
    {{{ RET #(); is_freelist fl al (b && (d =? 0)) }}}. 
  Proof. 
    iInduction d as [|d IH] forall (b c); simpl; 
    iIntros (Hd -> Hcr Hd2 Hbs φ) "(#Hal2 & #Hal4 & Hfl & Hun) Hphi"; 
    iUnfold freelist_extend; wp_pures. 
    { case_bool_decide; [lia|]. wp_pures. iApply "Hphi". by rewrite andb_true_r. }
    case_bool_decide; [|lia]. wp_pures. 
    rewrite replicate_add array_app length_replicate. 
    iDestruct "Hun" as "(Hun1 & Hun2)". 
    wp_apply (freelist_push_hoare with "[Hfl Hun1]").
    { iFrame "Hfl". iExists (bs - 1). assert (S (bs - 1) = bs) by lia. rewrite H0.
      iFrame "Hal4 Hal2". iSplitL "Hun1". 
      - Search "↦∗" replicate. iApply big_sepL_mono; 
        [|iApply seq_array_pointsto_eq; iApply "Hun1"]. iIntros. auto.
      - iExists (cap + c). iPureIntro. split; [|lia]. rewrite Loc.add_assoc. 
        f_equal. lia. }
    iIntros "Hfl". wp_pure. wp_pure. wp_pure. fold freelist_extend.  
    assert (Heq : (Z.of_nat c + 1)%Z = Z.of_nat (c + 1)) by lia. rewrite Heq. 
    iApply ("IH" with "[] [] [] [] [] [Hfl Hun2]"); try iPureIntro; 
    [lia|done|lia|lia|done| |]. 
    { iFrame "Hal2 Hal4 Hfl". rewrite Loc.add_assoc. 
      by rewrite Nat2Z.inj_add Z.mul_add_distr_r Z.mul_1_l. }
    iNext. iIntros. iApply "Hphi". by rewrite andb_false_l andb_false_r.
  Qed. 

  (*instead of is_allocator al bs as precondition 
     we have empty freelists, so that we can prove that 
     something stronger then ∃ b, is_allocator al bs b in post conditoin
     we need this to prove alloc *)
  Lemma extend_hoare al res cap bs : 
    res > 0 -> 
    cap ≤ res -> 
    bs > 0 -> 
    {{{ 
      (al +ₗ 2) ↦□  #res ∗ (al +ₗ 3) ↦ #cap ∗ (al +ₗ 4) ↦□  #bs ∗ 
      is_freelist al al true ∗ is_freelist (al +ₗ 1) al true ∗
      (al +ₗ (5 + cap * bs)) ↦∗ replicate ((res - cap) * bs) NONEV 
    }}} 
      extend #al 
    {{{ vret, RET vret; 
      ((∃ l, ⌜vret = SOMEV #l⌝ ∗ (([∗ list] i ∈ seq 0 bs, ∃ v, (l +ₗ i) ↦ v)) ∗ 
        is_valid_loc l al ∗ is_allocator al bs (res - cap =? 1))  
        ∨  
      ⌜vret = NONEV⌝ ∗ is_allocator al bs true) 
    }}}.
  Proof. 
    iIntros (Hr Hcr Hbs φ) "(#Hal2 & Hal3 & #Hal4 & Hfl & Hfl2 & Hun) Hphi". 
    iUnfold extend. wp_pures. wp_load. wp_load. wp_load. wp_pures. 
    destruct (decide (cap = 0)) as [Hc | Hc]. 
    { rewrite Hc. wp_pures. case_bool_decide; [|lia]. wp_pures. 
      wp_apply ((freelist_extend_hoare al al res bs true (al +ₗ 5) 0 0 0 0) with "[Hfl]"); 
      try lia; [by rewrite Z.mul_0_l|rewrite array_nil; iFrame "Hal2 Hal4 Hfl"|].
      rewrite Nat.sub_0_r Z.mul_0_l. destruct res; [lia|]. simpl. 
      rewrite replicate_add array_app. iDestruct "Hun" as "(Hun1 & Hun2)". 
      iIntros "Hfl". wp_store. wp_pures. iApply "Hphi". iLeft.
      rewrite length_replicate Z.add_0_l Z.add_0_r Loc.add_assoc. 
      iExists (al +ₗ 5). iSplitR; [done|]. iSplitL "Hun1".
      { iApply big_sepL_mono; [|by iApply seq_array_pointsto_eq]. iIntros. auto. }
      iSplitR. 
      { iFrame "Hal2 Hal4". iExists 0. rewrite Z.mul_0_l Z.add_0_r. iPureIntro. 
        split; [done|lia]. }
      iFrame. iFrame "Hal2 Hal4". iExists 1, true, true. rewrite Z.mul_1_l.
      replace (Z.of_nat 1) with (1%Z) by lia. replace (S res - 1) with (res) by lia. 
      iFrame "Hal3 Hfl Hfl2 Hun2". iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      rewrite Nat.eqb_eq. iPureIntro. intuition. }
    case_bool_decide; [inv H; lia|]. wp_pures. case_bool_decide.
    { wp_pures. case_bool_decide; [inv H1; lia|]. wp_pures. 
      assert (Z.of_nat (cap - 1) = (Z.of_nat cap - 1)%Z) by lia. rewrite -H2.
      (*split: (cap - 1) * bs + (res - cap - (cap - 1)) * bs)*)
      assert ((res - cap) * bs = (cap - 1) * bs + (res - cap - (cap - 1)) * bs) 
      by lia. rewrite H3 replicate_add array_app. 
      iDestruct "Hun" as "(Hun1 & Hun2)". rewrite length_replicate.
      wp_apply (freelist_extend_hoare al al res bs true (al +ₗ (5 + (cap * bs))) cap 
      (cap - 1) 0 (cap - 1) with "[Hfl Hun1]"); try lia; [done| |].
      { iFrame "Hal2 Hfl Hal4". by rewrite Z.mul_0_l Loc.add_0. }
      iIntros "Hfl". rewrite andb_true_l. wp_store. wp_pures. iApply "Hphi".  
      (*split: bs of *)
      replace (res - cap - (cap - 1)) with (1 + (res - cap - cap)) by lia. 
      rewrite Nat.mul_add_distr_r Nat.mul_1_l replicate_add array_app.
      iDestruct ("Hun2") as "(Hun1 & Hun2)". iLeft. 
      rewrite length_replicate !Loc.add_assoc. iExists _. iSplitR; [done|]. 
      iSplitL "Hun1". 
      { replace ((5 + (cap + cap - 1) * bs)%Z)  (*relies on earlier asserts*)
        with (5 + cap * bs + ((cap - 1) * bs)%nat)%Z by lia. 
        iApply big_sepL_mono; [|iApply seq_array_pointsto_eq; iApply "Hun1"].
        iIntros. iExists NONEV. 
        by replace (5 + cap * bs + ((cap - 1) * bs)%nat)
        with ((5 + cap * bs + (cap - 1) * bs)%nat) by lia. }
      iSplitR. 
      { iFrame "Hal2 Hal4". iExists (cap + cap - 1). Set Printing Coercions.
        rewrite -Nat2Z.inj_add. iSplitR; [|iPureIntro; lia]. 
        by replace (Z.of_nat (cap + cap) - 1)%Z with (Z.of_nat (cap + cap - 1)) by lia. }
      rewrite -Nat2Z.inj_add. iFrame "Hfl2 Hal2 Hal3 Hal4 Hfl". iSplitR; [done|]. 
      iSplitR; [iPureIntro; lia|]. iSplitR; [done|]. iSplitR. 
      { iPureIntro. rewrite !Nat.eqb_eq. lia. }
      assert ((5 + cap * bs + (((cap - 1) * bs)%nat + bs))%Z 
      = (5 + (cap + cap)%nat * bs)%Z) by lia.
      assert ((res - cap - cap) * bs = (res - (cap + cap)) * bs) by lia.
      by rewrite -H4 H5 Z.add_assoc.  }
    wp_pures. destruct (decide (res - cap = 0)) as [Hcr2 | Hcr2]. 
    { rewrite -Nat2Z.inj_sub; [|done]. rewrite Hcr2. wp_pures. 
      iApply "Hphi". iRight. iSplitR; [done|]. iFrame "Hal2 Hal3 Hal4 Hfl Hfl2". 
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iSplitR; 
      [by iPureIntro|]. iSplitR; [|by rewrite Hcr2]. iPureIntro. 
      intuition. lia. }
    case_bool_decide; [inv H1; lia|]. wp_pures.
    (* split (res - cap - 1) * bs + bs  *)
    assert (res - cap = (res - cap - 1) + 1) by lia. rewrite H2. 
    rewrite Nat.mul_add_distr_r Nat.mul_1_l replicate_add array_app length_replicate. 
    iDestruct "Hun" as "(Hun1 & Hun2)". 
    iPoseProof (freelist_extend_hoare al al res bs true (al +ₗ (5 + cap * bs)) 
    cap (res - cap - 1) 0 (res - cap - 1)) as "H"; [lia|done|done|lia|done|]. 
    assert (Z.of_nat (res - cap - 1) = (Z.of_nat res - Z.of_nat cap - 1)%Z) by lia.
    rewrite H3. wp_apply ("H" with "[Hfl Hun1]"). 
    { rewrite Loc.add_assoc Z.mul_0_l Z.add_0_r. iFrame "Hfl Hun1 Hal2 Hal4". }
    iIntros "Hfl". wp_store. wp_pures. iApply "Hphi". iLeft.
    rewrite !Loc.add_assoc.
    assert ((5 + cap * bs + ((res - cap - 1) * bs)%nat)%Z 
    = (5 + (cap + (res - cap) - 1) * bs)%Z) by lia. rewrite H4. 
    iExists _. iSplitR; [by iPureIntro|]. iSplitL "Hun2".
    { iApply big_sepL_mono; [|by iApply seq_array_pointsto_eq]. iIntros. auto. }
    iSplitR. iFrame "Hal2 Hal4". iExists (cap + (res - cap) - 1). iSplitR; 
    [|iPureIntro; lia]. rewrite -Nat2Z.inj_sub; [|lia]. rewrite -Nat2Z.inj_add.
    assert ((Z.of_nat (cap + (res - cap)) - 1)%Z 
    = (Z.of_nat (cap + (res - cap) - 1))%Z) by lia. by rewrite H5. 
    iFrame "Hal2 Hal4". iExists (cap + (res - cap)). rewrite -Nat2Z.inj_sub; [|done]. 
    rewrite -Nat2Z.inj_add. iFrame "Hal3 Hfl Hfl2". iSplitR; [by iPureIntro|]. 
    iSplitR; [iPureIntro; lia|]. iSplitR; [by iPureIntro|]. iSplitR.
    - iPureIntro. rewrite -H2 !Nat.eqb_eq. intuition; try lia.
    - assert (res - (cap + (res - cap)) = 0) by lia. rewrite H5 Nat.mul_0_l.
      simpl. by rewrite array_nil.
  Qed.

  Lemma alloc_hoare al bs b :
    {{{ is_allocator al bs b }}}
      alloc #al
    {{{ vret, RET vret; 
      (∃ l b', ⌜vret = SOMEV #l⌝ ∗ ([∗ list] i ∈ seq 0 bs, ∃ v, (l +ₗ i) ↦ v) ∗ 
        is_valid_loc l al ∗ is_allocator al bs b')
        ∨ 
      ⌜vret = NONEV⌝ ∗ is_allocator al bs true
    }}}.
  Proof.
    iIntros (φ) "(%res&%cap&%b1&%b2&%Hr&%Hcr&%Hbs&%Hf&#Hal2&Hal3&#Hal4&Hfl&Hfl2&Hun)Hphi".
    iUnfold alloc. wp_pures. 
    wp_apply (freelist_pop_hoare with "[Hfl]"); [iFrame "Hfl Hal4"|].
    iIntros (v) "[(-> & Hfl) | (%l & %b' & -> & Hlbs & #Hlv & Hfl)]"; wp_pures.
    { wp_apply (freelist_pop_hoare with "[Hfl2]"); [iFrame "Hfl2 Hal4"|].
      iIntros (v) "[(-> & Hfl2) | (%l & %b'' & -> & Hlbs & #Hlv & Hfl2)]"; wp_pures.
      - wp_apply ((extend_hoare al res cap bs) with "[Hal3 Hun Hfl Hfl2]"); try lia; 
        [iFrame; iFrame "Hal2 Hal4"|]. 
        iIntros (v) "[(%l & -> & Hlbs & #Hvl & Hal) | (-> & Hal)]".
        + iApply "Hphi". iLeft. iFrame "Hlbs Hal Hvl". done.
        + iApply "Hphi". iRight. auto. 
      - destruct b''; [|iDestruct "Hfl2" as "(%l1 & %s & Hal1 & Hflr)"]; wp_load; 
        wp_store; wp_store; wp_pures; iApply "Hphi"; iLeft; iFrame "Hlbs Hlv".
        + iExists (res =? cap). iSplitR; [done|]. iFrame. iExists true, true. 
          iFrame "Hal2 Hal4 Hfl Hfl2". iSplitR; [done|]. iSplitR; [done|]. 
          iSplitR; [done|]. iPureIntro. rewrite Nat.eqb_eq. tauto.
        + iExists false. iSplitR; [done|]. iFrame. iExists false, true. 
          iFrame "Hal1 Hal2 Hal4 Hfl Hflr". iSplitR; [done|]. iSplitR; [done|]. 
          iSplitR; [done|]. iPureIntro. intuition; inversion H0. }
    iApply "Hphi". iLeft. iFrame. iExists ((res =? cap) && b' && b2). 
    iFrame "Hlv Hal2 Hal4". iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. 
    iSplitR; [done|]. by rewrite !andb_true_iff Nat.eqb_eq Logic.and_assoc.
  Qed.
 
End Hoare.
