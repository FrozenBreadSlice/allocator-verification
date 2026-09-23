From iris.heap_lang Require Import lang proofmode notation.

Definition freelist_pop : val := λ: "fl",
  match: !"fl" with
    NONE => NONE
  | SOME "l" => "fl" <- !"l" ;; SOME "l" 
  end.

Definition freelist_push : val := λ: "fl" "l",
  "l" <- !"fl" ;; 
  "fl" <- SOME "l".

(*TODO(Ben): first hide res, gets block size, store it*)
Definition new_alloc_lazy : val := λ: "n", 
  let: "lbase" := AllocN ("n" + #3) NONE in 
  "lbase" <- NONE ;;
  "lbase" +ₗ #1 <- "n" ;;
  "lbase" +ₗ #2 <- #0 ;;
  "lbase".

Definition free : val := λ: "al" "l", freelist_push "al" "l".

(*TODO(Ben): takes block size and does c * bz*)
Definition freelist_extend : val := rec: "rec" "fl" "lb" "n" "c" :=
  if: "c" + #1 ≤ "n"
  then freelist_push "fl" ("lb" +ₗ "c") ;;
       "rec" "fl" "lb" "n" ("c" + #1)
  else #().
  
(*TODO(Ben): takes block size and does (cap + ext - 1) * bz and base is + bz * cap*)
Definition extend : val := λ: "al", 
  let: "fl" := "al" in
  let: "res" := !("al" +ₗ #1) in 
  let: "cap" := !("al" +ₗ #2) in 
  let: "mext" := if: "cap" = #0 then #1 else "cap" in
  let: "ext" := if: "mext" ≤ "res" - "cap" then "mext" else "res" - "cap" in 
  if: "ext" = #0 then NONE 
  else 
    freelist_extend "fl" ("al" +ₗ (#3 + "cap")) ("ext" - #1) #0 ;;
    ("al" +ₗ #2) <- ("cap" + "ext") ;;
    SOME ("al" +ₗ (#3 + "cap" + "ext" - #1)).

Definition alloc : val := λ: "al", 
  match: freelist_pop "al" with 
    NONE => extend "al" 
  | SOME "l" => SOME "l"
  end.
  
Section Hoare.
  Context `{!heapGS_gen hlc Σ}.

  Implicit Types l lbase al fl : loc.
  Implicit Types n i res cap size : nat.
  Implicit Types v w : val.

  Definition is_valid_loc l al : iProp Σ := 
    ∃ res (i : nat), (al +ₗ 1) ↦□ #res ∗ ⌜l = (al +ₗ (3 + i))⌝ ∗ ⌜i < res⌝.

  Global Instance is_valid_loc_presist l al : Persistent (is_valid_loc l al).
  Proof. apply _. Qed.

  Fixpoint is_freelist_rec l al size : iProp Σ := 
    match size with 
    | O => l ↦ NONEV ∗ is_valid_loc l al 
    | S s => ∃ l1, l ↦ SOMEV #l1 ∗ is_valid_loc l al ∗ is_freelist_rec l1 al s
    end.
    
  Definition is_freelist l al : iProp Σ := 
    l ↦ NONEV 
      ∨
    ∃ l1 size, l ↦ SOMEV #l1 ∗ is_freelist_rec l1 al size.

  (*res now has fractional ownership and is only readable (box) 
    now we can hide it, now can also never free l +ₗ 1*)
  Definition is_allocator (al : loc) : iProp Σ := 
    ∃ res cap vs, ⌜res > 0⌝ ∗ ⌜cap ≤ res⌝ ∗ (al +ₗ 1) ↦□  #res ∗ 
      (al +ₗ 2) ↦ #cap ∗ is_freelist al al ∗  
      (al +ₗ (3 + cap)) ↦∗ vs ∗ ⌜length vs = res - cap⌝.

  Lemma new_alloc_hoare res : 
    {{{ ⌜res > 0⌝ }}} 
      new_alloc_lazy #res 
    {{{ al, RET #al; is_allocator al }}}.
  Proof. 
    iIntros (φ) "%Hn Hphi". iUnfold new_alloc_lazy. wp_pures.
    wp_apply wp_allocN; [lia|done|]. iIntros "%al (HalN & _)". 
    assert (Heq : Z.to_nat (res + 3) = S (S (S (Z.to_nat res)))) by lia.
    rewrite Heq. simpl. rewrite 3!array_cons.
    iDestruct "HalN" as "(Hal & Hal1 & Hal2 & HalN)". wp_store. wp_store. 
    rewrite 2!Loc.add_assoc. wp_store. iApply "Hphi". 
    iExists res, 0. iMod (pointsto_persist with "Hal1") as "#Hal1". iFrame.
    iSplitR; [by iPureIntro|]. iSplitR; [iPureIntro; lia|]. iSplitR; [done|].
    iPureIntro. rewrite length_replicate. lia.
  Qed.

   Lemma freelist_pop_hoare fl al : 
    {{{ is_freelist fl al }}} 
      freelist_pop #fl
    {{{ vret, RET vret; 
      is_freelist fl al ∗
      (⌜vret = NONEV⌝ 
        ∨ 
      ∃ l v, ⌜vret = SOMEV #l⌝ ∗ l ↦ v ∗ is_valid_loc l al)
    }}}. 
  Proof.
    iIntros (φ) "[Hl | (%l1 & %s & Hl & Hflr)] Hphi"; 
    iUnfold freelist_pop; wp_load; wp_pures.
    { iApply "Hphi". iFrame. by iLeft. }
    destruct s; simpl.
    { iDestruct "Hflr" as "(Hl1 & Hvl)". wp_load. wp_store. wp_pures. 
      iApply "Hphi". iFrame. iRight. by iFrame. }
    iDestruct "Hflr" as "(%l0 & Hl1 & Hl1v & Hflr)". wp_load. wp_store.
    wp_pures. iApply "Hphi". iSplitR "Hl1 Hl1v"; [iRight; by iFrame|].
    iRight. by iFrame.   
  Qed.

  Lemma freelist_push_hoare l fl al : 
    {{{ is_freelist fl al ∗ (∃ v, l ↦ v) ∗ is_valid_loc l al }}}
      freelist_push #fl #l
    {{{ RET #(); is_freelist fl al }}}.
  Proof. 
    iIntros (φ) "([Hfl|(%l1&%s&Hfl&Hisfl)]&(%v&Hl)&Hlv) Hphi"; 
    iUnfold freelist_push; wp_load; wp_store; wp_store.
    { iApply "Hphi". iRight. iFrame. iExists 0. by iFrame. }
    iApply "Hphi". iRight. iExists l, (S s). by iFrame. 
  Qed.

  (*shouldn't we have a problem here? 
     since we own a lot of locations that are valid locations 
     it is possible that l is one of those locations and then 
     we should derive a contradiciton..
     but from alloc you always get an is_valid_loc that is 
     also within cap so it should not be an issue *)
  Lemma free_hoare l al : 
    {{{ is_allocator al ∗ (∃ v, l ↦ v) ∗ is_valid_loc l al }}}
      free #al #l
    {{{ RET #(); is_allocator al }}}.
  Proof.
    iIntros (φ) "((%res&%cap&%vs&%Hr&%Hcr&Hal1&Hal2&Hfl&Hun) & (%v & Hl) & #Hlv) Hphi".
    iUnfold free. wp_pures. iApply (freelist_push_hoare with "[Hfl Hl]"); [by iFrame|].
    iNext. iIntros "Hfl". iApply "Hphi". iFrame. auto.
  Qed.

  Lemma freelist_extend_hoare fl al res lb cap n c d : 
    d = n - c -> 
    lb = (al +ₗ (3 + cap)) ->
    cap ≤ res ->
    n ≤ res - cap ->
    {{{ 
      (al +ₗ 1) ↦□ #res ∗ 
      is_freelist fl al ∗ ∃ vs, (lb +ₗ c) ↦∗ vs ∗ ⌜length vs = d⌝ 
    }}} 
      freelist_extend #fl #lb #n #c
    {{{ RET #(); is_freelist fl al }}}. 
  Proof. 
    iInduction d as [|d IH] forall (c); simpl; 
    iIntros (Hd -> Hcr Hd2 φ) "(#Hal1 & Hisfl & %vs & Hun & %Hlen) Hphi"; 
    iUnfold freelist_extend; wp_pures. 
    { case_bool_decide; [lia|]. wp_pures. by iApply "Hphi". }
    case_bool_decide; [|lia]. wp_pures. destruct vs;
    [rewrite length_nil in Hlen; lia|]. rewrite array_cons.
    iDestruct "Hun" as "(Hun1 & Hun)". 
    wp_apply (freelist_push_hoare with "[Hisfl Hun1]").
    { iFrame. iExists res, (cap + c). iFrame "Hal1". rewrite Loc.add_assoc. 
      iPureIntro. split; [|lia]. by rewrite Nat2Z.inj_add Z.add_assoc. }
    iIntros "Hisfl". wp_pure. wp_pure. wp_pure. fold freelist_extend.  
    assert (Heq : (Z.of_nat c + 1)%Z = Z.of_nat (c + 1)) by lia. rewrite Heq. 
    iApply ("IH" with "[] [] [] [] [Hisfl Hun]"); 
    try iPureIntro; [lia|done|lia|lia| |]. 
    { iFrame "Hal1". iSplitR "Hun"; [done|]. iExists vs. iSplitL; 
      [by rewrite Loc.add_assoc Nat2Z.inj_add|]. iPureIntro. simpl in Hlen. lia. }
    iNext. iIntros "Hfl". by iApply "Hphi".  
  Qed. 

  Lemma extend_hoare al : 
    {{{ is_allocator al }}} 
      extend #al 
      {{{ vret, RET vret; 
        is_allocator al ∗ 
        ((∃ l v, ⌜vret = SOMEV #l⌝ ∗ l ↦ v ∗ is_valid_loc l al) 
          ∨  
        ⌜vret = NONEV⌝)
      }}}.
  Proof. 
    iIntros (φ) "(%res&%cap&%vs&%Hr&%Hcr & #Hal1 & Hal2 & Hisfl & Hun & %Hlen) Hphi".
    iUnfold extend. wp_pures. wp_load. wp_load. wp_pures. 
    destruct (decide (cap = 0)) as [Hc | Hc]. 
    { rewrite Hc. wp_pures. case_bool_decide; [|lia]. wp_pures. 
      wp_apply ((freelist_extend_hoare al al res (al +ₗ 3) 0 0 0 0) with "[Hisfl]"); 
      try lia; [assert ((3 + Z.of_nat 0)%Z = 3) by lia; by rewrite H0| |].
      { iFrame "Hal1". iSplitL "Hisfl"; [done|]. iExists []. iSplit; 
        [by rewrite array_nil|iPureIntro; by rewrite length_nil]. }
      destruct vs; [rewrite length_nil in Hlen; lia|]. rewrite array_cons.
      iDestruct "Hun" as "(Hun1 & Hun)".
      iIntros "Hisfl". wp_store. wp_pures. iApply "Hphi". iSplitR "Hun1". 
      { iExists res, 1, vs. rewrite Loc.add_assoc. iFrame. iFrame "Hal1". 
        iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iPureIntro. 
        simpl in Hlen. lia. }
      iLeft. iExists (al +ₗ 3), v. iFrame. iSplitL; [done|]. iExists res, 0. auto. }
    case_bool_decide; [inv H; lia|]. wp_pures. case_bool_decide.
    { wp_pures. case_bool_decide; [inv H1; lia|]. wp_pures. 
      assert (Z.of_nat (cap - 1) = (Z.of_nat cap - 1)%Z) by lia. rewrite -H2.
      rewrite -(take_drop (cap - 1) vs). 
      iDestruct (array_app with "Hun") as "(Hun1 & Hun2)".
      assert (Hlt : length (take (cap - 1) vs) = cap - 1); [rewrite length_take; lia|].
      wp_apply (freelist_extend_hoare al al res (al +ₗ (3 + cap)) 
      cap (cap - 1) 0 (cap - 1) with "[Hisfl Hun1]"); try lia; [done| |].
      { iFrame "Hal1 Hisfl". rewrite Loc.add_0. iFrame. iPureIntro. by rewrite Hlt. }
      iIntros "Hisfl". wp_store. wp_pures. iApply "Hphi". rewrite Hlt. 
      rewrite -(take_drop 1 (drop (cap - 1) vs)). 
      iDestruct (array_app with "Hun2") as "(Hun1 & Hun2)". iSplitR "Hun1". 
      { iExists res, (cap + cap), (drop cap vs). rewrite Nat2Z.inj_add. 
        iFrame. iFrame "Hal1". iSplitR; [iPureIntro; lia|]. 
        iSplitR; [iPureIntro; lia|]. rewrite length_take length_drop Hlen.
        iSplitL; [|iPureIntro; rewrite length_drop; lia]. 
        assert (1 `min` (res - cap - (cap - 1)) = 1); [rewrite min_l; [done|lia]|]. 
        rewrite H3 drop_drop 2!Loc.add_assoc -Nat2Z.inj_add. 
        assert (cap - 1 + 1 = cap) by lia. by rewrite H4 Z.add_assoc. }
      iLeft. rewrite Loc.add_assoc. rewrite Nat2Z.inj_sub; [|lia].
      Search "+" "-". assert ((3 + cap + (cap - 1))%Z = (3 + cap + cap - 1)%Z) by lia. 
      rewrite H3. iExists (al +ₗ (3 + cap + cap - 1)).
      assert (length (drop (cap - 1) vs) > 0); [rewrite length_drop Hlen; lia|].
      destruct (drop (cap - 1) vs); [rewrite length_nil in H4; lia|]. simpl.
      rewrite take_0. iDestruct (array_singleton with "Hun1") as "Hun1".
      iExists v. iFrame. iSplitR; [by iPureIntro|]. iExists res, (cap + cap - 1). 
      iFrame "Hal1". iSplitL; [|iPureIntro; lia]. rewrite -Z.add_assoc. 
      assert ((3 + (cap + cap) - 1)%Z = (3 + (cap + cap - 1))%Z) by lia. 
      rewrite H5 Nat2Z.inj_sub; [|lia]. by rewrite Nat2Z.inj_add. }
    wp_pures. destruct (decide (res - cap = 0)) as [Hcr2 | Hcr2]. 
    { rewrite -Nat2Z.inj_sub; [|done]. rewrite Hcr2. wp_pures. 
      iApply "Hphi". iSplitL; [iFrame; iFrame "Hal1"; iPureIntro; lia|].
      iRight. by iPureIntro. }
    case_bool_decide; [inv H1; lia|]. wp_pures.
    iPoseProof (freelist_extend_hoare al al res (al +ₗ (3 + cap)) cap 
    (res - cap - 1) 0 (res - cap - 1)) as "H"; [lia|done|done|lia|]. 
    assert (Z.of_nat (res - cap - 1) = (Z.of_nat res - Z.of_nat cap - 1)%Z) by lia.
    rewrite H2 -(take_drop (res - cap - 1) vs). 
    iDestruct (array_app with "Hun") as "(Hun1 & Hun2)".
    wp_apply ("H" with "[Hisfl Hun1]"). 
    { iFrame "Hal1 Hisfl". iExists (take (res - cap - 1) vs). iSplitL "Hun1"; [
      by rewrite Loc.add_assoc Z.add_0_r|]. iPureIntro. rewrite length_take. lia. }
    iIntros "Hisfl". wp_store. wp_pures. iApply "Hphi".
    rewrite -(take_drop 1 (drop (res - cap - 1) vs)). 
    iDestruct (array_app with "Hun2") as "(Hun1 & Hun2)". iSplitR "Hun1". 
    { iExists res, (cap + (res - cap)),  (drop (res - cap) vs). iFrame "Hal1".
      rewrite -Nat2Z.inj_sub; [|done]. rewrite Nat2Z.inj_add. iFrame.
      iSplitR; [done|]. iSplitR; [iPureIntro; lia|]. rewrite length_take.
      iSplitL; [|iPureIntro; rewrite length_drop Hlen; lia].
      rewrite Hlen. assert ((res - cap - 1) `min` (res - cap) = res - cap - 1); 
      [rewrite min_l; [done|lia]|]. rewrite H3. rewrite length_take.
      assert (1 `min` length (drop (res - cap - 1) vs) = 1); 
      [rewrite length_drop Hlen min_l; [done|]; lia|]. rewrite H4. 
      rewrite drop_drop Nat.sub_add; [|lia]. rewrite !Loc.add_assoc. 
      assert ((Z.of_nat (res - cap - 1) + Z.of_nat 1)%Z = Z.of_nat (res - cap)) by lia.
      by rewrite H5 Z.add_assoc. }
    iLeft. rewrite length_take Hlen. 
    assert ((res - cap - 1) `min` (res - cap) = res - cap - 1); 
    [rewrite min_l; [done|lia]|]. rewrite H3. 
    assert (length (drop (res - cap - 1) vs) > 0); [rewrite length_drop Hlen; lia|].
    destruct (drop (res - cap - 1) vs); [rewrite length_nil in H4; lia|]. simpl. 
    rewrite take_0 array_singleton 2!Loc.add_assoc -Nat2Z.inj_sub; [|done].
    assert ((3 + cap + Z.of_nat (res - cap - 1))%Z = 
    (3 + cap + Z.of_nat (res - cap) - 1)%Z) by lia. 
    rewrite H5. iExists (al +ₗ (3 + cap + (res - cap)%nat - 1)), v. iSplitR; 
    [by iPureIntro|]. iFrame. iExists res, (cap + (res - cap)%nat - 1). iFrame "Hal1".
    iSplitR; [iPureIntro|iPureIntro; lia]. 
    rewrite -Z.add_assoc -Nat2Z.inj_add -Z.add_sub_assoc Nat2Z.inj_sub; [done|lia].
  Qed.

  Lemma alloc_hoare al :
    {{{ is_allocator al }}}
      alloc #al
    {{{ vret, RET vret; 
      is_allocator al ∗
      ((∃ l v, ⌜vret = SOMEV #l⌝ ∗ l ↦ v ∗ is_valid_loc l al)
        ∨ 
      ⌜vret = NONEV⌝)
    }}}.
  Proof.
    iIntros (φ) "(%res&%cap&%vs&%Hr& %Hcr & Hal1 & Hal2 & Hisfl & Hun & %Hlen) Hphi". 
    iUnfold alloc. wp_pures. wp_apply (freelist_pop_hoare with "Hisfl"). 
    iIntros (v) "(Hisfl & [->|(%l & %v' & -> & Hl & #Hlv)])".
    { wp_pures. wp_apply (extend_hoare with "[Hal1 Hal2 Hun Hisfl]"); 
      [iFrame; iPureIntro; lia|]. iIntros (v) "(Hal & [(%l & %v' & -> & Hisfl)| ->])"; 
      iApply "Hphi"; iSplitL "Hal"; try done; [iLeft; by iFrame|by iRight]. }
    wp_pures. iApply "Hphi". iSplitR "Hl"; [iFrame; iPureIntro; lia|].
    iLeft. iFrame. iSplitR; [by iPureIntro|done]. 
  Qed.

End Hoare.
