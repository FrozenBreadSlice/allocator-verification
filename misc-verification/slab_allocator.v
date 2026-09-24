From iris.heap_lang Require Import lang proofmode notation.

Definition freelist_pop : val := λ: "fl",
  match: !"fl" with
    NONE => NONE
  | SOME "l" => "fl" <- !"l" ;; SOME "l" 
  end.

Definition freelist_push : val := λ: "fl" "l",
  "l" <- !"fl" ;; 
  "fl" <- SOME "l".

Definition new_alloc_lazy : val := λ: "n" "bs", 
  let: "al" := AllocN ("n" * "bs" + #4) NONE in 
  "al" <- NONE ;;
  "al" +ₗ #1 <- "n" ;;
  "al" +ₗ #2 <- #0 ;;
  "al" +ₗ #3 <- "bs" ;;
  "al".

Definition free : val := λ: "al" "l", freelist_push "al" "l".

Definition freelist_extend : val := rec: "rec" "fl" "lb" "bs" "n" "c" :=
  if: "c" + #1 ≤ "n"
  then freelist_push "fl" ("lb" +ₗ ("c" * "bs")) ;;
       "rec" "fl" "lb" "bs" "n" ("c" + #1)
  else #().
  
Definition extend : val := λ: "al", 
  let: "fl" := "al" in
  let: "res" := !("al" +ₗ #1) in 
  let: "cap" := !("al" +ₗ #2) in 
  let: "bs" := !("al" +ₗ #3) in
  let: "mext" := if: "cap" = #0 then #1 else "cap" in
  let: "ext" := if: "mext" ≤ "res" - "cap" then "mext" else "res" - "cap" in 
  if: "ext" = #0 then NONE 
  else 
  freelist_extend "fl" ("al" +ₗ (#4 + "cap" * "bs")) "bs" ("ext" - #1) #0 ;;
    ("al" +ₗ #2) <- ("cap" + "ext") ;;
    SOME ("al" +ₗ (#4 + ("cap" + "ext" - #1) * "bs")).

Definition alloc : val := λ: "al", 
  match: freelist_pop "al" with 
    NONE => extend "al" 
  | SOME "l" => SOME "l"
  end.
  
Section Hoare.
  Context `{!heapGS_gen hlc Σ}.

  Implicit Types l lbase al fl : loc.
  Implicit Types n i res cap size bs : nat.
  Implicit Types v w : val.
  
  Definition is_valid_loc l al : iProp Σ := 
    ∃ (res bs i : nat), (al +ₗ 1) ↦□ #res ∗ (al +ₗ 3) ↦□ #bs ∗ 
      ⌜l = (al +ₗ (4 + i * bs))⌝ ∗ ⌜i < res⌝.

  Global Instance is_valid_loc_presist l al : Persistent (is_valid_loc l al).
  Proof. apply _. Qed.

  Fixpoint is_freelist_rec l al size : iProp Σ := 
    ∃ bs, (al +ₗ 3) ↦□  #(S bs) ∗
    match size with 
    | O => l ↦ NONEV ∗ ([∗ list] i ∈ seq 1 bs, ∃ v, (l +ₗ i) ↦  v) ∗ is_valid_loc l al 
    | S s => ∃ l1, l ↦ SOMEV #l1 ∗ ([∗ list] i ∈ seq 1 bs, ∃ v, (l +ₗ i) ↦  v) ∗
          is_valid_loc l al ∗ is_freelist_rec l1 al s
    end.
    
  Definition is_freelist al : iProp Σ := 
    al ↦ NONEV 
      ∨
    ∃ l1 size, al ↦ SOMEV #l1 ∗ is_freelist_rec l1 al size.

  Definition is_allocator (al : loc) bs : iProp Σ := 
    ∃ (res cap : nat), ⌜res > 0⌝ ∗ ⌜cap ≤ res⌝ ∗ ⌜bs > 0⌝ ∗ (al +ₗ 1) ↦□  #res ∗ 
      (al +ₗ 2) ↦ #cap ∗ (al +ₗ 3) ↦□  #bs ∗ is_freelist al ∗  
      (al +ₗ (4 + cap * bs)) ↦∗ replicate ((res - cap) * bs) NONEV. 

  Lemma new_alloc_hoare res bs : 
    {{{ ⌜res > 0⌝ ∗ ⌜bs > 0⌝ }}} 
      new_alloc_lazy #res #bs 
    {{{ al, RET #al; is_allocator al bs }}}.
  Proof. 
    iIntros (φ) "(%Hn & %Hbs) Hphi". iUnfold new_alloc_lazy. wp_pures.
    wp_apply wp_allocN; [lia|done|]. iIntros "%al (HalN & _)". 
    assert (Heq : Z.to_nat (res * bs + 4) = S (S (S (S (res * bs))))) by lia.
    rewrite Heq. simpl. rewrite 4!array_cons.
    iDestruct "HalN" as "(Hal & Hal1 & Hal2 & Hal3 & HalN)". wp_store. wp_store.
    rewrite 3!Loc.add_assoc. wp_store. wp_store. iApply "Hphi". 
    iExists res, 0. 
    iMod (pointsto_persist with "Hal1") as "#Hal1". 
    iMod (pointsto_persist with "Hal3") as "#Hal3". iFrame "Hal Hal1 Hal2 Hal3".
    iSplitR; [by iPureIntro|]. iSplitR; [iPureIntro; lia|]. iSplitR; [by iPureIntro|]. 
    by rewrite Z.mul_0_l Nat.sub_0_r.
  Qed.

  Lemma freelist_pop_hoare al bs : 
    {{{ (al +ₗ 3) ↦□ #bs ∗ is_freelist al }}} 
      freelist_pop #al
    {{{ vret, RET vret; 
      is_freelist al ∗
      (⌜vret = NONEV⌝ 
        ∨ 
      ∃ l, ⌜vret = SOMEV #l⌝ ∗ 
        ([∗ list] i ∈ seq 0 bs, ∃ v, (l +ₗ i) ↦ v) ∗ is_valid_loc l al)
    }}}. 
  Proof.
    iIntros (φ) "(#Hal3 & [H | (%l1 & %s & Hfl & Hflr)]) Hphi"; 
    iUnfold freelist_pop; wp_load; wp_pures.
    { iApply "Hphi". iFrame. by iLeft. }
    destruct s; simpl.
    { iDestruct "Hflr" as "(%bs1 & #Hal3' & Hl1 & Hl1r & #Hl1v)". 
      wp_load. wp_store. wp_pures. iApply "Hphi". iFrame. iRight. 
      iExists l1. iFrame. iSplitR; [by iPureIntro|].
      iCombine "Hal3 Hal3'" gives %[_ Heq]. simplify_eq. simpl. iFrame "Hl1v Hl1r". 
      iExists NONEV. by rewrite Loc.add_0. }
    iDestruct "Hflr" as "(%bs1 & #Hal3' & %l & Hl1 & Hl1r & #Hl1v & Hflr)". 
    wp_load. wp_store. wp_pures. iApply "Hphi". 
    iSplitL "Hfl Hflr"; [iRight; by iFrame|]. iRight.     
    iCombine "Hal3 Hal3'" gives %[_ Heq]. simplify_eq. simpl. iFrame "Hl1v Hl1r". 
    iSplitR; [by iPureIntro|]. rewrite Loc.add_0. auto. 
  Qed.

  Lemma freelist_push_hoare l al : 
    {{{ 
      ∃ bs, (al +ₗ 3) ↦□ #(S bs) ∗
      is_freelist al ∗ (([∗ list] i ∈ seq 0 (S bs), ∃ v, (l +ₗ i) ↦ v)) ∗ 
      is_valid_loc l al 
    }}}
      freelist_push #al #l
    {{{ RET #(); is_freelist al }}}.
  Proof. 
    simpl. rewrite Loc.add_0. iIntros (φ) "(%bs&#Hal3&[H | (%l1 & %s & Hfl & Hflr)] & 
    ((%v & Hl) & Hl1bs) & Hlv) Hphi"; iUnfold freelist_push; wp_load; wp_store; 
    wp_store. { iApply "Hphi". iRight. iFrame. iExists 0. iFrame. by iFrame "Hal3". }
    iApply "Hphi". iRight. iExists l, (S s). by iFrame. 
  Qed.

  Lemma free_hoare l al bs : 
    {{{ 
      is_allocator al (S bs) ∗ (([∗ list] i ∈ seq 0 (S bs), ∃ v, (l +ₗ i) ↦ v)) ∗ 
      is_valid_loc l al 
    }}}
      free #al #l
    {{{ RET #(); is_allocator al (S bs) }}}.
  Proof.
    iIntros (φ) "((%res&%cap&%Hr&%Hcr&%Hbs&#Hal1&Hal2&#Hal3&Hfl&Hun) &Hlbs&#Hlv) Hphi".
    iUnfold free. wp_pures. iApply (freelist_push_hoare with "[Hfl Hlbs]").
    - iFrame. iFrame "Hlv Hal3".
    - iNext. iIntros "Hfl". iApply "Hphi". iFrame. auto.
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

  Lemma freelist_extend_hoare al res bs lb cap n c d : 
    d = n - c -> 
    lb = (al +ₗ (4 + cap * bs)) ->
    cap ≤ res ->
    n ≤ res - cap ->
    bs > 0 ->
    {{{ 
      (al +ₗ 1) ↦□ #res ∗ (al +ₗ 3) ↦□ #bs ∗
      is_freelist al ∗ (lb +ₗ (c * bs)) ↦∗ replicate (d * bs) NONEV 
    }}} 
      freelist_extend #al #lb #bs #n #c
    {{{ RET #(); is_freelist al }}}. 
  Proof. 
    iInduction d as [|d IH] forall (c); simpl; 
    iIntros (Hd -> Hcr Hd2 Hbs φ) "(#Hal1 & #Hal3 & Hfl & Hun) Hphi"; 
    iUnfold freelist_extend; wp_pures. 
    { case_bool_decide; [lia|]. wp_pures. by iApply "Hphi". }
    case_bool_decide; [|lia]. wp_pures. 
    rewrite replicate_add array_app length_replicate. 
    iDestruct "Hun" as "(Hun1 & Hun2)". 
    wp_apply (freelist_push_hoare with "[Hfl Hun1]").
    { iFrame "Hfl". iExists (bs - 1). assert (S (bs - 1) = bs) by lia. rewrite H0.
      iFrame "Hal3 Hal1". iSplitL "Hun1". 
      - Search "↦∗" replicate. iApply big_sepL_mono; 
        [|iApply seq_array_pointsto_eq; iApply "Hun1"]. iIntros. auto.
      - iExists (cap + c). iPureIntro. split; [|lia]. rewrite Loc.add_assoc. 
        f_equal. lia. }
    iIntros "Hfl". wp_pure. wp_pure. wp_pure. fold freelist_extend.  
    assert (Heq : (Z.of_nat c + 1)%Z = Z.of_nat (c + 1)) by lia. rewrite Heq. 
    iApply ("IH" with "[] [] [] [] [] [Hfl Hun2]"); try iPureIntro; 
    [lia|done|lia|lia|done| |]. 
    { iFrame "Hal1 Hal3 Hfl". rewrite Loc.add_assoc. 
      by rewrite Nat2Z.inj_add Z.mul_add_distr_r Z.mul_1_l. }
    iNext. iIntros. by iApply "Hphi".
  Qed. 

  Lemma extend_hoare al bs : 
    {{{ is_allocator al bs }}} 
      extend #al 
      {{{ vret, RET vret; 
        is_allocator al bs ∗ 
        ((∃ l, ⌜vret = SOMEV #l⌝ ∗ (([∗ list] i ∈ seq 0 bs, ∃ v, (l +ₗ i) ↦ v)) ∗ 
          is_valid_loc l al) 
          ∨  
        ⌜vret = NONEV⌝)
      }}}.
  Proof. 
    iIntros (φ) "(%res&%cap&%Hr&%Hcr&%Hbs&#Hal1&Hal2&#Hal3&Hfl&Hun) Hphi". 
    iUnfold extend. wp_pures. wp_load. wp_load. wp_load. wp_pures. 
    destruct (decide (cap = 0)) as [Hc | Hc]. 
    { rewrite Hc. wp_pures. case_bool_decide; [|lia]. wp_pures. 
      wp_apply ((freelist_extend_hoare al res bs (al +ₗ 4) 0 0 0 0) with "[Hfl]"); 
      try lia; [by rewrite Z.mul_0_l|rewrite array_nil; iFrame "Hal1 Hal3 Hfl"|].
      rewrite Nat.sub_0_r. destruct res; [lia|]. simpl. 
      rewrite replicate_add array_app. iDestruct "Hun" as "(Hun1 & Hun2)". 
      iIntros "Hfl". wp_store. wp_pures. iApply "Hphi". iSplitL "Hal2 Hun2 Hfl".
      { rewrite length_replicate Z.add_0_l. iFrame "Hal3 Hal1 Hfl". 
        iExists 1. iFrame "Hal2". iSplitR; [by iPureIntro|]. iSplitR; 
        [iPureIntro; lia|]. iSplitR; [by iPureIntro|]. assert (S res - 1 = res) by lia.
        by rewrite Z.mul_0_l Z.mul_1_l Loc.add_assoc H0. }
      iLeft. rewrite Z.mul_0_l !Z.add_0_r. iExists (al +ₗ 4). iSplitR; [done|].
      iSplitL.
      { iApply big_sepL_mono; [|by iApply seq_array_pointsto_eq]. iIntros. auto. }
      iFrame "Hal3 Hal1". iExists 0. rewrite Z.mul_0_l. iPureIntro. split; [done|lia]. }
    case_bool_decide; [inv H; lia|]. wp_pures. case_bool_decide.
    { wp_pures. case_bool_decide; [inv H1; lia|]. wp_pures. 
      assert (Z.of_nat (cap - 1) = (Z.of_nat cap - 1)%Z) by lia. rewrite -H2.
      (*split: (cap - 1) * bs + (res - cap - (cap - 1)) * bs)*)
      assert ((res - cap) * bs = (cap - 1) * bs + (res - cap - (cap - 1)) * bs) 
      by lia. rewrite H3 replicate_add array_app. 
      iDestruct "Hun" as "(Hun1 & Hun2)". rewrite length_replicate.
      wp_apply (freelist_extend_hoare al res bs (al +ₗ (4 + (cap * bs))) cap 
      (cap - 1) 0 (cap - 1) with "[Hfl Hun1]"); try lia; [done| |].
      { iFrame "Hal1 Hfl Hal3". by rewrite Z.mul_0_l Loc.add_0. }
      iIntros "Hfl". wp_store. wp_pures. iApply "Hphi".  
      (*split: bs of *)
      assert (res - cap - (cap - 1) = 1 + (res - cap - cap)) by lia. rewrite H4.
      rewrite Nat.mul_add_distr_r Nat.mul_1_l replicate_add array_app.
      iDestruct ("Hun2") as "(Hun1 & Hun2)". iSplitR "Hun1". 
      { rewrite -Nat2Z.inj_add. iFrame "Hal1 Hal3 Hal2 Hfl". iSplitR; [by iPureIntro|].
        iSplitR; [iPureIntro; lia|]. iSplitR; [by iPureIntro|]. 
        rewrite length_replicate !Loc.add_assoc. 
        assert ((4 + cap * bs + (((cap - 1) * bs)%nat + bs))%Z 
        = (4 + (cap + cap)%nat * bs)%Z) by lia.
        assert ((res - cap - cap) * bs = (res - (cap + cap)) * bs) by lia.
        by rewrite H5 H6. }
      iLeft. rewrite Loc.add_assoc. 
      assert ((4 + (cap + cap - 1) * bs)%Z = 
      4 + cap * bs + ((cap - 1) * bs)%nat) by lia. rewrite H5. iExists _. 
      iSplitR; [by iPureIntro|]. iSplitL. 
      { iApply big_sepL_mono; [|iApply seq_array_pointsto_eq; iApply "Hun1"].
        iIntros. iExists NONEV. 
        assert ((4 + cap * bs + ((cap - 1) * bs)%nat)%Z = 
        (4 + cap * bs + (cap - 1) * bs)%nat) by lia. by rewrite H7.  }
      iFrame "Hal1 Hal3". iExists (cap + (cap - 1)). iPureIntro.
      split; [|lia]. f_equal. lia. } 
    wp_pures. destruct (decide (res - cap = 0)) as [Hcr2 | Hcr2]. 
    { rewrite -Nat2Z.inj_sub; [|done]. rewrite Hcr2. wp_pures. 
      iApply "Hphi". iSplitL; [|by iRight].
      iFrame "Hal1 Hal3 Hal2 Hfl". iSplitR; [by iPureIntro|]. 
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. by rewrite Hcr2. }
    case_bool_decide; [inv H1; lia|]. wp_pures.
    (* split (res - cap - 1) * bs + bs  *)
    assert (res - cap = (res - cap - 1) + 1) by lia. rewrite H2. 
    rewrite Nat.mul_add_distr_r Nat.mul_1_l replicate_add array_app length_replicate. 
    iDestruct "Hun" as "(Hun1 & Hun2)". 
    iPoseProof (freelist_extend_hoare al res bs (al +ₗ (4 + cap * bs)) 
    cap (res - cap - 1) 0 (res - cap - 1)) as "H"; [lia|done|done|lia|done|]. 
    assert (Z.of_nat (res - cap - 1) = (Z.of_nat res - Z.of_nat cap - 1)%Z) by lia.
    rewrite H3. wp_apply ("H" with "[Hfl Hun1]"). 
    { rewrite Loc.add_assoc Z.mul_0_l Z.add_0_r. iFrame "Hfl Hun1 Hal1 Hal3". }
    iIntros "Hfl". wp_store. wp_pures. iApply "Hphi". 
    (* split bs of*) 
    iSplitL "Hfl Hal2". 
    { rewrite -Nat2Z.inj_sub; [|done]. rewrite -Nat2Z.inj_add. 
      iFrame "Hal1 Hal2 Hal3 Hfl". iSplitR; [by iPureIntro|]. iSplitR; 
      [iPureIntro; lia|]. iSplitR; [by iPureIntro|].
      assert (res - (cap + (res - cap)) = 0) by lia. rewrite H4 Nat.mul_0_l.
      simpl. by rewrite array_nil. }
    iLeft. rewrite !Loc.add_assoc. 
    assert ((4 + cap * bs + ((res - cap - 1) * bs)%nat)%Z 
    = (4 + (cap + (res - cap) - 1) * bs)%Z) by lia. rewrite H4. 
    iExists _. iSplitR; [by iPureIntro|]. iSplitL.
    { iApply big_sepL_mono; [|by iApply seq_array_pointsto_eq]. iIntros. auto. }
    iFrame "Hal1 Hal3". iExists (cap + (res - cap) - 1). iSplitR; [|iPureIntro; lia].
    Set Printing Coercions. rewrite -Nat2Z.inj_sub; [|lia]. rewrite -Nat2Z.inj_add.
    assert ((Z.of_nat (cap + (res - cap)) - 1)%Z 
    = (Z.of_nat (cap + (res - cap) - 1))%Z) by lia. by rewrite H5. 
  Qed.

  Lemma alloc_hoare al bs :
    {{{ is_allocator al bs }}}
      alloc #al
    {{{ vret, RET vret; 
      is_allocator al bs ∗
      ((∃ l, ⌜vret = SOMEV #l⌝ ∗ ([∗ list] i ∈ seq 0 bs, ∃ v, (l +ₗ i) ↦ v) ∗ 
        is_valid_loc l al)
        ∨ 
      ⌜vret = NONEV⌝)
    }}}.
  Proof.
    iIntros (φ) "(%res&%cap&%Hr&%Hcr&%Hbs&#Hal1&Hal2&#Hal3&Hfl&Hun) Hphi". 
    iUnfold alloc. wp_pures. 
    wp_apply (freelist_pop_hoare with "[Hfl]"); [iFrame "Hfl Hal3"|].
    iIntros (v) "(Hfl & [-> | (%l & -> & Hlbs & Hlv)])"; wp_pures.
    { wp_apply (extend_hoare with "[Hal2 Hun Hfl]"); 
      [iFrame "Hal1 Hal2 Hal3 Hfl Hun"; iPureIntro; lia|]. 
      iIntros (v) "(Hal & [(%l & -> & Hlbs & Hlv) | ->])"; iApply "Hphi"; 
      [iFrame; iLeft; iFrame; auto|iFrame; by iRight]. } 
    iApply "Hphi". iFrame. iSplitR; [iFrame "Hal1 Hal3"; iPureIntro; lia|].
    iLeft. iFrame "Hlbs". by iSplitR. 
  Qed.

End Hoare.
