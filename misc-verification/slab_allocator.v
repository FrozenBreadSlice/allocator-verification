From iris.proofmode Require Import proofmode. 
From iris.heap_lang Require Import lang proofmode notation.

Definition freelist_pop : val := λ: "fl",
  match: !"fl" with
    NONE => NONE
  | SOME "l" => "fl" <- !"l" ;; SOME "l" 
  end.

Definition freelist_push : val := λ: "fl" "l",
  "l" <- !"fl" ;; 
  "fl" <- SOME "l".

Definition new_alloc_lazy : val := λ: "n", 
  let: "lbase" := AllocN ("n" + #3) NONE in 
  "lbase" <- NONE ;;
  ("lbase" +ₗ #1) <- "n" ;;
  ("lbase" +ₗ #2) <- #0 ;;
  "lbase".

Definition free : val := λ: "al" "l", freelist_push "al" "l".

Definition freelist_extend : val := rec: "rec" "fl" "lb" "n" "c" :=
  if: "c" + #1 ≤ "n"
  then freelist_push "fl" ("lb" +ₗ "c") ;;
       "rec" "fl" "lb" "n" ("c" + #1)
  else #().
  
Definition extend : val := λ: "al", 
  let: "fl" := "al" in
  let: "res" := !("al" +ₗ #1) in 
  let: "cap" := !("al" +ₗ #2) in 
  let: "ext" := if: "cap" ≤ "res" - "cap" then "cap" else "res" - "cap" in 
  freelist_extend "fl" ("al" +ₗ (#3 + "cap")) "ext" #0 ;;
  ("al" +ₗ #2) <- ("cap" + "ext").

Definition alloc : val := λ: "al", 
  match: (freelist_pop "al") with 
    NONE => extend "al" ;; freelist_pop "al" 
  | SOME "l" => SOME "l"
  end.
  
Section Hoare.
Context `{!heapGS_gen hlc Σ}.

Implicit Types l lbase al fl : loc.
Implicit Types n i res cap size : nat.
Implicit Types v w : val.

(*Definition is_valid_loc l lbase n : iProp Σ := 
   ∃ (i : nat), ⌜l = lbase +ₗ i⌝ ∗ ⌜i < n⌝. *)

Definition is_valid_loc l lbase n : Prop := 
  ∃ i, l = lbase +ₗ i /\ i < n.

Fixpoint is_freelist_rec l lbase cap size : iProp Σ := 
  match size with 
  | O => l ↦ NONEV ∗ ⌜is_valid_loc l lbase cap⌝ (*is_valid_loc l lbase cap*)
  | S s => ∃ l1, l ↦ SOMEV #l1 ∗ ⌜is_valid_loc l lbase cap⌝(*is_valid_loc l lbase cap*) ∗ is_freelist_rec l1 lbase cap s
  end.
  
Definition is_freelist l lbase cap size : iProp Σ := 
  match size with 
  | 0 => l ↦ NONEV
  | S s => ∃ l1, l ↦ SOMEV #l1 ∗ is_freelist_rec l1 lbase cap s
  end.

Definition is_allocator (l : loc) (res cap size : nat) : iProp Σ := 
  ⌜res > 0⌝ ∗ 
  (*⌜cap ≤ res⌝ ∗ ⌜size ≤ cap⌝ ∗ fix proofs later with these maybe? *)
  (*also may need 'raw' resources.. given by AllocN*)
  is_freelist l (l +ₗ 3) cap size ∗ (l +ₗ 1) ↦ #res ∗ (l +ₗ 2) ↦ #cap.

Lemma new_alloc_lazy_hoare l res : 
  {{{ ⌜res > 0⌝ }}} 
    new_alloc_lazy #res 
  {{{ l, RET #l; is_allocator l res 0 0 }}}.
Proof. 
  iIntros (φ) "%Hn Hphi". iUnfold new_alloc_lazy. wp_pures.
  wp_apply wp_allocN_seq; [lia|done|]. iIntros "%la HlaN". 
  assert (Heq : Z.to_nat (res + 3) = S (S (S (Z.to_nat res)))) by lia.
  rewrite Heq -cons_seq big_sepL_cons. 
  iDestruct "HlaN" as "[[Hla HlaT] HlaN]". rewrite Loc.add_0. wp_store. 
  rewrite -cons_seq big_sepL_cons. iDestruct "HlaN" as "[[Hla1 Hla1T] HlaN]". wp_store. 
  rewrite -cons_seq big_sepL_cons. iDestruct "HlaN" as "[[Hla2 Hla2T] HlaN]". wp_store. 
  iApply "Hphi". by iFrame.
Qed.

Lemma freelist_pop_hoare fl lbase cap size : 
  {{{ is_freelist fl lbase cap size }}} 
    freelist_pop #fl
  {{{ vret, RET vret; 
    ⌜vret = NONEV⌝ ∗ is_freelist fl lbase cap size 
    (*maybe make stronger say, size = 0        ^ here*)
      ∨ 
    ∃ l v, ⌜vret = SOMEV #l⌝ ∗ l ↦ v ∗ is_freelist fl lbase cap (size - 1) 
  }}}. 
Proof.
  destruct size; simpl. 
  { iIntros (φ) "Hfl Hphi"; iUnfold freelist_pop; wp_load. wp_pures. iApply "Hphi".
    iFrame. by iLeft. }
  iIntros (φ) "(%l & Hfl & Hflr) Hphi". iUnfold freelist_pop. wp_load. wp_pures.
  destruct size; simpl.
  { iDestruct "Hflr" as "(Hl & Hvl)". wp_load. wp_store. wp_pures. iApply "Hphi".
    iFrame. iRight. by iFrame. }
  iDestruct "Hflr" as "(%l1 & Hl & Hlv & Hflr)". wp_load. wp_store. wp_pures. 
  iApply "Hphi". iFrame. iRight. by iFrame. 
Qed.

Lemma freelist_push_hoare fl lbase l cap size : 
  {{{ is_freelist fl lbase cap size ∗ (∃ v, l ↦ v) ∗ ⌜is_valid_loc l lbase cap⌝ }}}
    freelist_push #fl #l
  {{{ RET #(); is_freelist fl lbase cap (S size) }}}.
Proof. 
  destruct size; simpl.
  { iIntros (φ) "(Hfl & (%v & Hl) & Hlv) Hphi". iUnfold freelist_push. wp_pures. 
    wp_load. wp_store. wp_store. iApply "Hphi". by iFrame. }
  iUnfold freelist_push. destruct size; simpl.
  { iIntros (φ) "((%l1 & Hfl & Hflv & Hflr) & (%v & Hl) & Hlv) Hphi". wp_load.
    wp_store. wp_store. iApply "Hphi". by iFrame. }
  iIntros (φ) "((%l1 & Hfl & Hflv) & (%v & Hl) & Hlv) Hphi". wp_load.
  wp_store. wp_store. iApply "Hphi". by iFrame.
Qed.

Lemma free_hoare al l res cap size : 
  {{{ is_allocator al res cap size ∗ (∃ v, l ↦ v) ∗ ⌜is_valid_loc l (al +ₗ 3) cap⌝ }}}
    free #al #l
  {{{ RET #(); is_allocator al res cap (S size) }}}.
Proof.
  iIntros (φ) "((%Hres & Hfl & Hal1) & Hl & Hvl) Hphi".
  iUnfold free. wp_pures. 
  iApply ((freelist_push_hoare al (al +ₗ 3)) with "[Hfl Hl Hvl]"); iFrame.
  iNext. iIntros "Hfl". iApply "Hphi". by iFrame.
Qed.

Lemma is_valid_loc_range l lbase cap n c :
  c ≤ n -> 
  is_valid_loc l lbase cap -> 
  is_valid_loc (l +ₗ n) lbase cap -> 
  is_valid_loc (l +ₗ c) lbase cap.
Proof.
  intros Hc (i & -> & Hic) (j & Heq & Hjc). unfold is_valid_loc. exists (i + c).
  rewrite Loc.add_assoc in Heq. rewrite Loc.add_assoc. apply Loc.add_inj in Heq. 
  split; [by rewrite Nat2Z.inj_add|lia].
Qed.

Lemma is_valid_loc_cap l lbase cap n : 
  is_valid_loc l lbase cap -> is_valid_loc l lbase (cap + n).
Proof. 
  intros (i & -> & Hic). unfold is_valid_loc. exists i. split; [done|lia].
Qed.

Lemma is_freelist_rec_larger_cap fl lbase cap size n : 
  is_freelist_rec fl lbase cap size -∗ is_freelist_rec fl lbase (cap + n) size.
Proof.
  iInduction size as [|size IH]forall (fl); simpl; iUnfold is_freelist_rec. 
  { iIntros "($ & %H)". iPureIntro. by apply is_valid_loc_cap. }
  fold is_freelist_rec. iIntros "(%l1 & Hfl & %Hflv & Hisfl)". iFrame.
  iSplitR; [iPureIntro; by apply is_valid_loc_cap|]. by iApply "IH". 
Qed.

Lemma is_freelist_larger_cap fl lbase cap size n : 
  is_freelist fl lbase cap size -∗ is_freelist fl lbase (cap + n) size.
Proof.
  destruct size; iUnfold is_freelist; [by iIntros|]. 
  iIntros "(%l1 & Hfl & Hisflr)". iFrame. by iApply is_freelist_rec_larger_cap.
Qed.

Lemma freelist_extend_hoare fl lbase lb cap size n c d : 
  d = n - c -> 
  {{{ is_freelist fl lbase cap size ∗ 
    ⌜is_valid_loc lb lbase cap⌝ ∗ ⌜is_valid_loc (lb +ₗ (n - 1)) lbase cap⌝ ∗
      [∗ list] i ∈ seq c d, ∃ v, (lb +ₗ i) ↦ v 
  }}} 
    freelist_extend #fl #lb #n #c
  {{{ RET #(); is_freelist fl lbase (cap + d) (size + d) }}}. 
Proof. 
  iInduction d as [|d IH] forall (cap size c); simpl; 
  iIntros (Hd φ) "(Hisfl & %Hlbv & %Hlbnv & HlbCD) Hphi"; iUnfold freelist_extend. 
  { wp_pures. case_bool_decide; [lia|]. wp_pures. iApply "Hphi". 
    by rewrite !Nat.add_0_r. }
  wp_pures. case_bool_decide; [|lia]. wp_pures. 
  iDestruct "HlbCD" as "(Hlbc & HlbCD)".
  wp_apply (freelist_push_hoare with "[Hisfl Hlbc]").
  { iFrame. iPureIntro. apply (is_valid_loc_range _ _ _ (n - 1)); [lia|done|].
    assert ((Z.of_nat n - 1)%Z = Z.of_nat (n - 1)) by lia. by rewrite -H0. }
  iIntros "Hisfl". wp_pure. wp_pure. wp_pure. fold freelist_extend.  
  assert (Heq :(Z.of_nat c + 1)%Z = Z.of_nat (c + 1)) by lia. rewrite Heq. 
  iApply ("IH" with "[] [HlbCD Hisfl]"); [iPureIntro; lia| |]. 
  { iAssert (is_freelist fl lbase (cap + 1) (S size)) with "[Hisfl]" as "Hifl"; 
    [by iApply is_freelist_larger_cap|]. rewrite Nat.add_1_r. iFrame.
    iSplitR. { iPureIntro. rewrite -Nat.add_1_r. by apply is_valid_loc_cap. }
    iSplitR. { iPureIntro. rewrite -Nat.add_1_r. by apply is_valid_loc_cap. }
    by rewrite Nat.add_1_r. }
  iNext. iIntros "Hisfl". iApply "Hphi". by rewrite !Nat.add_succ_comm.
Qed.

(*TODO(Ben): probalby need things like cap <= res, size <= cap, add to is_allocator 
 then fix proofs..*)
Lemma extend_hoare_true al res cap size : 
  cap ≤ res - cap -> 
  {{{ is_allocator al res cap size }}} 
    extend #al 
  {{{ RET #(); is_allocator al res (cap + cap) (size + cap) }}}.
Proof. 
  iIntros (Hc φ) "(%Hr & Hisfl & Hal1 & Hal2) Hphi". iUnfold extend.
  wp_pures. wp_load. wp_load. wp_pures. case_bool_decide; [|lia].
  wp_pures. iPoseProof (freelist_extend_hoare al (al +ₗ 3) (al +ₗ (3 + cap)) 
  cap size cap 0 cap) as "H"; [lia|]. assert (Z.of_nat 0 = 0%Z) by lia. rewrite H0. 
  wp_apply ("H" with "[Hisfl]"). 
  { (*can't prove rn, because is_allocator forgets that it has a bunch of 
    locations that point to an aribtrary value, i guess we add that aswell*) 
    admit. }
  iIntros "Hisfl". wp_store. iApply "Hphi". iUnfold is_allocator.
  iFrame. iSplitR; [by iPureIntro|]. by rewrite Nat2Z.inj_add.
Admitted.

Lemma alloc_hoare al res cap size :
  {{{ is_allocator al res cap size }}}
    alloc #al
  {{{ vret, RET vret; 
    ⌜vret = NONEV⌝ ∗ is_allocator al res cap size 
      ∨ 
    ∃ l v, ⌜vret = SOMEV #l⌝ ∗ l ↦ v ∗ is_allocator al res cap (size - 1)
  }}}.
Proof.
  iIntros (φ) "Hal Hphi". iUnfold alloc. wp_pures. wp_apply freelist_pop_hoare. 
  { admit. } iIntros "%v H". (*works out i think*) 
Admitted.

End Hoare.
