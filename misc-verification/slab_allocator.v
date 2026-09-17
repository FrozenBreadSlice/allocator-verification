From iris.proofmode Require Import proofmode. 
From iris.heap_lang Require Import lang proofmode notation.

Definition new_alloc_lazy : val := λ: "n", 
  let: "lbase" := AllocN ("n" + #2) NONE in 
  "lbase" <- NONE ;;
  ("lbase" +ₗ #1) <- "n" ;;
  "lbase".

(*requires n != 0, since l + (c = 0) is always written!*)
Definition freelist_eager_init : val := rec: "rec" "n" "c" "l" := 
  if: ("c" + #2) ≤ "n" 
  then ("l" +ₗ "c") <- SOME ("l" +ₗ ("c" + #1)) ;;   
       "rec" "n" ("c" + #1) "l" 
  else ("l" +ₗ "c") <- NONE ;; #().
  
Definition new_alloc_eager : val := λ: "n",
  let: "lbase" := AllocN ("n" + #2) NONE in 
  "lbase" <- SOME ("lbase" +ₗ #2) ;;
  ("lbase" +ₗ #1) <- "n" ;;
  freelist_eager_init "n" #0 ("lbase" +ₗ #2) ;; 
  "lbase".

Definition freelist_pop : val := λ: "fl",
  match: !"fl" with
    NONE => NONE
  | SOME "l" => "fl" <- !"l" ;; SOME "l" 
  end.

Definition freelist_push : val := λ: "fl" "l",
  "l" <- !"fl" ;; 
  "fl" <- SOME "l".

Definition alloc : val := λ: "al", freelist_pop "al".

Definition free : val := λ: "al" "l", freelist_push "al" "l".
  
Section Hoare.
Context `{!heapGS_gen hlc Σ}.

Implicit Types l lbase al fl : loc.
Implicit Types n i : nat.
Implicit Types v w : val.

Definition is_valid_loc l lbase n : iProp Σ := 
  ∃ (i : nat), ⌜l = lbase +ₗ i⌝ ∗ ⌜i < n⌝. 

Fixpoint is_freelist_rec l lbase n (ls : list loc) : iProp Σ := 
  match ls with 
  | [] => l ↦ NONEV ∗ is_valid_loc l lbase n 
  | l1::ls => l ↦ SOMEV #l1 ∗ is_valid_loc l lbase n ∗ is_freelist_rec l1 lbase n ls
  end.
  
Definition is_freelist l lbase n : iProp Σ := 
  l ↦ NONEV 
    ∨ 
  ∃ l1 ls, l ↦ SOMEV #l1 ∗ is_freelist_rec l1 lbase n ls.

Definition is_allocator (l : loc) (n : nat) : iProp Σ := 
  ⌜n > 0⌝ ∗ is_freelist l (l +ₗ 2) n ∗ (l +ₗ 1) ↦ #n.

(*update proof with S n instead of n > 0*)
Lemma new_alloc_lazy_hoare l n : 
  {{{ ⌜n > 0⌝ }}} 
    new_alloc_lazy #n 
  {{{ l, RET #l; is_allocator l n }}}.
Proof. 
  iIntros (φ) "%Hn Hal". iUnfold new_alloc_lazy. wp_pures.
  wp_apply wp_allocN_seq; [lia|done|]. iIntros "%la HlaN". 
  assert (Heq : Z.to_nat (n + 2) = S (Z.to_nat n + 1)) by lia.
  rewrite Heq -cons_seq big_sepL_cons. iDestruct "HlaN" as "[[Hla HlaT] HlaN]". 
  rewrite Loc.add_0.  wp_store. 
  assert (Heq2 : Z.to_nat n + 1 = S (Z.to_nat n)) by lia. 
  rewrite Heq2 -cons_seq big_sepL_cons.
  iDestruct "HlaN" as "[[Hla1 Hla1T] HlaN]". wp_store.
  iApply "Hal". iUnfold is_allocator, is_freelist. 
  iSplitR; [done|]. iSplitR "Hla1"; [by iLeft|done]. 
Qed.

Lemma eager_init_freelist_hoare n c d l : 
  d = n - c ->   
  c ≤ n -> 
  {{{ [∗ list] i ∈ seq c (S d), ∃ v, (l +ₗ i) ↦ v }}} 
    freelist_eager_init #(S n) #c #l
  {{{ RET #(); 
    ([∗ list] (i : nat) ∈ seq c d, (l +ₗ i) ↦ SOMEV #(l +ₗ (i + 1))) ∗
    (l +ₗ n) ↦ NONEV
  }}}.
Proof.  
  iInduction d as [|d IH] forall (l c); iIntros (φ) "%Hd %Hcn Hraw Hl"; simpl.
  { iUnfold freelist_eager_init. wp_pures.
    case_bool_decide; [lia|]. wp_pures. iDestruct "Hraw" as "((%vc & Hlc) & _)".
    wp_store. iApply "Hl". assert (Heq : n = c) by lia. rewrite Heq. by iFrame. }
  iUnfold freelist_eager_init. wp_pures. case_bool_decide; [|lia].
  wp_pures. iDestruct "Hraw" as "((%vc & Hlc) & (%vc1 & Hlc1)  & Hraw)". 
  wp_store. fold freelist_eager_init. assert (Heq : d = n - (c + 1)) by lia. 
  assert (Hineq : c + 1 ≤ n) by lia. 
  iSpecialize ("IH" $! l (c + 1) Heq Hineq Hcn). wp_pure.
  rewrite Nat2Z.inj_add. iApply ("IH" with "[Hlc1 Hraw]").
  { rewrite -Nat2Z.inj_add Nat.add_1_r. iSplitL "Hlc1"; iFrame. }
  rewrite Nat.add_1_r. iNext. iIntros "Hl2". iApply "Hl". by iFrame. 
Qed.
  
Lemma eager_init_freelist_gives_freelist n l k : 
  ([∗ list] (i : nat) ∈ seq k n, 
    (l +ₗ i) ↦ SOMEV #(l +ₗ (i + 1))) ∗ (l +ₗ (k + n)) ↦ NONEV -∗ 
    is_freelist_rec (l +ₗ k) l ((S n) + k) ((λ i, l +ₗ i) <$> (seq (S k) n)).
Proof.
  iInduction n as [|n IH] forall (k l); simpl; iIntros "Hfl".
  { rewrite -Nat2Z.inj_add Nat.add_0_r. iDestruct "Hfl" as "[_ Hlk]". iFrame.
    iUnfold is_valid_loc. iExists k. iPureIntro. split; [done|lia]. }
  iDestruct "Hfl" as "((Hlk & Hfl) & Hlksn)". iSplitL "Hlk". 
  { assert (Heq : (Z.of_nat k + 1)%Z = Z.of_nat (S k)) by lia. by rewrite Heq. }
  assert (Heq : S (S (n + k)) = S (n + S k)) by lia. rewrite Heq. iSplitR. 
  { iUnfold is_valid_loc. iExists k. iPureIntro. split; [done|lia]. } 
  iApply "IH". iFrame. rewrite -!Nat2Z.inj_add Nat.add_succ_comm. iFrame.
Qed.

Lemma big_sepL_mono_sep n m (P Q : nat -> iProp Σ) : 
  ([∗ list] i ∈ seq m n, P i ∗ Q i)
  ⊢ 
  ([∗ list] i ∈ seq m n, P i).
Proof.
  iApply big_sepL_mono. iIntros (x y H) "(Hp & Hq)". iFrame.
Qed.

Lemma big_sepL_seq_shift n m c (P : nat -> iProp Σ) : 
  ([∗ list] i ∈ seq m n, P (c + i))
  ⊣⊢
  ([∗ list] i ∈ seq (m + c) n, P i).
Proof.
  iInduction n as [|n IH] forall (m c); simpl; [done|].
  iSplit; iIntros "(HP & Hrest)"; rewrite -Nat.add_succ_l; 
  rewrite Nat.add_comm; iFrame; by iApply "IH".
Qed.

Lemma new_alloc_eager_hoare l n : 
  {{{ True }}} 
    new_alloc_eager #(S n) 
  {{{ l, RET #l; is_allocator l (S n) }}}.
Proof. 
  iIntros (φ) "_ Hal". iUnfold new_alloc_eager. wp_pures.
  wp_apply wp_allocN_seq; [lia|done|]. iIntros "%la HlaN". 
  assert (Heq : Z.to_nat (S n + 2) = S (S (Z.to_nat n + 1))) by lia.
  rewrite Heq -cons_seq big_sepL_cons. iDestruct "HlaN" as "[[Hla HlaT] HlaN]". 
  rewrite Loc.add_0. wp_store. rewrite -cons_seq big_sepL_cons.
  iDestruct "HlaN" as "((Hla1 & Hla1T) & HlaN)". wp_store. wp_pure. 
  wp_apply (eager_init_freelist_hoare n 0 n (la +ₗ 2) with "[HlaN]"); try lia.
  { (*TODO(Ben): clean this subproof up!, big_sepL_mono_sep not necessary*)
    iPoseProof big_sepL_mono_sep as "HlaN2". iSpecialize ("HlaN2" with "HlaN").
    rewrite Nat2Z.id. 
    iPoseProof (big_sepL_seq_shift (S n) 0 2) as "H". rewrite Nat.add_1_r.
    iSpecialize ("H" with "HlaN2"). iApply big_sepL_mono; [|iApply "H"].
    iIntros (k y Hk) "H1". iExists NONEV. Set Printing Coercions.
    assert (Z.of_nat (2 + y) = (2 + Z.of_nat y)%Z) by lia. rewrite H. 
    rewrite Loc.add_assoc. done. }
  iIntros "HlaN". 
  iPoseProof (eager_init_freelist_gives_freelist n (la +ₗ 2) 0) as "Hfl".
  rewrite -Nat2Z.inj_add. simpl. iSpecialize ("Hfl" with "HlaN"). 
  wp_pures. iApply "Hal". iUnfold is_allocator. iSplitR; [iPureIntro; lia|].
  iUnfold is_freelist. iSplitR "Hla1"; [|done]. iRight. iExists (la +ₗ 2), 
  ((λ i, la +ₗ 2 +ₗ i) <$> seq 1 n). iSplitL "Hla"; [done|]. 
  by rewrite Loc.add_0 Nat.add_0_r. 
Qed.

Lemma freelist_pop_hoare fl lbase n : 
  {{{ is_freelist fl lbase (S n) }}} 
    freelist_pop #fl
  {{{ vret, RET vret; 
    ⌜vret = NONEV⌝ ∗ is_freelist fl lbase (S n) 
      ∨ 
    ∃ l v, ⌜vret = SOMEV #l⌝ ∗ l ↦ v ∗ is_freelist fl lbase (S n) 
  }}}. 
Proof.
  iIntros (φ) "[Hfl|(%l & %ls & Hl & Hflr)] Hisfl"; iUnfold freelist_pop; wp_load;
  wp_pures. { iApply "Hisfl". iLeft. by iFrame. } destruct ls; simpl.
  { iDestruct "Hflr" as "(H & Hivl)". wp_load. wp_store. wp_pures. 
    iApply "Hisfl". iUnfold is_freelist. iRight. by iFrame. } 
  iDestruct "Hflr" as "(H & Hivl & Hflr)". wp_load. wp_store. 
  wp_pures. iApply "Hisfl". iUnfold is_freelist. iRight. iFrame. 
  iSplitR; [done|]. iRight. by iFrame.
Qed.

Lemma alloc_hoare al n :
  {{{ is_allocator al n }}}
    alloc #al
  {{{ vret, RET vret; 
    ⌜vret = NONEV⌝ ∗ is_allocator al n 
      ∨ 
    ∃ l v, ⌜vret = SOMEV #l⌝ ∗ l ↦ v ∗ is_allocator al n
  }}}.
Proof.
  iIntros (φ) "(%Hn & [H | H] & Hal1) Hlal"; iUnfold alloc; wp_pures.
  { destruct n; [lia|].
    wp_apply ((freelist_pop_hoare al (al +ₗ 2) n) with "[H]"); [by iLeft|].
    iIntros "%v [(-> & Hisfl) | (%l & %v0 & -> & Hl & Hisfl)]"; iApply "Hlal"; 
    [iLeft; by iFrame|]. iRight. iExists l, v0. by iFrame. }
  wp_apply ((freelist_pop_hoare al (al +ₗ 2) (n - 1)) with "[H]");
  assert (Heq : S (n - 1) = n) by lia; rewrite Heq. 
  { iDestruct "H" as "(%l & %ls & Hal & Hflr)". iRight. iFrame. }
  iIntros "%v [(-> & Hisfl) | (%l & %v0 & -> & Hl & Hisfl)]"; iApply "Hlal". 
  { iLeft. by iFrame. } iRight. by iFrame.
Qed.

Lemma freelist_push_hoare fl lbase l n : 
  {{{ is_freelist fl lbase n ∗ (∃ v, l ↦ v) ∗ is_valid_loc l lbase n }}}
    freelist_push #fl #l
  {{{ RET #(); is_freelist fl lbase n }}}.
Proof. 
  iIntros (φ) "([Hfl | (%l1 & %ls & Hfl & Hflr)] & (%v & Hl) & Hvl) Hphi"; 
  iUnfold freelist_push; wp_pures; wp_load; wp_store; wp_store; iApply "Hphi"; 
  iRight; iExists l; [iExists []|iExists (l1::ls)]; by iFrame.
Qed.

Lemma free_hoare al l n : 
  {{{ is_allocator al n ∗ (∃ v, l ↦ v) ∗ is_valid_loc l (al +ₗ 2) n }}}
    free #al #l
  {{{ RET #(); is_allocator al n }}}.
Proof.
  iIntros (φ) "((%Hn & Hfl & Hal1) & Hl & Hvl) Hphi".
  iUnfold free. wp_pures. 
  iApply ((freelist_push_hoare al (al +ₗ 2) l n) with "[Hfl Hl Hvl]"); [by iFrame|].
  iNext. iIntros "Hfl". iApply "Hphi". by iFrame.
Qed.

End Hoare.
