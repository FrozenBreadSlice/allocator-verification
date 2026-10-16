From AllSrc.iris_heap_lang_asm Require Import lang notation proofmode.

(* definitions *)

Definition down_align (l : loc) (a : Z) : loc := (l `quot` a * a)%Z.

Definition free_frac res := (1 / pos_to_Qp (Pos.succ (Pos.of_nat res)))%Qp.
Definition page_frac cbs res := (pos_to_Qp (Pos.of_nat (S cbs)) * free_frac res)%Qp.

(* helper lemmas *)
Section Utils.
  Context `{!heapGS_gen hlc Σ}.

  Lemma down_align_in_range l l' a : 
    (0 < l)%Z ->
    (0 < a)%Z -> 
    Z.divide a l -> 
    (l ≤ l' < l + a)%Z -> 
    down_align l' a = l.
  Proof.
    intros. unfold down_align. 
    assert (l = (l `quot` a * a))%Z as Heql.
    { destruct H1 as [x Heql]. rewrite Heql Z.quot_mul; lia. }
    remember (l `quot` a)%Z as x.
    assert (l' = a * l' `quot` a + l' `rem` a)%Z as Heql'; 
    [apply Z.quot_rem'|].
    remember (l' `quot` a)%Z as y.
    remember (l' `rem` a)%Z as r.
    rewrite Heql. rewrite Z.mul_cancel_r; [|lia].
    assert (0 ≤ r < a)%Z as Hr.
    { rewrite Heqr. apply Z.rem_bound_pos_pos; lia. }
    rewrite Heql in H2. rewrite Heql' in H2. nia.
  Qed.

  (* TODO(Ben): rename *)
  Lemma quot_helper x y : 
    (0 < x)%Z -> 
    (0 < y)%Z -> 
    (x `quot` y * y ≤ x)%Z.
  Proof.
    intros. 
    assert (x = y * x `quot` y + x `rem` y)%Z as Heqx; 
    [apply Z.quot_rem'|].
    remember (x `quot` y)%Z as z.
    remember (x `rem` y)%Z as r.
    rewrite Heqx. 
    assert (0 ≤ r)%Z as Hr.
    { rewrite Heqr. apply Z.rem_bound_pos_pos; lia. }
    lia.
  Qed.

  Lemma page_frac_own res : 
    0 < res ->
    page_frac res res = 1%Qp.
  Proof. 
    intros. rewrite /page_frac /free_frac. 
    assert (Pos.of_nat (S res) = Pos.succ (Pos.of_nat res)) by lia. 
    rewrite H0 Qp.mul_div_r. apply eq_refl. 
  Qed.

  Lemma page_frac_to_free_fac fbs res : 
    (page_frac (S fbs) res = page_frac fbs res + free_frac res)%Qp.
  Proof.
    rewrite /page_frac.
    replace (Pos.of_nat (S (S fbs))) with 
    (Pos.of_nat (S fbs) + 1)%positive by lia.
    rewrite -pos_to_Qp_add Qp.mul_add_distr_r Qp.mul_1_l. apply eq_refl.
  Qed.

  Lemma seq_array_pointsto_eq_gen l dq (n m : nat) :
      ([∗ list] i ∈ seq m n, ∃ v, (l + (i : nat))%Z ↦{dq} v) ⊢
      ∃ vs, ⌜length vs = n⌝ ∗ (l + m)%Z ↦∗{dq} vs.
    Proof.
      rewrite /array. revert l. 
      induction n as [|n' IH]=> l /=.
      { iIntros. iExists []. auto. }
      iIntros "((%v & Hl) & Hr)". 
      rewrite -fmap_S_seq big_sepL_fmap. 
      setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
      setoid_rewrite Z.add_assoc. 
      iPoseProof (IH with "Hr") as "(%vs & %Hl & Hr)".
      iExists (v::vs). iSplitR.
      { iPureIntro. simpl. lia. }
      simpl. rewrite Z.add_0_r.  setoid_rewrite Nat2Z.inj_succ. 
      setoid_rewrite <-Z.add_1_l. setoid_rewrite Z.add_assoc. 
      setoid_rewrite <-Z.add_1_l. setoid_rewrite Z.add_assoc. 
      iFrame.
    Qed.

  Lemma inject_litint_nat (n m : nat) : 
      #n = #m → n = m.
  Proof. intros. inversion H. by apply Nat2Z.inj. Qed. 

  Lemma seq_array_pointsto_eq' l dq v n (m : nat) :
    (l + m)%Z ↦∗{dq} replicate n v ⊣⊢
    ([∗ list] i ∈ seq m n, (l + (i : nat))%Z ↦{dq} v).
  Proof.
    rewrite /array. revert l m. 
    induction n as [|n' IH]=> l m /=; [done|].
    f_equiv; [by rewrite Z.add_0_r|]. 
    rewrite -fmap_S_seq big_sepL_fmap. 
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
    setoid_rewrite Z.add_assoc. 
    assert (l + Z.of_nat m + 1 = (l + 1) + Z.of_nat m)%Z by lia.
    rewrite H. apply IH.
  Qed.

  Lemma seq_array_pointsto_eq l dq v n :
    l ↦∗{dq} replicate n v ⊣⊢
    ([∗ list] i ∈ seq 0 n, (l + (i : nat))%Z ↦{dq} v).
  Proof.
    rewrite /array. revert l. 
    induction n as [|n' IH]=> l /=; [done|].
    f_equiv. rewrite -fmap_S_seq big_sepL_fmap. 
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
    setoid_rewrite Z.add_assoc. apply IH.
  Qed.

End Utils.
