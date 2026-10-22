From AllSrc.iris_heap_lang_asm Require Import lang notation proofmode.

(* definitions *)
Definition down_align (l : loc) (a : Z) : loc := (l `quot` a * a)%Z.

(* TODO(Ben): support for nat -> Qp *)
Definition free_frac res : Qp := 1 / pos_to_Qp (Pos.succ (Pos.of_nat res)).
Definition page_frac fbs res : Qp := pos_to_Qp (Pos.of_nat (S fbs)) * free_frac res.

Section Utils.
  Context `{!heapGS_gen hlc Σ}.

  (* alignment helper *)
  Lemma down_align_in_range l l' a : 
    (0 < l)%Z →
    (0 < a)%Z → 
    Z.divide a l → 
    (l ≤ l' < l + a)%Z → 
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

  Lemma quot_mult_bound x y : 
    (0 < x)%Z → 
    (0 < y)%Z → 
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

  (* fractional helpers *)
  Lemma page_frac_own res : 
    0 < res → 
    page_frac res res = 1%Qp.
  Proof. 
    intros. rewrite /page_frac /free_frac. 
    assert (Pos.of_nat (S res) = Pos.succ (Pos.of_nat res)) by lia. 
    rewrite H0 Qp.mul_div_r. apply eq_refl. 
  Qed.

  Lemma page_frac_to_free_frac fbs res : 
    (page_frac (S fbs) res = page_frac fbs res + free_frac res)%Qp.
  Proof.
    rewrite /page_frac.
    replace (Pos.of_nat (S (S fbs))) with 
    (Pos.of_nat (S fbs) + 1)%positive by lia.
    rewrite -pos_to_Qp_add Qp.mul_add_distr_r Qp.mul_1_l. apply eq_refl.
  Qed.
  
  Lemma page_frac_split (a b : nat) res : 
    (page_frac (a + S b) res = page_frac a res + page_frac b res)%Qp.
  Proof.
    rewrite /page_frac.
    replace (Pos.of_nat (S (a + S b))) 
    with (Pos.of_nat (S a) + Pos.of_nat (S b))%positive by lia.
    by rewrite -pos_to_Qp_add Qp.mul_add_distr_r. 
  Qed.

  (* array and big_sepL helpers *) 
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
  
  Lemma big_sepL_get_middle (Q : loc → iProp Σ) (ls ls' : list loc) l : 
    ([∗ list] y ∈ ls ++ [l] ++ ls', Q y) ⊣⊢ 
    Q l ∗ [∗ list] y ∈ ls ++ ls', Q y.
  Proof.
    induction ls as [|l' ls IH]=> /=; [done|].
    rewrite bi.sep_assoc (bi.sep_comm (Q l) (Q l')) -bi.sep_assoc.
    f_equiv. apply IH. 
  Qed.

  (* NoDup helpers *)
  Lemma NoDup_snoc {A : Type} (x : A) (L : list A) : 
    NoDup (L ++ [x]) → x ∉ L ∧ NoDup L.
  Proof.
    induction L; simpl; intros.
    { split; [apply not_elem_of_nil|by apply NoDup_nil]. }
    apply NoDup_cons in H as [H1 H2].
    specialize (IHL H2) as [H3 H4]. 
    apply not_elem_of_app in H1 as [H1 H5].
    split; [|by apply NoDup_cons].
    apply not_elem_of_cons. split; [|done]. 
    by apply not_elem_of_cons in H5 as [H5 _].
  Qed.
  
  Lemma NoDup_cons_middle {A : Type} (a : A) (L1 L2 : list A) :  
    NoDup (L1 ++ a :: L2) → a ∉ (L1 ++ L2).
  Proof.
    induction L1; simpl; intros; [by apply NoDup_cons_1_1|].
    intros. specialize (NoDup_cons_1_1 _ _ H) as H'. 
    apply NoDup_cons_1_2 in H. specialize (IHL1 H).
    apply not_elem_of_app in H' as [_ H']. simpl in *. 
    apply not_elem_of_cons in H' as [H' _].
    apply not_elem_of_cons. split; [|done]. by apply not_eq_sym.
  Qed.

  (* misc helpers *)
  Lemma inject_litint_nat (n m : nat) : 
    #n = #m → n = m.
  Proof. intros. inversion H. by apply Nat2Z.inj. Qed. 

End Utils.
