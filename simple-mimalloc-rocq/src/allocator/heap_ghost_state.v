From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.
From iris.algebra Require Export auth gmultiset.

Class my_ghostG Σ := { #[local]my_ghostG_inG :: inG Σ (authR (gmultisetUR loc)) }.

Section HGS.
  Context `{!heapGS_gen hlc Σ, !my_ghostG Σ}.

  Implicit Types γ : gname.
  Implicit Types l : loc.
  Implicit Types L : gmultiset loc.
  
  Definition my_auth γ (L : gmultiset loc) : iProp Σ := 
    own γ (● L). 

  Definition my_frac γ l : iProp Σ := 
    own γ (◯  {[+ l +]}).

  Lemma my_auth_unit : 
    ⊢ |==> ∃ γ, my_auth γ ∅.
  Proof. iIntros. iApply own_alloc. by apply auth_auth_valid. Qed.
  
  Lemma my_auth_my_frac_agree γ L l : 
    my_auth γ L -∗ my_frac γ l -∗ ⌜l ∈ L⌝.
  Proof.
    iIntros "Ha Hf". 
    iPoseProof (own_valid_2 with "Ha Hf") as "%Hv".
    apply auth_both_valid in Hv as [Hv _].
    specialize (Hv 1). 
    apply gmultiset_included in Hv.
    by apply gmultiset_singleton_subseteq_l in Hv. 
  Qed.

  Lemma my_auth_my_frac_alloc γ L l : 
    my_auth γ L ==∗ my_auth γ (L ⊎ {[+ l +]}) ∗ my_frac γ l.
  Proof. 
    iIntros "Ha". iApply own_op.
    iApply (own_update with "[Ha]"); [|done].
    apply auth_update_alloc.
    remember (L ⊎ {[+ l +]}) as H.
    assert (({[+ l +]} : gmultiset loc) = ε ⊎ ({[+ l +]})) by set_solver.
    rewrite H0. rewrite HeqH.
    apply gmultiset_local_update_alloc. 
  Qed.

  Lemma my_auth_my_frac_dealloc' γ L l : 
    my_auth γ (L ⊎ {[+ l +]}) -∗ my_frac γ l ==∗ my_auth γ L.
  Proof.
    iIntros "Ha Hf". rewrite /my_auth /my_frac. 
    iCombine "Ha" "Hf" as "H".
    iApply (own_update with "H").
    apply auth_update_dealloc.
    assert (({[+ l +]} : gmultiset loc) ∖ {[+ l +]} = ε).
    { by apply gmultiset_difference_diag. }
    rewrite -H.
    assert (L = (L ⊎ {[+ l +]}) ∖ {[+ l +]}) by multiset_solver.
    remember (L ⊎ {[+ l +]}) as H'.
    rewrite H0 HeqH'.
    apply gmultiset_local_update_dealloc.
    multiset_solver.
  Qed.

  Lemma my_auth_my_frac_dealloc γ L l : 
    my_auth γ L -∗ my_frac γ l ==∗ my_auth γ (L ∖ {[+ l +]}).
  Proof.
    iIntros "Ha Hf". rewrite /my_auth /my_frac.
    iCombine "Ha" "Hf" as "H".
    iApply (own_update with "H").
    apply auth_update_dealloc.
    assert ((ε : gmultiset loc) = ({[+ l +]} ∖ {[+ l +]}))
    by multiset_solver. rewrite H.
    apply gmultiset_local_update_dealloc.
    multiset_solver.
  Qed.

  Definition is_allocator_internal γ l L : iProp Σ := 
    my_auth γ L. 

  Definition is_allocator γ l : iProp Σ := 
    ∃ L, is_allocator_internal γ l L.

  Definition is_valid_loc γ l : iProp Σ := 
    my_frac γ l.

  Lemma test γ l l' L :
    is_allocator_internal γ l L ∗ is_valid_loc γ l' ⊢ ⌜l' ∈ L⌝.
  Proof.
    iIntros "(Ha & Hf)". rewrite /is_allocator_internal /is_valid_loc.
    iApply (my_auth_my_frac_agree with "[Ha]"); done.
  Qed.
End HGS.

Global Opaque my_auth my_frac. 
