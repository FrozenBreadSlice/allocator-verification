From iris.base_logic.lib Require Import mono_nat.
From iris.program_logic Require Import total_adequacy.
From IntrusiveAllocators.iris_heap_lang_asm Require Export adequacy.
From IntrusiveAllocators.iris_heap_lang_asm Require Import proofmode notation.

Definition heap_total hlc Σ `{!heapGpreS Σ} s e σ φ m :
  (∀ `{!heapGS_gen hlc Σ},
    ⊢ inv_heap_inv -∗ £ m -∗ WP e @ s; ⊤ [{ v, ⌜φ v⌝ }]) →
  sn erased_step ([e], σ).
Proof.
  intros Hwp; eapply (twp_total _ _ _); iIntros (?) "".
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init [] σ.(used_proph_id)) as (?) "[Hp _]".
  iMod (mono_nat_own_alloc 0) as (γ) "[Hsteps _]".
  iModIntro.
  iExists
    (λ σ ns κs _, (gen_heap_interp σ.(heap) ∗
                   proph_map_interp κs σ.(used_proph_id) ∗
                   γ ↪●MN ns)%I),
    id, (λ _, True%I), _; iFrame.
  by iApply (Hwp (HeapGS _ _ _ _ _ _ _ _)).
Qed.
