From IntrusiveAllocators.iris_heap_lang_asm Require Export lang.
From IntrusiveAllocators.iris_heap_lang_asm Require Import proofmode notation.
From IntrusiveAllocators.iris_heap_lang_asm.lib Require Import assert.

(** The function [unwrap o] (unsafely) asserts that [o] is [SOMEV v],
and returns the contained value [v]. *)
Definition unwrap : val := λ: "o",
  match: "o" with
    NONE => assert: #false
  | SOME "v" => "v"
  end.

Section proof.
  Context `{!heapGS Σ}.

  Lemma unwrap_spec Φ v : ▷ Φ v ⊢ WP unwrap (SOMEV v) {{ Φ }}.
  Proof. iIntros "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.
End proof.
