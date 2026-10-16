From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.
From AllSrc.allocator Require Import page_allocator. 
Import PAlloc.
From AllSrc.iris_heap_lang_asm.lib Require Import unwrap.

Section Test.
  Context `{!heapGS_gen hlc Σ}.

  Local Definition test_program : val := λ: "_", 
    let: "res" := #4%nat in 
    let: "bs" := #2%nat in 
    let: "align" := #1%nat in
    let: "al" := page_new_alloc "res" "bs" "align" in
    let: "l1" := unwrap (page_alloc "al") in
    let: "l2" := unwrap (page_alloc "al") in
    "l1" <- #1 ;;
    ("l1" + #1) <- #2 ;;
    "l2" <- #3 ;; 
    ("l2" + #1) <- #4 ;;
    page_free "al" "l1" ;;
    page_free "al" "l2" ;;
    page_dealloc "al".
  
  Local Lemma test_progam_hoare :
    {{{ emp }}} 
      test_program #() 
    {{{ RET #(); emp }}}.
  Proof. 
    iIntros (φ) "_ Hphi". iUnfold test_program.
    wp_pures. wp_apply (page_new_alloc_hoare); [iPureIntro; lia|].
    iIntros (al) "(Hp & _ & _)". wp_pures.
    wp_apply (page_alloc_hoare with "Hp"). 
    iIntros (v) "[(%l & -> & Hun & Hv & Hp)|(_ & %H & _)]"; [|lia].
    wp_lam. wp_pures. (*TODO(Ben): why can i not apply unwrap_spec?*)
    wp_apply (page_alloc_hoare with "Hp").
    iIntros (v) "[(%l' & -> & Hun' & Hv' & Hp)|(_ & %H & _)]"; [|lia].
    wp_lam. wp_pures. simpl.
    iDestruct "Hun" as "((%v0 & Hl0) & (%v1 & Hl1) & _)".
    iDestruct "Hun'" as "((%v2 & Hl2) & (%v3 & Hl3) & _)".
    rewrite 2!Z.add_0_r.
    wp_store. wp_store. wp_store. wp_store. 
    wp_apply (page_free_hoare with "[Hp Hl0 Hl1 Hv]"). 
    { iFrame. simpl. rewrite Z.add_0_r. iFrame. }
    iIntros "Hp". wp_pures.
    wp_apply (page_free_hoare with "[Hp Hl2 Hl3 Hv']"). 
    { iFrame. simpl. rewrite Z.add_0_r. iFrame. }
    iIntros "Hp". wp_pures.
    by wp_apply (page_dealloc_hoare with "Hp"). 
  Qed.

End Test.
