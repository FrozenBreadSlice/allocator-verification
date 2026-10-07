From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.
From AllSrc.iris_heap_lang_asm.lib Require Export array.
From AllSrc.intrusive_list Require Export cycle_double.

Module IList.
Section IList.
  Context `{!heapGS_gen hlc Σ}.

  Implicit Types lr l pl : Z.
  
  Definition is_ilist := DCycle.pred.

  Definition pred_unique := DCycle.pred_unique.
 
  Definition new := DCycle.new. 

  Definition prev := DCycle.prev. 

  Definition next := DCycle.next. 

  Definition is_empty := DCycle.is_empty.

  Definition push_front := DCycle.insert_0.

  Definition pop_back := DCycle.remove_1.
      
  (* TODO(Ben): maybe verify a more efficient removal function *)

  (* arbitrary removal in the list
     initially ll = pl (page list head) 
     lrem = (intrusive) list entry to remove *)
  Definition remove : val := rec: "rec" "ll" "lrem" :=
    if: is_empty "ll" then NONE 
    else
      let: "ln" := next "ll" in 
      if: "ln" = "lrem" 
      then 
        let: "lrem'" := DCycle.remove_0 "ll" in 
        "lrem'" <- NONE ;;
        ("lrem'" + #1) <- NONE ;;
        SOME "lrem'"
      else "rec" "ln" "lrem".
      
  Definition push_front_hoare := DCycle.insert_0_spec.

  Definition pop_back_hoare := DCycle.remove_1_spec.

  (*should make a lemma that all locations are different in a DCycle..*)
  Lemma remove_hoare pl lr L1 L2 : 
    {{{ DCycle.pred pl (L1 ++ [lr] ++ L2) }}}
      remove #pl #lr 
    {{{ RET SOMEV #lr; 
        lr ↦∗ [NONEV; NONEV] ∗ DCycle.pred pl (L1 ++ L2 )
    }}}.
  Proof. 
    iInduction L1 as [|l L1 IH] forall (pl L2); simpl; 
    iIntros (φ) "Hpl Hphi"; iUnfold remove; wp_pures; 
    wp_apply (DCycle.is_empty_spec with "Hpl"); iIntros "Hpl";
    case_bool_decide; try inversion H; wp_pures; 
    wp_apply (DCycle.next_spec with "Hpl"); iIntros "Hpl"; wp_pures.
    { case_bool_decide; [|contradiction]. wp_pures.  
      wp_apply (DCycle.remove_0_spec with "Hpl"). 
      iIntros (v0 v1) "(Hpl & Hlr)". rewrite !array_cons array_nil. 
      iDestruct "Hlr" as "(Hlr1 & Hlr2 & _)". wp_store. wp_store. 
      wp_pures. iApply "Hphi". by iFrame. }
    iPoseProof (pred_unique with "Hpl") as "(Hpl & %Hd)".
    assert (l ≠ lr).
    { Search NoDup. apply NoDup_cons in Hd as [_ Hd].
      apply NoDup_cons in Hd as [Hd _]. 
      apply not_elem_of_app in Hd as [_ Hd]. Search (_ ∉ _ :: _).
      by apply not_elem_of_cons in Hd as [Hd _]. }
    case_bool_decide; [simplify_eq|]. 
    wp_pure. fold remove. iApply ("IH" with "[Hpl]").
    { rewrite DCycle.pred_rotate -app_assoc -app_comm_cons. auto. }
    iNext. iIntros "(Hlr & Hl)". iApply "Hphi". 
    rewrite DCycle.pred_rotate app_assoc. by iFrame. 
  Qed.

End IList.
End IList.
