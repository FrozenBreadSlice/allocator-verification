From AllSrc.iris_heap_lang_asm Require Import lang proofmode notation.
From AllSrc.allocator Require Import page_allocator.
From AllSrc.intrusive_list Require Import ilist.

(* Heap allocator

*)

Module HAlloc. Section HAlloc.
  Context `{!heapGS_gen hlc Σ}.
 
  Implicit Types al l lq lf : loc.
  Implicit Types bs i : nat.

  (* constants *)
  Definition f_queue : nat := 0.
  Definition f_full : nat := 2.

  Definition num_f : nat := 2.
  Definition queue_size : nat := 2.

  Definition PAGE_DATA_SIZE : nat := 64.
  (* TODO(Ben): more queues with block sizes later *)
  Definition BLOCK_SIZE : nat := 16. 

  (*derived*)
  Definition SEGMENT_SIZE : nat := PAlloc.HEADER_SIZE + PAGE_DATA_SIZE.
  (*smallest power of 2 containing SEGMENT_SIZE*)
  Definition SEGMENT_ALIGN : nat := 128.  
  Definition NUM_BLOCKS : nat := PAGE_DATA_SIZE / BLOCK_SIZE.

  (* 
    function definitions
  *)

  Definition heap_new_alloc : val := λ: "_", 
    let: "al" := AllocN (#num_f * #queue_size) NONE in 
    IList.new ("al" + #f_queue) ;;
    IList.new ("al" + #f_full) ;;
    "al".

  Definition heap_free : val := λ: "l", 
    let: "lmd" := ("l" `quot` #SEGMENT_ALIGN) * #SEGMENT_ALIGN in
    if: !("lmd" + #PAlloc.f_in_full) = #true 
    then 
      let: "al" := ("lmd" + #PAlloc.f_heap) in 
      let: "lp" := IList.remove ("al" + #f_full) ("lmd" + #PAlloc.f_list) in 
      IList.push_front ("al" + #f_queue) "lp" ;;
      ("lp" + #PAlloc.f_in_full) <- #false ;;
      PAlloc.page_free "lmd" "l"
    else  
      (*TODO(Ben): here we don't want to have ld..!*)
      PAlloc.page_free "lmd" "l".

  Definition queue_alloc : val := rec: "rec" "bsq" "full" := 
    if: IList.is_empty "bsq" then NONE 
    else 
      let: "lp" := IList.prev "bsq" in
      match: PAlloc.page_alloc "lp" with 
        NONE => 
          let: "lp'" := IList.pop_back "bsq" in 
          IList.push_front "full" "lp'" ;;
          ("lp'" + #PAlloc.f_in_full) <- #true ;;
          "rec" "bsq" "full" 
      | SOME "l" => SOME "l"
      end.

  Definition heap_alloc : val := λ: "al" "n", 
    if: #BLOCK_SIZE < "n" then NONE 
    else
      let: "bsq" := ("al" + #f_queue) in 
      let: "full" := ("al" + #f_full) in 
      match: queue_alloc "bsq" "full" with 
        NONE => 
          let: "lp" := PAlloc.page_new_alloc "al" #NUM_BLOCKS #BLOCK_SIZE in 
          IList.push_front "bsq" "lp" ;;
          PAlloc.page_alloc "lp"
      | SOME "l" => SOME "l"
      end.

  (* 
    Representation
  *)
  
  (*
    How do we ever define this without spilling 
     internal details 
  Definition is_valid_loc l al : iProp Σ := 
    (*V forall lq in Lq ++ Lf, PAlloc.is_valid_loc l lq*).*)
  Definition is_valid_loc l al (Lq Lf : list loc) : iProp Σ := 
      (*this is one option 
       the other is to find the page this 
         belongs to and then call is_valid_loc with that page*)
      (([∨ list] l' ∈ (Lq ++ Lf), PAlloc.is_valid_loc l l').


  Definition is_heap al bs : iProp Σ := 
    ∃ (Lq Lf : list loc), 
      IList.is_ilist (al + f_queue)%Z Lq ∗ 
      IList.is_ilist (al + f_full)%Z Lf ∗
      ([∗ list] lq ∈ Lq, ∃ bf, 
          PAlloc.is_page (PairV #lq #(lq + PAlloc.d_off)) bs bf) ∗
      ([∗ list] lf ∈ Lf, 
          PAlloc.is_page (PairV #lf #(lf + PAlloc.d_off)) bs true).

  (*
    Hoare triples and proofs
  *)

  Lemma heap_new_alloc_hoare :
    {{{ emp }}}
      heap_new_alloc #() 
    {{{ al, RET #al; is_heap al BLOCK_SIZE }}}.
  Proof. 
    iIntros (φ) "_ Hphi". iUnfold heap_new_alloc. wp_pures.
    wp_apply wp_allocN; [done|done|]. iIntros (l) "(Hl & _)".
    wp_pures. unfold num_f, queue_size. 
    replace (Z.to_nat (2%nat * 2%nat)) with (2 + 2) by lia.
    rewrite replicate_add array_app length_replicate.
    iDestruct "Hl" as "(H1 & H2)". simpl.
    wp_apply (DCycle.new_spec with "[H1]"); [by rewrite Z.add_0_r|].
    iIntros "Hq". wp_pures. wp_apply (DCycle.new_spec with "H2"). 
    iIntros "Hf". wp_pures. iApply "Hphi". iUnfold is_heap.
    iFrame. by simpl.
  Qed.

  Lemma heap_free_hoare l al bs : 
    {{{ 
      is_heap al bs ∗ ([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v)
      (*is_valid l al big problem*)
    }}}
      heap_free #l
    {{{ RET #(); is_heap al bs }}}.
  Proof. Admitted.

  Lemma heap_alloc_hoare al n bs : 
    {{{ is_heap al bs }}} 
      heap_alloc #al #n
    {{{ vret, RET vret; 
       (∃ l, ⌜vret = SOMEV #l⌝ ∗ 
          ([∗ list] i ∈ seq 0 bs, ∃ v, (l + i)%Z ↦ v) ∗ 
          (*is_valid_loc l al ∗*) is_heap al bs)
        ∨ 
      ⌜vret = NONEV⌝ ∗ is_heap al bs
    }}}.
  Proof. Admitted.

End HAlloc. End HAlloc.
