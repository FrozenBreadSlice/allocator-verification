(*
  Uses:
   Rocq 9.0.1, Ocaml 4.14.1
   Iris (rocq-iris.4.5.0)
   Heap lang (rocq-iris-heap-lang.4.5.0)
*)

From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang proofmode notation.

Definition new_list : val := λ: "_", 
  let: "start" := Alloc NONE in
  let: "end" := Alloc NONE in
  let: "hd" := Alloc "start" in
  let: "tl" := Alloc "end" in
  "start" <- InjL "end" ;;
  "end" <- InjL "start" ;;
  ("hd", "tl").

Definition push_front : val := λ: "l" "x",
  let: "hd" := Fst "l" in
  let: "tl" := Snd "l" in
  match: ! !"hd" with 
    InjL "lnext" => 
    let: "node" := Alloc (InjR ("x", (!"hd", "lnext"))) in
    (*update previous pointer of next node to (current) node*)
    match: !"lnext" with
      InjL "lback" => "lnext" <- InjL "node" 
    | InjR "nnode" => "lnext" <- InjR (Fst "nnode", ("node", Snd (Snd "nnode")))
    end ;;
    !"hd" <- InjL "node" ;;
    SOME #()    
  | InjR "_" => NONE (*error state*)
  end.

Definition pop_front : val := λ: "l",
  let: "hd" := Fst "l" in
  match: ! !"hd" with
    InjL "lnext" => 
    match: !"lnext" with 
      InjL "_" => NONE (*no element in list*)
    | InjR "node" => 
      Free "lnext" ;;
      let: "prev" := Fst (Snd "node") in
      let: "next" := Snd (Snd "node") in
      !"hd" <- InjL "next" ;;
      (*"hd" <- "next";;*)
      (*update previous pointer of new head*)
      match: !"next" with 
        InjL "_" => "next" <- InjL "prev" 
      | InjR "nnode" => "next" <- InjR (Fst "nnode", ("prev", Snd (Snd "nnode"))) 
      end ;;
      SOME (Fst "node")
    end
  | InjR "_" => NONE (*error state*)
  end.

(*TODO(Ben): write version without writing to lt?*)
Definition push_back : val := λ: "l" "x", 
  let: "hd" := Fst "l" in
  let: "tl" := Snd "l" in
  match: ! !"tl" with 
    InjL "lback" => 
    match: !"lback" with 
      InjL "_" => push_front "l" "x" (*empty list case*) 
    | InjR "pnode" => 
      let: "lnewlast" := Alloc NONE in 
      let: "lnowlast" := !"tl" in
      "lnowlast" <- InjR ("x", ("lback", "lnewlast")) ;;
      (*update previous nodes next pointer to newly inserted node*)
      "lback" <- InjR (Fst "pnode", (Fst (Snd "pnode"), "lnowlast")) ;;
      "lnewlast" <- InjL "lnowlast" ;; (*update with back pointer*)
      "tl" <- "lnewlast" ;; 
      SOME #()
    end
  | InjR "_" => NONE (*error state*)
  end.
  
Definition pop_back : val := λ: "l", 
  let: "tl" := Snd "l" in 
  match: ! !"tl" with 
    InjL "lback" =>
    match: !"lback" with 
      InjL "_" => NONE  
    | InjR "node" =>
      Free "lback" ;;
      let: "prev" := Fst (Snd "node") in 
      (*update lback to prev of node*) 
      !"tl" <- InjL "prev" ;; 
      (*update previous next pointer to !"tl"*)
      match: !"prev" with 
        InjL "_" => "prev" <- InjL !"tl" 
      | InjR "node" => "prev" <- InjR (Fst "node", (Fst (Snd "node"), !"tl"))  
      end ;;
      SOME (Fst "node")
    end
  | InjR "_" => NONE (*error state*)
  end.


Section Hoare.
  Context `{!heapGS_gen hlc Σ}.

  Implicit Types l lh lt lstart lnext llast lback lnl : loc.
  Implicit Types v w li : val.

  Fixpoint is_list_nodes (lprev lnow llast lback : loc) (vs : list val) : iProp Σ := 
    match vs with 
    | [] => ⌜lnow = llast⌝ ∗ ⌜lprev = lback⌝ 
    | v::vs => ∃ l, lnow ↦ InjRV (v, (#lprev, #l)) ∗ is_list_nodes lnow l llast lback vs
    end.

  Definition is_list (v : val) (vs : list val) : iProp Σ := 
    ∃ lh lt lstart llast lnext lback, ⌜v = PairV #lh #lt⌝ ∗ 
    (*lh ↦ InjLV #lstart ∗ lt ↦ InjLV #lback ∗ 
       is_list_nodes lh lstart lt lback vs. (*could try this?*) *)
      lh ↦ #lstart ∗ lt ↦ #llast ∗
      lstart ↦ InjLV #lnext ∗ llast ↦ InjLV #lback ∗ 
         is_list_nodes lstart lnext llast lback vs.
   
  Lemma new_list_hoare :
    {{{ True }}}
      new_list #() 
    {{{ vret, RET vret; is_list vret [] }}}.
  Proof. 
    iIntros (φ) "%Ht Hphi". iUnfold new_list. wp_alloc ls. wp_alloc ll. 
    wp_alloc lh. wp_alloc lt. wp_store. wp_store. wp_pures. iApply "Hphi".
    iUnfold is_list. iExists lh, lt, ls, ll. by iFrame. 
  Qed.

  Lemma push_front_hoare li vs v :
    {{{ is_list li vs }}}
      push_front li v
    {{{ RET SOMEV #(); is_list li (v :: vs) }}}.
  Proof.
    iIntros (φ) "Hisl Hphi". iUnfold push_front. wp_pures. 
    iDestruct "Hisl" as "(%lh&%lt&%ls&%ll&%ln&%lb & -> & Hlh & Hlt & Hls & Hll & Hisln)".
    wp_load. wp_load. wp_load. wp_alloc lnode as "Hlnode". 
    destruct vs.
    { iDestruct "Hisln" as "(<- & <-)". wp_load. wp_store. wp_load. wp_store. wp_pures.
      iApply "Hphi". iExists lh, lt, ls, ln. by iFrame. }
    iDestruct "Hisln" as "(%ln2 & Hln & Hisln)". fold is_list_nodes.
    wp_load. wp_store. wp_load. wp_store. wp_pures. iApply "Hphi".
    iExists lh, lt, ls, ll. by iFrame.
  Qed. 

  Lemma pop_front_hoare_nil li :
    {{{ is_list li [] }}}
      pop_front li
    {{{ RET NONEV; is_list li [] }}}.
  Proof. 
    iIntros (φ) "Hisl Hphi".
    iDestruct "Hisl" as "(%lh&%lt&%ls&%ll&%ln&%lb & -> & Hlh & Hlt & Hls & Hll & Hisln)".
    iUnfold pop_front. wp_load. wp_load. wp_pures. iDestruct "Hisln" as "(<- & <-)". 
    wp_load. wp_pures. iApply "Hphi". iExists lh, lt, ls, ln, ln, ls. by iFrame.
  Qed. 

  Lemma pop_front_hoare_cons li vs v :
    {{{ is_list li (v :: vs) }}}
      pop_front li
    {{{ RET SOMEV v; is_list li vs }}}.
  Proof.
    iIntros (φ) "Hisl Hphi".
    iDestruct "Hisl" as "(%lh&%lt&%ls&%ll&%ln&%lb & -> & Hlh & Hlt & Hls & Hll & Hisln)".
    iDestruct "Hisln" as "(%ln' & Hln & Hisln)". fold is_list_nodes. 
    iUnfold pop_front. wp_load. wp_load. wp_load. wp_free. wp_pures. wp_load. wp_store. 
    destruct vs.
    { iDestruct "Hisln" as "(<- & <-)". wp_load. wp_store. wp_pures. iApply "Hphi". 
      iExists lh, lt, ls, ln', ln', ls. by iFrame. } 
    iDestruct "Hisln" as "(%ln2 & Hln & Hisln)". fold is_list_nodes.
    wp_load. wp_store. wp_pures. iApply "Hphi". iUnfold is_list, is_list_nodes. 
    iExists lh, lt, ls, ll, ln', lb. by iFrame.
  Qed.

  Lemma back_pointsto_last_node lp ls ll lb vs : 
    is_list_nodes lp ls ll lb vs -∗ 
      match vs with 
      | [] => is_list_nodes lp ls ll lb vs 
      | _ => ∃ v lp2, lb ↦ InjRV (v, (#lp2, #ll)) ∗ 
                (lb ↦ InjRV (v, (#lp2, #ll)) -∗ is_list_nodes lp ls ll lb vs)
      end.
  Proof.
    iInduction vs as [|v vs IH] forall (lp ls ll lb); simpl; [done|]. 
    iIntros "(%ln & Hls & Hisln)". iSpecialize ("IH" with "Hisln").
    destruct vs.
    { iDestruct "IH" as "(<- & <-)" . iExists v, lp. iSplitL "Hls"; [done|].
      iIntros "Hls". iExists ln. iSplitL "Hls"; done. }
    iDestruct "IH" as "(%v1 & %lp2 & Hlb & Hrec)". 
    iExists v1, lp2. iSplitL "Hlb"; [done|]. iIntros "Hlb". iExists ln. 
    iSplitL "Hls"; [done|]. iApply "Hrec". done.
  Qed.

  Lemma extend_is_list_nodes ls ll0 ll lnl lb v vs : 
    is_list_nodes ll0 ls ll lb vs -∗ ll ↦ InjRV (v, (#lb, #lnl)) -∗ 
      is_list_nodes ll0 ls lnl ll (vs ++ [v]).
  Proof.
    iInduction vs as [|v' vs IH] forall (ls ll0 ll lnl lb v); simpl.
    { iIntros "(<- & <-) Hll". by iFrame. }
    iIntros "(%l & Hls & Hisln) Hll". iExists l. iSplitL "Hls"; [done|].
    iApply ("IH" with "Hisln"). done.
  Qed.

  Lemma push_back_hoare li vs v :
    {{{ is_list li vs }}}
      push_back li v
    {{{ RET SOMEV #(); is_list li (vs ++ [v]) }}}.
  Proof.
    iIntros (φ) "Hisl Hphi". 
    iDestruct "Hisl" as "(%lh&%lt&%ls&%ll&%ln&%lb & -> & Hlh & Hlt & Hls & Hll & Hisln)".
    iUnfold push_back. wp_load. wp_load. wp_pures. 
    iPoseProof (back_pointsto_last_node with "Hisln") as "Hlb"; destruct vs.
    { iDestruct "Hlb" as "(<- & <-)". wp_load. wp_pures. 
      iApply ((push_front_hoare (#lh, #lt) [] v) with "[Hlh Hlt Hls Hll] [Hphi]"); 
      simpl; [|iApply "Hphi"]. iUnfold is_list, is_list_nodes. iExists lh, lt, ls, ln. 
      by iFrame. }
    iDestruct "Hlb" as "(%v1 & %lp2 & Hlb & Hrec)". wp_load. wp_alloc lnl as "Hlnl".
    wp_load. wp_store. wp_store. wp_store. wp_store. wp_pures. iApply "Hphi".
    iExists lh, lt, ls, lnl, ln, ll. iFrame. iSplitR; [done|]. 
    iSpecialize ("Hrec" with "Hlb"). by iApply (extend_is_list_nodes with "[Hrec]"); 
    [|iApply "Hll"].
  Qed.

  Lemma pop_back_hoare_nil li : 
    {{{ is_list li [] }}}
      pop_back li 
    {{{ RET NONEV; is_list li [] }}}.
  Proof. 
    iIntros (φ) "(%lh&%lt&%ls&%ll&%ln&%lb&->& Hlh & Hlt & Hls & Hll & (<- & <-)) Hphi". 
    iUnfold pop_back. wp_load. wp_load. wp_load. wp_pures. iApply "Hphi".
    iExists lh, lt, ls, ln, ln, ls. by iFrame.
  Qed.

  Lemma is_list_nodes_app lp ls ll lb vs1 vs2 : 
    is_list_nodes lp ls ll lb (vs1 ++ vs2) -∗ 
      ∃ (lm lmb : loc), is_list_nodes lp ls lm lmb vs1 ∗ is_list_nodes lmb lm ll lb vs2.
  Proof.
    iInduction vs1 as [|v vs IH] forall (lp ls ll lb); simpl. 
    { iIntros "Hisln". iExists ls, lp. by iFrame. } 
    iIntros "(%l & Hls & Hisln)". iSpecialize ("IH" with "Hisln"). 
    iDestruct "IH" as "(%lm & %lmb & Hislnvs & Hislnvs2)". iExists lm, lmb. 
    iSplitR "Hislnvs2"; [|done]. iFrame.
  Qed.
    
  Lemma pop_back_hoare_cons li vs v :
    {{{ is_list li (v :: vs) }}}
      pop_back li
    {{{ vret, RET vret; ∃ v', 
      ⌜Some v' = last (v::vs)⌝ ∗ ⌜vret = SOMEV v'⌝ ∗ 
      is_list li (removelast (v::vs)) 
    }}}.
  Proof.
    iIntros (φ) "(%lh&%lt&%ls&%ll&%ln&%lb&->& Hlh & Hlt & Hls & Hll & Hisln) Hphi". 
    iUnfold pop_back. wp_load. wp_load. wp_pures. 
    destruct vs. 
    { iDestruct "Hisln" as "(%ln1 & Hln & Hisln)". fold is_list_nodes. 
      iDestruct "Hisln" as "(<- & <-)". wp_load. wp_pures. wp_free. wp_load.
      wp_store. wp_load. wp_load. wp_store. wp_pures. iApply "Hphi".
      iExists v. iSplitR; [done|]. iSplitR; [done|]. 
      iExists lh, lt, ls, ln1, ln1, ls. by iFrame. }
    assert (∃ vs1 v' v'', v :: v0 :: vs = vs1 ++ [v'; v'']); [admit|].
    destruct H as (vs1 & v1 & v2 & ->).
    iPoseProof (is_list_nodes_app with "Hisln") as "Hsplit".
    iDestruct "Hsplit" as "(%lm & %lmb & Hisln & Hisln2)".
    iDestruct "Hisln2" as "(%l1 & Hlm & %l2 & Hl1 & <- & <-)".
    wp_load. wp_free. wp_load. wp_store. wp_load. wp_load. wp_store. wp_pures.
    iApply "Hphi". iExists v2. iSplitR; [admit|]. iSplitR; [done|].
    iExists lh, lt, ls, l2, ln, lm. iFrame. iSplitR; [done|].
  Admitted.

End Hoare.
