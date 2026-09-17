(*
  Uses:
   Rocq 9.0.1, Ocaml 4.14.1
   Iris (rocq-iris.4.5.0)
   Heap lang (rocq-iris-heap-lang.4.5.0)
*)

From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang proofmode notation.

(*is list is empty the back pointer is last pointer (circular)*)
(*if the list is not empty back pointer is previous to last pointer*)
(*if the list is not empty the first element previous pointer is last pointer*)
(*so prev/back = last is null basically*)
(*first had null as head pointer, but push_back gets annoying, 
   since you need to prove that if lback != lh then 
   vs is not empty, this is true but annoying to prove 
   now with circularity we can implement push_back without 
   that if statement*)
(* last pointer changes in push back still and issue so 
tail is even better, since we can still do the trick but it is stable*)
Definition new_list : val := λ: "_", 
  (*let: "node" := Alloc NONE in*)
  let: "node" := Alloc (InjL NONE) in
  let: "hd" := Alloc "node" in
  let: "tl" := Alloc "node" in
  (*"node" <- InjL "node" ;;*)
  ("hd", "tl").

Definition push_front : val := λ: "l" "x",
  let: "hd" := Fst "l" in
  let: "tl" := Snd "l" in
  (*tail pointer as previous -> basically our null*)
  (*let: "node" := Alloc (InjR ("x", (!"tl", !"hd"))) in*)
  let: "node" := Alloc (InjR ("x", (NONE, !"hd"))) in
  (*update previous pointer of next node to (current) node*)
  match: ! !"hd" with
    InjL "lback" => !"hd" <- InjL "node" 
  | InjR "nnode" => 
      (*copy next and value over, replace previous with node*)
      (*!"hd" <- InjR (Fst "nnode", ("node", Snd (Snd "nnode")))*)
      !"hd" <- InjR (Fst "nnode", (SOME "node", Snd (Snd "nnode")))
  end ;;
  "hd" <- "node";;
  #().

Definition pop_front : val := λ: "l",
  let: "hd" := Fst "l" in
  match: ! !"hd" with
    InjL "_" => InjL #() 
  | InjR "node" =>
     Free (!"hd");;
     let: "prev" := Fst (Snd "node") in
     let: "next" := Snd (Snd "node") in
     "hd" <- "next";;
     (*update previous pointer of new head*)
     match: !"next" with 
       InjL "_" => "next" <- InjL "prev" 
     | InjR "nnode" => 
         "next" <- InjR (Fst "nnode", ("prev", Snd (Snd "nnode"))) 
     end ;;
     (*return value of popped front*)
     InjR (Fst "node")
  end.

Definition push_back : val := λ: "l" "x", 
  let: "hd" := Fst "l" in
  let: "tl" := Snd "l" in
  match: ! !"tl" with 
    InjL "lback" => 
        match: !"lback" with 
          InjL "_" => push_front "l" "x" (*we get here if lback = tl, empty list case*) 
        | InjR "pnode" => 
          let: "lnewlast" := Alloc (InjL #()) in (*() is dummy value, like in new_list*)
          let: "lnowlast" := !"tl" in
          "lnowlast" <- InjR ("x", ("lback", "lnewlast"));;
          (*update previous nodes next pointer to newly inserted node*)
          "lback" <- InjR (Fst "pnode", (Fst (Snd "pnode"), "lnowlast")) ;;
          "lnewlast" <- InjL "lnowlast" ;; (*update with back pointer*)
          "tl" <- "lnewlast" ;; 
          #() (*succes value*)
        end
  | InjR "_" => InjL #() (*error state, should never happen*)
  end.
  
(* TODO(Ben): implement
Definition pop_back : val := λ: "l", "l". 
*)

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
  ∃ lh lt lstart llast lback, ⌜v = PairV #lh #lt⌝ ∗ lh ↦ #lstart ∗ lt ↦ #llast ∗ 
    llast ↦ InjLV #lback ∗ is_list_nodes lt lstart llast lback vs.
     
Lemma new_list_hoare :
  {{{ True }}}
    new_list #() 
  {{{ vret, RET vret; is_list vret [] }}}.
Proof. 
  iIntros "%Phi %Ht Hl". iUnfold new_list. wp_pures. wp_alloc l. wp_pures.
  wp_alloc l'. wp_pures. wp_alloc l''. wp_pures. wp_store. wp_pures. iApply "Hl".
  iUnfold is_list. iExists l', l'', l, l. by iFrame.
Qed.

Lemma push_front_hoare li vs v :
  {{{ is_list li vs }}}
    push_front li v
  {{{ RET #(); is_list li (v :: vs) }}}.
Proof.
  iIntros "%Phi Hisl Hl". iUnfold push_front. wp_pures. 
  iDestruct "Hisl" as "(%lh & %lt & %ls & %ll & %lb & -> & Hlh & Hlt & Hll & Hisln)".
  wp_load. wp_alloc lnode as "Hlnode". wp_load. destruct vs.
  { iDestruct "Hisln" as "(<- & <-)". wp_load. wp_load. wp_store. wp_store. 
    iApply "Hl". iUnfold is_list. iExists lh, lt, lnode, ls, lnode. by iFrame. }
  iDestruct "Hisln" as "(%ln & Hln & Hisln)". fold is_list_nodes.
  wp_load. wp_load. wp_store. wp_store. iApply "Hl". iUnfold is_list.
  iExists lh, lt, lnode, ll, lb. by iFrame.
Qed. 

Lemma pop_front_hoare_nil li :
  {{{ is_list li [] }}}
    pop_front li
  {{{ RET InjLV #(); is_list li [] }}}.
Proof. 
  iIntros "%Phi Hisl Hl".
  iDestruct "Hisl" as "(%lh & %lt & %ls & %ll & %lb & -> & Hlh & Hlt & Hll & (<- & <-))".
  iUnfold pop_front. wp_load. wp_load. wp_pures. iApply "Hl".
  iUnfold is_list, is_list_nodes. iExists lh, lt. by iFrame.
Qed.

Lemma pop_front_hoare_cons li vs v :
  {{{ is_list li (v :: vs) }}}
    pop_front li
  {{{ RET (InjRV v); is_list li vs }}}.
Proof.
  iIntros "%Phi Hisl Hl".
  iDestruct "Hisl" as "(%lh & %lt & %ls & %ll & %lb & -> & Hlh & Hlt & Hll & Hisln) /=".
  iDestruct "Hisln" as "(%ln & Hls & Hisln)". iUnfold pop_front.
  wp_load. destruct vs. 
  { iDestruct "Hisln" as "(<- & <-)". wp_load. wp_load. wp_free. wp_store. wp_load.
    wp_store. wp_pures. iApply "Hl". iUnfold is_list, is_list_nodes. 
    iExists lh, lt. by iFrame. }
  iDestruct "Hisln" as "(%ln2 & Hln & Hisln)". fold is_list_nodes.
  wp_load. wp_load. wp_free. wp_store. wp_load. wp_store.
  wp_pures. iApply "Hl". iUnfold is_list, is_list_nodes. 
  iExists lh, lt, ln, ll, lb. by iFrame.
Qed.

Lemma back_pointsto_last_node lp ls ll lb vs : 
  is_list_nodes lp ls ll lb vs -∗ 
    match vs with 
    | [] => is_list_nodes lp ls ll lb vs 
    | _ => ∃ v (lp2 : loc), lb ↦ InjRV (v, (#lp2, #ll)) ∗ 
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
  {{{ RET #(); is_list li (vs ++ [v]) }}}.
Proof.
  iIntros "%Phi Hisl Hl". 
  iDestruct "Hisl" as "(%lh & %lt & %ls & %ll & %lb & -> & Hlh & Hlt & Hll & Hisln)".
  iUnfold push_back. wp_load. wp_load. wp_pures. 
  iPoseProof (back_pointsto_last_node with "Hisln") as "Hlb";
  destruct vs.
  { iDestruct "Hlb" as "(<- & <-)". wp_load. wp_load. wp_pures.
    iApply ((push_front_hoare (#lh, #lt) [] v) with "[Hlh Hlt Hll] [Hl]"); 
    simpl; [|iApply "Hl"]. iUnfold is_list, is_list_nodes. iExists lh, lt. by iFrame. }
  iDestruct "Hlb" as "(%v1 & %lp2 & Hlb & Hrec)". wp_load. wp_load.
  wp_alloc lnl as "Hlnl". wp_load. wp_store. wp_store. wp_store. wp_store.
  iApply "Hl". iUnfold is_list. iExists lh, lt, ls, lnl. iFrame.
  iSplitR; [done|]. iSpecialize ("Hrec" with "Hlb").
  iApply (extend_is_list_nodes with "[Hrec]"); [|iApply "Hll"].
  (*ll is not stable -> lnl so maybe store tl, is stable and still can 
     do trick in push_back*)
Qed.

End Hoare.
