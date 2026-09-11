(*
  Uses:
   Rocq 9.0.1, Ocaml 4.14.1
   Iris (rocq-iris.4.5.0)
   Heap lang (rocq-iris-heap-lang.4.5.0)
*)

From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang proofmode notation.

Definition new_list : val := λ: "_", 
  let: "node" := Alloc (InjLV #()) in
  let: "hd" := Alloc "node" in
  let: "tl" := Alloc "node" in
  "node" <- InjL "hd";;
  ("hd", "tl").

Definition push_front : val := λ: "l" "x",
  let: "hd" := Fst "l" in
  let: "node" := Alloc (InjR ("x", ("hd", !"hd"))) in
  (*update previous pointer of next node to (current) node*)
  match: ! !"hd" with
    InjL "lback" => !"hd" <- InjL "node"
  | InjR "nnode" => 
      (*copy next and value over, replace previous with node*)
      !"hd" <- InjR (Fst "nnode", ("node", Snd (Snd "nnode")))
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
      (*lback can also be hd, then we have empty list then we just push front*)
      if: "lback" = "hd" 
      then push_front "l" "x"
      else 
        match: !"lback" with 
          InjL "_" => InjL #() (*error state, should never happen*)
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

Implicit Types l : loc.
Implicit Types v w li : val.

(*not going to work for push_back and pop_back*)
Fixpoint is_list_nodes (lprev lnow llast lback : loc) (vs : list val) : iProp Σ := 
  match vs with 
  | [ ] => ⌜lnow = llast⌝ ∗ ⌜lprev = lback⌝
  | [v] => lnow ↦ InjRV (v, (#lprev, (LitV (LitLoc llast)))) ∗ ⌜lnow = lback⌝
  | v::vs => ∃ lnext, lnow ↦ InjRV (v, (#lprev, (LitV (LitLoc lnext)))) ∗ 
                  is_list_nodes lnow lnext llast lback vs
  end.

Definition is_list (v : val) (vs : list val) : iProp Σ := 
  ∃ lh lt lnext llast, ⌜v = PairV (LitV (LitLoc lh)) (LitV (LitLoc lt))⌝ ∗ 
    lh ↦ (LitV (LitLoc lnext)) ∗ lt ↦ (LitV (LitLoc llast)) ∗ 
    ∃ lback, llast ↦ InjLV (LitV (LitLoc lback)) ∗ is_list_nodes lh lnext llast lback vs.
(* see note on this *)
     
Lemma new_list_hoare :
  {{{ True }}}
    new_list #() 
  {{{ vret, RET vret; is_list vret [] }}}.
Proof. 
  iIntros "%Phi %Ht Hl". iUnfold new_list. wp_pures. wp_alloc l. wp_pures.
  wp_alloc l'. wp_pures. wp_alloc l''. wp_store. wp_pures. iApply "Hl".
  iUnfold is_list. iExists l', l''. by iFrame.
Qed.

Lemma push_front_hoare li vs v :
  {{{ is_list li vs }}}
    push_front li v
  {{{ RET #(); is_list li (v :: vs) }}}.
Proof.
  iIntros "%Phi Hisl Hl". iUnfold push_front. wp_pures. 
  iDestruct "Hisl" as "(%lh & %lt & %ln & %ll & -> & Hlh & Hlt & %lb & Hll & Hisln)".
  wp_load. wp_alloc lnode. wp_load. destruct vs.
  { iDestruct "Hisln" as "(<- & <-)". wp_load. wp_load. wp_store. wp_store. 
    iApply "Hl". iUnfold is_list. iExists lh, lt, lnode, ln. by iFrame. }
  destruct vs. 
  { iDestruct "Hisln" as "(Hln & ->)". wp_load. wp_load. wp_store. wp_store. 
    iApply "Hl". iUnfold is_list. iExists lh, lt, lnode, ll. by iFrame. }
  iDestruct "Hisln" as "(%lnext & Hln & Hisnl)". fold is_list_nodes.
  wp_load. wp_load. wp_store. wp_store. iApply "Hl". iUnfold is_list.
  iExists lh, lt, lnode, ll. by iFrame.
Qed. 

Lemma pop_front_hoare_nil li :
  {{{ is_list li [] }}}
    pop_front li
  {{{ RET InjLV #(); is_list li [] }}}.
Proof. 
  iIntros "%Phi Hisl Hl".
  iDestruct "Hisl" as "(%lh & %lt & %ln & %ll & -> & Hlh & Hlt & %lb & Hl2 & <- & <-)".
  iUnfold pop_front. wp_load. wp_load. wp_pures. iApply "Hl".
  iUnfold is_list, is_list_nodes. iExists lh, lt, ln, ln. by iFrame.
Qed.

Lemma pop_front_hoare_cons li vs v :
  {{{ is_list li (v :: vs) }}}
    pop_front li
  {{{ RET (InjRV v); is_list li vs }}}.
Proof.
  iIntros "%Phi Hisl Hl".
  iDestruct "Hisl" as "(%lh & %lt & %ln & %ll & -> & Hlh & Hlt & Hisln) /=".
  iDestruct "Hisln" as "(%lb & Hll & Hisln)". iUnfold pop_front.
  wp_load. destruct vs. 
  { iDestruct "Hisln" as "(Hln & <-)". wp_load. wp_load. wp_free. wp_store. wp_load.
    wp_store. wp_pures. iApply "Hl". iUnfold is_list, is_list_nodes. 
    iExists lh, lt, ll, ll. by iFrame. }
  iDestruct "Hisln" as "(%lnext & Hln & Hisln)".
  wp_load. wp_load. wp_free. wp_store. destruct vs.
  { iDestruct "Hisln" as "(Hlnext & <-)". wp_load. wp_store. wp_pures. iApply "Hl".
    iUnfold is_list, is_list_nodes. iExists lh, lt, lnext, ll. by iFrame. }
  iDestruct "Hisln" as "(%lnext2 & Hlnext & Hisln)". fold is_list_nodes. 
  wp_load. wp_store. wp_pures. iApply "Hl". 
  iUnfold is_list, is_list_nodes. iExists lh, lt, lnext, ll. by iFrame.
Qed.

(*stuck in proof*)
Lemma push_back_hoare li vs v :
  {{{ is_list li vs }}}
    push_back li v
  {{{ RET #(); is_list li (vs ++ [v]) }}}.
Proof.
  iIntros "%Phi Hisl Hl". 
  iDestruct "Hisl" as "(%lh & %lt & %ln & %ll & -> & Hlh & Hlt & %lb & Hll & Hisln)".
  iUnfold push_back. wp_load. wp_load. wp_pures. destruct vs.
  { iDestruct "Hisln" as "(<- & <-)". destruct (bool_decide (#lh = #lh)) eqn:Heq. wp_pures.
    - iApply ((push_front_hoare (LitV (LitLoc lh), LitV (LitLoc lt)) [] v) 
      with "[Hlh Hlt Hll] [Hl]"); simpl; [|iApply "Hl"].
      iUnfold is_list, is_list_nodes. iExists lh, lt, ln, ln. by iFrame.
    - admit. (*should be easy*) }
  destruct (bool_decide (#lb = #lh)) eqn:Heq.
  { admit. (*need to prove that lb != lh if not empty :|, seems tediouss,
      should get it from seperation logic but how?*) }
  wp_pures. destruct vs.
  { iDestruct "Hisln" as "(Hlnext & <-)". wp_load. wp_alloc lnewlast. wp_load. 
    wp_store. wp_store. wp_store. wp_store. iApply "Hl". iUnfold is_list.
    iExists lh, lt, ln, lnewlast. by iFrame. }
  iDestruct "Hisln" as "(%lnext2 & Hlnext & Hisln)". fold is_list_nodes. 
  wp_load.
Qed.

End Hoare.
