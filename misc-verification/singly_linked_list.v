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
  ("hd", "tl").

Definition push_front : val := λ: "l" "x",
  let: "hd" := Fst "l" in
  let: "node" := Alloc (InjR ("x", !"hd")) in
  "hd" <- "node";;
  #().

Definition pop_front : val := λ: "l",
  let: "hd" := Fst "l" in
  match: ! !"hd" with
    InjL "_" => InjL #() 
  | InjR "node" =>
     Free (!"hd");;
     "hd" <- Snd "node";;
     InjR (Fst "node")
  end.

Definition push_back : val := λ: "l" "x", 
  let: "tl" := Snd "l" in
  let: "node" := Alloc (InjL #()) in
  !"tl" <- InjR (Pair "x" "node");;
  "tl" <- "node" ;;
  #().

Section Hoare.
Context `{!heapGS_gen hlc Σ}.

Implicit Types l lh lt : loc.
Implicit Types v w li : val.

Fixpoint is_list_nodes (l1 l2 : loc) (vs : list val) : iProp Σ := 
  match vs with 
  | [] => ⌜l1 = l2⌝
  | x::vs => ∃ l, l1 ↦ InjRV (x, #l) ∗ is_list_nodes l l2 vs 
  end.

Definition is_list (v : val) (vs : list val) : iProp Σ := 
  ∃ lh lt l1 l2, ⌜v = PairV #lh #lt⌝ ∗ lh ↦ #l1 ∗ lt ↦ #l2 ∗ 
    is_list_nodes l1 l2 vs ∗ l2 ↦ InjLV #(). 
  
Lemma new_list_hoare :
  {{{ True }}}
    new_list #() 
  {{{ vret, RET vret; is_list vret [] }}}.
Proof. 
  iIntros "%Phi %Ht Hl". iUnfold new_list. wp_pures. wp_alloc l. wp_pures.
  wp_alloc l'. wp_pures. wp_alloc l''. wp_pures. iApply "Hl".
  iUnfold is_list. iExists l', l''. by iFrame.
Qed.

Lemma push_front_hoare li vs v :
  {{{ is_list li vs }}}
    push_front li v
  {{{ RET #(); is_list li (v :: vs) }}}.
Proof.
  iIntros "%Phi Hisl Hl". iUnfold push_front. wp_pures. 
  iDestruct "Hisl" as "(%lh&%lt & %l1 & %l2 & -> & Hlhp & Hltp & Hisln & Hl2)". 
  wp_pures. destruct vs.
  - iDestruct "Hisln" as "->". wp_load. wp_alloc lnew.
    wp_pures. wp_store. iApply "Hl". iUnfold is_list. 
    iExists lh, lt, lnew, l2. by iFrame. 
  - iDestruct "Hisln" as "(%ln & Hl1p & Hisln)". 
    fold is_list_nodes. wp_load. wp_alloc lnew. wp_pures. wp_store. 
    iApply "Hl". iUnfold is_list. iExists lh, lt, lnew, l2. by iFrame.
Qed. 

Lemma pop_front_hoare_nil li :
  {{{ is_list li [] }}}
    pop_front li
  {{{ RET InjLV #(); is_list li [] }}}.
Proof. 
  iIntros "%Phi Hisl Hl".
  iDestruct "Hisl" as "(%lh & %lt & %l1 & %l2 & -> & Hlh & Hlt & -> & Hl1)".
  iUnfold pop_front. wp_load. wp_load. wp_pures. iApply "Hl".
  iUnfold is_list, is_list_nodes. iExists lh, lt, l2, l2. by iFrame.
Qed.

Lemma pop_front_hoare_cons li vs v :
  {{{ is_list li (v :: vs) }}}
    pop_front li
  {{{ RET (InjRV v); is_list li vs }}}.
Proof.
  iIntros "%Phi Hisl Hl".
  iDestruct "Hisl" as "(%lh & %lt & %l1 & %l2 & -> & Hlh & Hlt & Hisln & Hl2) /=".
  iDestruct "Hisln" as "(%ln & Hl1 & Hisnl)". iUnfold pop_front.
  wp_load. wp_load. wp_load. wp_free. wp_store. wp_pures. 
  iApply "Hl". iUnfold is_list. iExists lh, lt, ln, l2. by iFrame.
Qed.

Lemma is_list_nodes_extend vs v l l1 l2 : 
  is_list_nodes l l1 vs -∗ l1 ↦ InjRV (v, #l2) -∗ is_list_nodes l l2 (vs ++ [v]).
Proof.
  iInduction vs as [|v' vs' IH] forall (l); simpl.
  { iIntros "-> Hl1". simpl. by iFrame. }
  iIntros "(%l3 & Hl11 & Hisln) Hl1". iFrame "Hl11". by iApply ("IH" with "[$]"). 
Qed.

Lemma push_back_hoare li vs v :
  {{{ is_list li vs }}}
    push_back li v
  {{{ RET #(); is_list li (vs ++ [v]) }}}.
Proof.
  iIntros "%Phi Hisl Hl". 
  iDestruct "Hisl" as "(%lh & %lt & %l1 & %l2 & -> & Hlh & Hlt & Hisln & Hl2)".
  iUnfold push_back. wp_alloc lnew. wp_load.
  wp_store. wp_store. iApply "Hl".  iUnfold is_list.
  iFrame "Hlh Hlt ∗". iSplitR; [done|]. by iApply (is_list_nodes_extend with "[$]").
Qed.

End Hoare.
