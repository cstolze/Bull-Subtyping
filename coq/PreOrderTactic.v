Require Import Compare_dec.
Import RelationClasses.
Import Relation_Definitions.

Set Implicit Arguments.

(* This module declares a tactic "preorder" which solves the following goal: *)
(* H1 : x1 < y1, H2 : x2 < y2 ... |- xn < yn *)
(* where < has been instanciated as a PreOrder. *)
(* There is no need to introduce the hypotheses beforehand. *)
(* The solver only uses the reflexivity and transitivity properties of the preorder *)

(* The tactic proceeds by reflection. *)
(* The objects (x1, x2 ...) are stored into a vector and reified into indexes *)
(* The statements x < y are reified into a pair (index_x, index_y) *)
(* The problem is reified into the pair (hypotheses list, goal) *)
(* Then we call the lemma preorder_heuristic *)

(* Sized list to store the objects *)
Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons : forall n : nat, A -> vector A n -> vector A (S n).
(* For vcons: Arguments A, n are implicit *)

(* Indexes for accessing vectors *)
Definition index (n : nat) := {m : nat | m < n}.

Definition index_to_nat {n : nat} (i : index n) : nat :=
  match i with
  | exist _ i _ => i
  end.

(* Decidable proof-irrelevant equality for indexes *)
Definition index_eq {n : nat} (i j : index n) := index_to_nat i = index_to_nat j.
Local Notation "i == j" := (index_eq i j) (at level 70).
Definition index_eq_dec {n : nat} : forall i j : index n, {i == j} +
                                                          {~ i == j}.
Proof.
  intros; unfold index_eq.
  decide equality.
Defined.

(* Helper function to access elements of a vector *)
Fixpoint _get {A : Type} {n : nat} (v : vector A n) {i : nat} {struct v} : i < n -> A.
  refine (match v in vector _ n' return i < n' -> A with
          | vnil _ => fun p : i < 0 => _
          | vcons x v' => match i as x return x < _ -> A with
                          | 0 => fun _ => x
                          | S j => fun p : _ => _get A _ v' j _
                          end
          end).
  - exfalso; inversion p.
  - apply Lt.lt_S_n; assumption.
Defined.

(* Wrapper for _get *)
Definition get {A : Type} {n : nat} (v : vector A n) (i : index n) : A :=
  match i with
  | exist _ _ p => _get v p
  end.

(* _get is proof-irrelevant *)
Lemma _get_irrelevant : forall A n (v : vector A n) i (p p' : i < n), _get v p = _get v p'.
Proof.
  intros ? ? v; induction v; intros i p ?.
  - inversion p.
  - simpl; destruct i; trivial.
Qed.

(* get is proof-irrelevant *)
Corollary get_irrelevant : forall A n (v : vector A n) (i j : index n), i == j -> get v i = get v j.
Proof.
  intros ? ? v [? ?] [? ?] H; lazy in H.
  subst.
  apply _get_irrelevant.
Qed.

(* Type that stores the reified goal *)
Definition formula (n : nat) : Set := (list (index n * index n)) * (index n * index n).

(* Heuristic type for heuristic functions: give a proof (Yes) or don't (No) *)
Inductive partial {A : Prop} : Set :=
| Yes : A -> partial
| No : partial.
Local Notation "[ A ]" := (@partial A).

(* Unpacking a heuristic proof *)
Definition partialOut {A : Prop} (p : [A]) : match p with | Yes _ => A | No => True end :=
  match p with
  | Yes p => p
  | No => I
  end.

Section PreOrderHeuristic.
  Variables (A : Type) (R : relation A).
  Hypothesis R_po : PreOrder R.
  Local Notation "x < y" := (R x y).

  (* Transform the reification back to the goal *)
  Definition denote_formula {n : nat} (v : vector A n) (f : formula n) : Prop :=
    match f with
    | (l, (i,j)) =>
      (fix loop l :=
         match l with
         | nil => get v i < get v j
         | cons (i,j) l' => get v i < get v j -> loop l'
         end) l
    end.

  (* Helper lemmas for preorder_heuristic *)

  (* Adding hypotheses work properly. It is transparent because it enables the recursive call. *)
  Lemma denote_cons : forall n (v: vector _ n) i j l a b, denote_formula v (cons (i,j) l, (a,b)) = (get v i < get v j -> denote_formula v (l,(a,b))).
  Proof.
    intros.
    induction l; auto.
  Defined.

  (* The goal preserves the transitivity property *)
  Lemma denote_trans : forall {n} {v : vector _ n} {l x} y {z}, denote_formula v (l,(x,y)) -> denote_formula v (l,(y,z)) -> denote_formula v (l,(x,z)).
  Proof.
    intros ? ? l ? ? ?; induction l as [|(?,?) ?];
      repeat rewrite denote_cons;
      auto; simpl.
    etransitivity; eauto.
  Qed.

  (* Sometimes, a < b because a < b *)
  Lemma denote_hyp : forall n (v : vector _ n) l a b, get v a < get v b -> denote_formula v (l,(a,b)).
  Proof.
    intros ? ? l ? ?; induction l as [|(?,?) ?];
      try rewrite denote_cons; auto.
  Qed.

  (* Main heuristic *)
  Definition preorder_heuristic : forall (n : nat) (v : vector A n) (f : formula n), [ denote_formula v f ].
    intros ? ? [l (a,b)]; generalize a b; clear a b.
    (* Induction on the number of hypotheses *)
    induction l as [|(i,j) l is_less]; intros a b.
    - (* Case with no hypothesis: a < b if a == b (same index) *)
      refine (if (index_eq_dec a b)
              then Yes _
              else No); simpl.
      erewrite get_irrelevant; [reflexivity | assumption].
    - (* Inductive case: either induction or transitivity through the new hypothesis *)
      rewrite denote_cons.
      refine (match (is_less a b) with
              | Yes _ => Yes _
              | No => match (is_less a i) with
                      | Yes _ => match (is_less j b) with
                                 | Yes _ => Yes _
                                 | No => No
                                 end
                      | No => No
                      end
              end); trivial; intros.
      (* Transitive case *)
      apply (denote_trans i); trivial.
      apply (denote_trans j); trivial.
      apply denote_hyp; trivial.
  Defined.
End PreOrderHeuristic.

(* Ltac functions below *)

(* Vector manipulation functions *)

(* Cast (i : nat) to an index {i : nat | i < n} *)
Ltac nat_to_index i n :=
  (* lt_dec: forall n m : nat, {n < m} + {~ n < m} *)
  lazymatch eval lazy in (lt_dec i n) with
  | left _ ?a => constr:(exist (fun x => x < n) i a)
  end.

(* See whether x is syntactically in v *)
Ltac is_in_vector x v :=
  lazymatch v with
  | vnil _ => false
  | vcons x _ => true
  | vcons _ ?v' => is_in_vector x v'
  end.

(* We can avoid syntactical duplication when building a vector *)
Ltac add_in_vector x v :=
  lazymatch is_in_vector x v with
  | true => v
  | false => constr:(vcons x v)
  end.

(* Find the position of x in v (x must be in v) (returns a nat) *)
Ltac lookup_vector x v :=
  lazymatch v with
  | vcons x _ => O
  | vcons _ ?v' => let n := lookup_vector x v' in
                   constr:(S n)
  end.

(* Reification functions *)

(* Parse the expression e to record all the objects in a vector *)
Ltac create_vector R e :=
  lazymatch e with
  | R ?x ?y -> ?e' => let v' := create_vector R e' in
                      add_in_vector x ltac:(add_in_vector y v')
  | R ?x ?y => add_in_vector x constr:(vcons y (vnil _))
  end.

(* Create a formula f such that denote_formula R v f = e *)
Ltac create_formula R e v :=
  let n := lazymatch type of v with
           | vector _ ?n => n
           end in
  lazymatch e with
  | R ?x ?y -> ?e' => let x := nat_to_index ltac:(lookup_vector x v) n in
                      let y := nat_to_index ltac:(lookup_vector y v) n in
                      let f := create_formula R e' v in
                      match f with
                      | pair ?l ?h => constr:((cons (x,y) l, h))
                      end
  | R ?x ?y => let x := nat_to_index ltac:(lookup_vector x v) n in
               let y := nat_to_index ltac:(lookup_vector y v) n in
               constr:((@nil (index n * index n),(x,y)))
  end.

(* Main reification function *)
(* Revert all the _ < _ hypotheses and replace the goal with denote_formula R v f *)
Ltac quote_formula R :=
  repeat lazymatch goal with
         | H : R _ _ |- _ => revert H
         end;
  lazymatch goal with
  | |- ?e => let v := create_vector R e in
             let f := create_formula R e v in
             change (denote_formula R v f)
  end.

(* Main tactic *)
Ltac preorder :=
  intros;
  match goal with
  | |- ?R _ _ => quote_formula R;
                 match goal with
                 | |- denote_formula R ?c ?f => exact (partialOut (preorder_heuristic _ c f))
                 end
  | _ => fail "preorder tactic unsuccessful"
  end.

(*
  Goal forall x y z t : nat, x <= y -> z <= t -> y <= z -> x <= t.
  Proof.
  time preorder.
  Qed.
*)
