Require Import Classes.Morphisms.
Require Import Relations.
Require Import Structures.Equalities.
Require Import Omega.
Require Import Unicode.Utf8_core.
Require PreOrderTactic.
Notation "x ⇒ y" := (x -> y)
                      (at level 99, y at level 200, right associativity): type_scope.

(* Dummy module type *)
Module Type SetTyp <: Typ.
  Parameter t : Set.
End SetTyp.

(* Module type for the variables: equality has to be decidable *)
Module Type VariableAlphabet <: UsualDecidableType :=
  SetTyp <+ HasUsualEq <+ UsualIsEq <+ HasEqDec.

Module Types (𝕍 : VariableAlphabet).

  (* Our type syntax *)
  Inductive term : Set :=
  | Var : 𝕍.t ⇒ term
  | Arrow : term ⇒ term ⇒ term
  | Inter : term ⇒ term ⇒ term
  | Union : term ⇒ term ⇒ term
  | Omega : term.
  Infix "⟶" := (Arrow) (at level 60, right associativity).
  Notation "(⟶)" := Arrow (only parsing).
  Infix "∩" := (Inter) (at level 35, right associativity).
  Notation "(∩)" := (Inter) (only parsing).
  Infix "∪" := (Union) (at level 30, right associativity).
  Notation "(∪)" := (Union) (only parsing).
  Notation "'ω'" := (Omega).

  (* measure on the types *)
  Fixpoint size (σ : term) : nat :=
    match σ with
    | Var α => 0
    | σ ⟶ τ => S((size σ) + (size τ))
    | σ ∩ τ => S((size σ) + (size τ))
    | σ ∪ τ => S((size σ) + (size τ))
    | ω => 0
    end.
  Definition pair_size (x : term * term) : nat :=
    let (s,t) := x in size s + size t.

  (* Well-foundedness principle for the main algorithm *)
  Definition main_algo_order : relation (term * term) :=
    λ x y, pair_size x < pair_size y.
  Definition wf_main_algo : well_founded main_algo_order := well_founded_ltof _ _.

  Module SubtypeRelation.
    Reserved Infix "≤" (at level 70).
    Reserved Infix "~=" (at level 70).

    (* The subtyping axioms, as defined in the theory Ξ of
       Barbanera, Franco, Mariangiola Dezani-Ciancaglini, and Ugo Deliguoro. "Intersection and union types: syntax and semantics." Information and Computation 119.2 (1995): 202-230. *)
    Inductive Subtype : term ⇒ term ⇒ Prop :=
    | R_InterMeetLeft : ∀ σ τ, σ ∩ τ ≤ σ
    | R_InterMeetRight : ∀ σ τ, σ ∩ τ ≤ τ
    | R_InterIdem : ∀ τ, τ ≤ τ ∩ τ
    | R_UnionMeetLeft : ∀ σ τ, σ ≤ σ ∪ τ
    | R_UnionMeetRight : ∀ σ τ, τ ≤ σ ∪ τ
    | R_UnionIdem : ∀ τ, τ ∪ τ ≤ τ
    | R_InterDistrib : ∀ σ τ ρ,
        (σ ⟶ ρ) ∩ (σ ⟶ τ) ≤ σ ⟶ ρ ∩ τ
    | R_UnionDistrib : ∀ σ τ ρ,
        (σ ⟶ ρ) ∩ (τ ⟶ ρ) ≤ σ ∪ τ ⟶ ρ
    | R_InterSubtyDistrib: ∀ σ σ' τ τ',
        σ ≤ σ' ⇒ τ ≤ τ' ⇒ σ ∩ τ ≤ σ' ∩ τ'
    | R_UnionSubtyDistrib: ∀ σ σ' τ τ',
        σ ≤ σ' ⇒ τ ≤ τ' ⇒ σ ∪ τ ≤ σ' ∪ τ'
    | R_InterUnionDistrib: ∀ σ τ ρ,
        σ ∩ (τ ∪ ρ) ≤ (σ ∩ τ) ∪ (σ ∩ ρ)
    | R_CoContra : ∀ σ σ' τ τ',
        σ ≤ σ' ⇒ τ ≤ τ' ⇒ σ' ⟶ τ ≤ σ ⟶ τ'
    | R_OmegaTop : ∀ σ, σ ≤ ω
    | R_OmegaArrow : ω ≤ ω ⟶ ω
    | R_Reflexive : ∀ σ, σ ≤ σ
    | R_Transitive : ∀ σ τ ρ, σ ≤ τ ⇒ τ ≤ ρ ⇒ σ ≤ ρ
    where "σ ≤ τ" := (Subtype σ τ).
    Notation "(≤)" := (Subtype) (only parsing).

    (* The equivalence relation *)
    Definition equiv (σ τ : term) : Prop := (σ ≤ τ) ∧ (τ ≤ σ).
    Notation "σ ~= τ" := (equiv σ τ).
    Notation "(~=)" := (equiv) (only parsing).

    (* SubtypeHints database *)
    Create HintDb SubtypeHints.
    Hint Constructors Subtype : SubtypeHints.
    Hint Unfold equiv : SubtypeHints.

    (* Add some useful tactics *)
    Ltac preorder := PreOrderTactic.preorder.
    Ltac inv H := inversion H; clear H; subst.

    (* Boost auto *)
    Local Hint Extern 0 (_ ≠ _) => discriminate.
    Local Hint Extern 0 => lazymatch goal with
                     | H : ?x ≠ ?x |- _ => contradiction
                     end.
    Local Hint Extern 1 => lazymatch goal with
                     | H : _ ∧ _ |- _ => destruct H
                     | H : _ ∨ _ |- _ => destruct H
                     end.

    (* Unlock all the preorder-related tactics for ≤ *)
    Instance Subtypes_Reflexive : Reflexive (≤) := R_Reflexive.
    Instance Subtypes_Transitive : Transitive (≤) := R_Transitive.
    Instance Subtypes_Preorder : PreOrder (≤) :=
      {| PreOrder_Reflexive := Subtypes_Reflexive;
         PreOrder_Transitive := Subtypes_Transitive |}.

    (* Unlock all the equivalence-related tactics for ~= *)
    Instance equiv_Reflexive: Reflexive (~=).
    Proof.
      auto with SubtypeHints.
    Qed.
    Hint Immediate equiv_Reflexive : SubtypeHints.
    Instance equiv_Transitive: Transitive (~=).
    Proof.
      compute.
      intros ? ? ? [? ?] [? ?].
      split; etransitivity; eassumption.
    Qed.
    Instance equiv_Symmetric: Symmetric (~=).
    Proof.
      compute; auto.
    Qed.
    Hint Immediate equiv_Symmetric : SubtypeHints.
    Instance equiv_Equivalence: Equivalence (~=) :=
      {| Equivalence_Reflexive := equiv_Reflexive;
         Equivalence_Transitive := equiv_Transitive;
         Equivalence_Symmetric := equiv_Symmetric |}.
    Instance Subtypes_PartialOrder : PartialOrder (~=) (≤).
    Proof.
      compute; auto.
    Qed.

    (* Let's make the SubtypeHints database bigger *)
    (* ≤-related facts *)
    Fact Inter_inf : ∀ σ τ ρ, σ ≤ τ ⇒ σ ≤ ρ ⇒ σ ≤ τ ∩ ρ.
    Proof with auto with SubtypeHints.
      intros.
      transitivity (σ ∩ σ)...
    Qed.
    Hint Resolve Inter_inf : SubtypeHints.

    Fact Inter_inf' : ∀ σ τ ρ, σ ≤ τ ∩ ρ ⇒ (σ ≤ τ) ∧ (σ ≤ ρ).
    Proof with auto with SubtypeHints.
      intros; split;
        etransitivity;
        try eassumption...
    Qed.

    (* Don't put it in auto or it may be slow *)
    Fact Inter_inf_dual : ∀ σ τ ρ, (σ ≤ ρ) ∨ (τ ≤ ρ) ⇒ σ ∩ τ ≤ ρ.
    Proof with auto with SubtypeHints.
      intros σ τ ? [? | ?];
        [transitivity σ | transitivity τ]...
    Qed.

    Fact Union_sup : ∀ σ τ ρ, σ ≤ ρ ⇒ τ ≤ ρ ⇒ σ ∪ τ ≤ ρ.
    Proof with auto with SubtypeHints.
      intros.
      transitivity (ρ ∪ ρ)...
    Qed.
    Hint Resolve Union_sup : SubtypeHints.

    Fact Union_sup' : ∀ σ τ ρ, σ ∪ τ ≤ ρ ⇒ (σ ≤ ρ) ∧ (τ ≤ ρ).
    Proof with auto with SubtypeHints.
      intros; split;
        etransitivity;
        try eassumption...
    Qed.

    (* Don't put it in auto or it may be slow *)
    Fact Union_sup_dual : ∀ σ τ ρ, (σ ≤ τ) ∨ (σ ≤ ρ) ⇒ σ ≤ τ ∪ ρ.
    Proof with auto with SubtypeHints.
      intros ? τ ρ [? | ?];
        [transitivity τ | transitivity ρ]...
    Qed.

    Fact OmegaArrow : ∀ σ τ, ω ≤ τ ⇒ ω ≤ σ ⟶ τ.
    Proof with auto with SubtypeHints.
      intro; transitivity (ω ⟶ ω)...
    Qed.
    Hint Resolve OmegaArrow : SubtypeHints.

    Fact UnionInterDistrib : ∀ σ τ ρ, (σ ∪ τ) ∩ (σ ∪ ρ) ≤ σ ∪ (τ ∩ ρ).
    Proof with auto with SubtypeHints.
      intros.
      etransitivity; [apply R_InterUnionDistrib|]...
      apply Union_sup; [apply Union_sup_dual|]...
      transitivity (ρ ∩ (σ ∪ τ))...
      etransitivity; [apply R_InterUnionDistrib|]...
    Qed.
    Hint Resolve UnionInterDistrib : SubtypeHints.

    (* For more tactics, we show the operators are compatible with the relations *)
    Instance Inter_Proper_ST : Proper ((≤) ==> (≤) ==> (≤)) (∩).
    Proof with auto with SubtypeHints.
      compute...
    Qed.

    Instance Union_Proper_ST : Proper ((≤) ==> (≤) ==> (≤)) (∪).
    Proof with auto with SubtypeHints.
      compute...
    Qed.

    Instance Arr_Proper_ST : Proper (transp _ (≤) ==> (≤) ==> (≤)) (⟶).
    Proof with auto with SubtypeHints.
      compute...
    Qed.

    Instance Inter_Proper_EQ : Proper ((~=) ==> (~=) ==> (~=)) (∩).
    Proof with auto with SubtypeHints.
      compute...
    Qed.

    Instance Union_Proper_EQ : Proper ((~=) ==> (~=) ==> (~=)) (∪).
    Proof with auto with SubtypeHints.
      compute...
    Qed.

    Instance Arr_Proper_EQ : Proper ((~=) ==> (~=) ==> (~=)) (⟶).
    Proof with auto with SubtypeHints.
      compute...
    Qed.

    (* Help auto use these properties *)
    Hint Extern 2 (?R _ _ ~= ?R _ _) =>
    lazymatch R with
    | (∩) => apply Inter_Proper_EQ
    | (∪) => apply Union_Proper_EQ
    | (⟶) => apply Arr_Proper_EQ
    end : SubtypeHints.

    (* Ask auto to automatically simplify the hypotheses *)
    Hint Extern 1 (_ ≤ _) =>
    lazymatch goal with
    | H : ω ≤ _ |- _ => try rewrite <- H; (clear H) + (try rewrite <- H in *; clear H)
    | H : ?σ ≤ ?τ ∩ ?ρ |- _ => apply Inter_inf' in H; destruct H
    | H : ?σ ∪ ?τ ≤ ?ρ |- _ => apply Union_sup' in H; destruct H
    end : SubtypeHints.

    (* Ask auto to use preorder if the goal is atomic *)
    Hint Extern 300 (?σ ≤ ?τ) =>
    lazymatch σ with
    | _ _ _ => fail
    | _ => lazymatch τ with
           | _ _ _ => fail
           | _ => preorder
           end
    end : SubtypeHints.

    (* ~=-related facts *)
    Fact InterArrowEquiv : ∀ σ1 σ2 τ ρ1 ρ2, σ1 ~= τ ⟶ ρ1 ⇒ σ2 ~= τ ⟶ ρ2 ⇒ σ1 ∩ σ2 ~= τ ⟶ ρ1 ∩ ρ2.
    Proof.
      intros ? ? ? ? ? H H'.
      rewrite H, H'.
      auto with SubtypeHints.
    Qed.
    Hint Resolve InterArrowEquiv : SubtypeHints.

    Fact UnionArrowEquiv : ∀ σ1 σ2 τ1 τ2 ρ, σ1 ~= τ1 ⟶ ρ ⇒ σ2 ~= τ2 ⟶ ρ ⇒ σ1 ∩ σ2 ~= τ1 ∪ τ2 ⟶ ρ.
    Proof.
      intros ? ? ? ? ? H H'.
      rewrite H, H'.
      auto with SubtypeHints.
    Qed.
    Hint Resolve UnionArrowEquiv : SubtypeHints.

    Fact UnionEquiv1 : ∀ σ1 σ2 τ1 τ2 τ3, σ1 ~= τ1 ∪ τ2 ⇒ σ2 ~= τ1 ∪ τ3 ⇒ σ1 ∩ σ2 ~= τ1 ∪ (τ2 ∩ τ3).
    Proof.
      intros ? ? ? ? ? H H'.
      rewrite H, H'.
      auto with SubtypeHints.
    Qed.
    Hint Resolve UnionEquiv1 : SubtypeHints.

    Fact UnionEquiv2 : ∀ σ1 σ2 τ1 τ2 τ3, σ1 ~= τ1 ∪ τ3 ⇒ σ2 ~= τ2 ∪ τ3 ⇒ σ1 ∩ σ2 ~= (τ1 ∩ τ2) ∪ τ3.
    Proof.
      intros ? ? ? ? ? H H'.
      rewrite H, H'.
      transitivity (τ3 ∪ (τ1 ∩ τ2)); auto with SubtypeHints.
    Qed.
    Hint Resolve UnionEquiv2 : SubtypeHints.

    Fact InterEquiv1 : ∀ σ1 σ2 τ1 τ2 τ3, σ1 ~= τ1 ∩ τ2 ⇒ σ2 ~= τ1 ∩ τ3 ⇒ σ1 ∪ σ2 ~= τ1 ∩ (τ2 ∪ τ3).
    Proof.
      intros ? ? ? ? ? H H'.
      rewrite H, H'.
      auto with SubtypeHints.
    Qed.
    Hint Resolve InterEquiv1 : SubtypeHints.

    Fact InterEquiv2 : ∀ σ1 σ2 τ1 τ2 τ3, σ1 ~= τ1 ∩ τ3 ⇒ σ2 ~= τ2 ∩ τ3 ⇒ σ1 ∪ σ2 ~= (τ1 ∪ τ2) ∩ τ3.
    Proof.
      intros ? ? ? ? ? H H'.
      rewrite H, H'.
      transitivity (τ3 ∩ (τ1 ∪ τ2)); auto with SubtypeHints.
    Qed.
    Hint Resolve InterEquiv2 : SubtypeHints.

    Hint Extern 1 (_ ~= _ ) =>
    repeat lazymatch goal with
           | H : ?x ~= ω |- context[?x] => rewrite H; clear H
           | H : ω ~= ?x |- context[?x] => rewrite <- H; clear H
           | H : ?x ~= _ |- context[?x] => rewrite H; clear H
           end : SubtypeHints.

    (* Syntactical predicates on terms *)

    (* Generalized intersection and union *)
    Inductive Generalize (c : term ⇒ term ⇒ term) (P : term ⇒ Prop) : term ⇒ Prop :=
    | G_nil : ∀ σ, P σ ⇒ Generalize c P σ
    | G_cons : ∀ σ τ, Generalize c P σ ⇒ Generalize c P τ ⇒ Generalize c P (c σ τ).
    Hint Constructors Generalize : SubtypeHints.

    (* Notations: [ ⋂ P ] x means x is a generalized intersection of terms verifying P *)
    Notation "[ ⋂ P ]" := (Generalize (∩) P).
    Notation "[ ⋃ P ]" := (Generalize (∪) P).

    Fact general_inheritance : ∀ f g P s, Generalize f P s ⇒ Generalize f (Generalize g P) s.
    Proof.
      intros ? ? ? ? H; induction H.
      - constructor; constructor; assumption.
      - constructor 2; assumption.
    Qed.
    Hint Resolve general_inheritance : SubtypeHints.

    (* Arrow Normal Form *)
    Inductive ANF : term ⇒ Prop :=
    | VarisANF : ∀ α, ANF (Var α)
    | ArrowisANF : ∀ σ τ, [⋂ ANF] σ ⇒ [⋃ ANF] τ ⇒ ANF (σ ⟶ τ)
    | ArrowisANF' : ∀ τ, [⋃ ANF] τ ⇒ ANF (ω ⟶ τ).
    Hint Constructors ANF : SubtypeHints.

    (* Conjunctive/Disjunctive Normal Forms *)
    Definition CANF (σ : term) : Prop := [⋂ [⋃ ANF]] σ ∨ σ = ω.
    Definition DANF (σ : term) : Prop := [⋃ [⋂ ANF]] σ ∨ σ = ω.
    Hint Unfold CANF : SubtypeHints.
    Hint Unfold DANF : SubtypeHints.

    (* Terms without Omega (with one exception, in Of_Arrow1) *)
    Inductive Omega_free : term ⇒ Prop :=
    | Of_Var : ∀ α, Omega_free (Var α)
    | Of_Union : ∀ σ τ, Omega_free σ ⇒ Omega_free τ ⇒ Omega_free (σ ∪ τ)
    | Of_Inter : ∀ σ τ, Omega_free σ ⇒ Omega_free τ ⇒ Omega_free (σ ∩ τ)
    | Of_Arrow1 : ∀ σ, Omega_free σ ⇒ Omega_free (ω ⟶ σ)
    | Of_Arrow2 : ∀ σ τ, Omega_free σ ⇒ Omega_free τ ⇒ Omega_free (σ ⟶ τ).
    Hint Constructors Omega_free : SubtypeHints.
    Hint Extern 1 =>
    match goal with
    | H : Omega_free ω |- _ => inversion H
    | H : Omega_free (_ _ _) |- _ => inv H
    end : SubtypeHints.

    (* Terms on which we'll define filters *)
    Unset Elimination Schemes.
    Inductive isFilter : term ⇒ Prop :=
    | OmegaisFilter : isFilter ω
    | VarisFilter : ∀ α, isFilter (Var α)
    | ArrowisFilter : ∀ σ τ, isFilter (σ ⟶ τ)
    | InterisFilter : ∀ σ τ, isFilter σ ⇒ isFilter τ ⇒ isFilter (σ ∩ τ).
    Set Elimination Schemes.
    Hint Constructors isFilter : SubtypeHints.

    Fact InterANF_isFilter : ∀ σ, [ ⋂ ANF] σ ⇒ isFilter σ.
    Proof.
      induction 1 as [? H|].
      inversion H; auto with SubtypeHints.
      constructor; trivial.
    Qed.
    Hint Extern 0 (isFilter ?σ) =>
    match goal with
    | H : [ ⋂ ANF] σ |- _ => apply InterANF_isFilter
    end : SubtypeHints.

    (* Huge tactics that deals with these forms *)
    Ltac decide_nf :=
      try (lazymatch goal with
           | H : ANF _ |- _ => idtac
           | H : Generalize _ _ _ |- _ => idtac
           | H : CANF _ |- _ => idtac
           | H : DANF _ |- _ => idtac
           | _ => fail
           end;
           repeat lazymatch goal with
                  | H : DANF (_ _ _) |- _ => inversion H as [?|H']; [|inversion H']; subst; clear H
                  | H : CANF (_ _ _) |- _ => inversion H as [?|H']; [|inversion H']; subst; clear H
                  | H : [⋃ ANF] (_ ∪ _) |- _ => inversion H as [? H'|]; [inversion H'|]; subst; clear H
                  | H : [⋃ [⋂ ANF]] (_ ∪ _) |- _ => inversion H as [? H'|];
                                                    [inversion H' as [? H''|]; inversion H''|];
                                                    subst; clear H
                  | H : [⋃ _] (_ ∩ _) |- _ => inv H
                  | H : [⋃ _] (_ ⟶ _) |- _ => inv H
                  | H : [⋃ _] (Var _) |- _ => inv H
                  | H : [⋃ _] ω |- _ => inv H
                  | H : [⋂ ANF] (_ ∩ _) |- _ => inversion H as [? H'|]; [inversion H'|]; subst; clear H
                  | H : [⋂ [⋃ ANF]] (_ ∩ _) |- _ => inversion H as [? H'|];
                                                    [inversion H' as [? H''|]; inversion H''|];
                                                    subst; clear H
                  | H : [⋂ _] (_ ∪ _) |- _ => inv H
                  | H : [⋂ _] (_ ⟶ _) |- _ => inv H
                  | H : [⋂ _] (Var _) |- _ => inv H
                  | H : [⋂ _] ω |- _ => inv H
                  | H : ANF (ω ⟶ _) |- _ => inversion H as [|? ? H'|];
                                            [inversion H' as [? H''|]; inversion H''|]; subst; clear H
                  | H : ANF (_ ⟶ _) |- _ => inv H
                  | H : ANF (_ ∩ _) |- _ => inversion H
                  | H : ANF (_ ∪ _) |- _ => inversion H
                  | H : ANF ω |- _ => inversion H
                  | H : Omega_free (_ _ _) |- _ => inv H
                  end);
      repeat lazymatch goal with
             | H : ?x |- ?x => assumption
             | |- [⋃ _] (_ ∪ _) => apply G_cons
             | |- [⋃ _] _ => apply G_cons
             | |- [⋂ _] (_ ∩ _) => apply G_cons
             | |- [⋂ _] _ => apply G_nil
             | |- ANF (Var _) => constructor
             | |- ANF (ω ⟶ _) => apply ArrowisANF'
             | |- ANF (_ ⟶ _) => constructor
             | |- CANF ω => right; reflexivity
             | |- DANF ω => right; reflexivity
             | |- CANF (Var _) => left; repeat constructor
             | |- DANF (Var _) => left; repeat constructor
             | |- CANF (_ _ _) => left
             | |- DANF (_ _ _) => left
             end.
    Hint Extern 1 (CANF _) => decide_nf : SubtypeHints.
    Hint Extern 1 (DANF _) => decide_nf : SubtypeHints.
    Hint Extern 1 (ANF _) => decide_nf : SubtypeHints.
    Hint Extern 1 (Generalize _ _ _) => decide_nf : SubtypeHints.

    (* The recursion scheme for isFilter uses P ω as an inductive hypothesis *)
    Lemma isFilter_ind : ∀ P : term ⇒ Prop,
        P ω ⇒
        (∀ α : 𝕍.t, P ω ⇒ P (Var α)) ⇒
        (∀ σ τ : term, P ω ⇒ P (σ ⟶ τ)) ⇒
        (∀ σ τ : term, isFilter σ ⇒ P σ ⇒ isFilter τ ⇒ P τ ⇒ P ω ⇒ P (σ ∩ τ)) ⇒
        ∀ σ : term, isFilter σ ⇒ P σ.
    Proof.
      intros P fω fα fA fI.
      exact (fix foo σ Fσ : P σ := match Fσ in isFilter σ return P σ with
                                   | OmegaisFilter => fω
                                   | VarisFilter α => fα α fω
                                   | ArrowisFilter σ τ => fA σ τ fω
                                   | InterisFilter σ τ Fσ Fτ => fI σ τ Fσ (foo σ Fσ) Fτ (foo τ Fτ) fω
                                   end).
    Qed.

    (* Recursion scheme for [⋃ ANF] *)
    Lemma Uanf_ind : ∀ P : term ⇒ Prop,
        (∀ α, P (Var α)) ⇒
        (∀ σ τ, P σ ⇒ P τ ⇒ P (σ ∪ τ)) ⇒
        (∀ σ τ, P τ ⇒ P (σ ⟶ τ)) ⇒
        (∀ σ, [⋃ ANF] σ ⇒ P σ).
      intros P fV fU fA.
      refine (fix foo (σ : term) := match σ with
                                    | Var α => λ _, fV α
                                    | σ ⟶ τ => λ pf, fA _ τ (foo τ _)
                                    | σ ∪ τ => λ pf, fU σ τ (foo σ _) (foo τ _)
                                    | σ ∩ τ => λ pf, _
                                    | ω => λ pf, _
                                    end);
        try(inversion pf as [? pf'|]; inv pf'); decide_nf.
    Qed.
    Ltac uanf_ind σ :=
      let foo HH :=
          repeat match goal with
                 | H : context[σ] |- _ => lazymatch H with
                                          | HH => fail
                                          | _ => revert H
                                          end
                 end;
          revert HH; revert σ;
          refine (Uanf_ind _ _ _ _); intros
      in
      lazymatch goal with
      | HH : [⋃ ANF] σ |- _ => foo HH
      | _ =>
        assert (HH : [⋃ ANF] σ) by (auto with SubtypeHints);
        foo HH
      end.

    (* Filters and ideals *)
    Reserved Notation "↑[ σ ] τ" (at level 65).
    Reserved Notation "↓[ σ ] τ" (at level 65).
    Inductive Filter : term ⇒ term ⇒ Prop :=
    | F_Refl : ∀ σ : term, isFilter σ ⇒ ↑[σ] σ
    | F_Inter : ∀ σ τ ρ : term, ↑[σ] τ ⇒ ↑[σ] ρ ⇒ ↑[σ] τ ∩ ρ
    | F_Union1 : ∀ σ τ ρ : term, ↑[σ] τ ⇒ ↑[σ] τ ∪ ρ
    | F_Union2 : ∀ σ τ ρ : term, ↑[σ] ρ ⇒ ↑[σ] τ ∪ ρ
    | F_Arrow1 : ∀ σ1 σ2 τ1 τ2 : term, σ2 ≤ σ1 ⇒ τ1 ≤ τ2 ⇒ ↑[σ1 ⟶ τ1] σ2 ⟶ τ2
    | F_Arrow2 : ∀ σ1 σ2 τ1 τ2 ρ1 ρ2 : term, ↑[σ1 ∩ σ2] τ1 ⟶ ρ1 ⇒ τ2 ≤ τ1 ⇒ ρ1 ≤ ρ2 ⇒ ↑[σ1 ∩ σ2] τ2 ⟶ ρ2
    | F_OmegaTopV : ∀ (α : 𝕍.t) (τ : term), ↑[ω] τ ⇒ ↑[Var α] τ
    | F_OmegaTopA : ∀ σ1 σ2 τ : term, ↑[ω] τ ⇒ ↑[σ1 ⟶ σ2] τ
    | F_OmegaTopI : ∀ σ1 σ2 τ : term, isFilter (σ1 ∩ σ2) ⇒ ↑[ω] τ ⇒ ↑[σ1 ∩ σ2] τ
    | F_Omega : ∀ σ τ : term, ↑[ω] τ ⇒ ↑[ω] σ ⟶ τ
    | F_Inter1 : ∀ σ1 σ2 τ : term, isFilter σ2 ⇒ ↑[σ1] τ ⇒ ↑[σ1 ∩ σ2] τ
    | F_Inter2 : ∀ σ1 σ2 τ : term, isFilter σ1 ⇒ ↑[σ2] τ ⇒ ↑[σ1 ∩ σ2] τ
    | F_ArrowInter : ∀ σ1 σ2 τ ρ1 ρ2 : term, ↑[σ1 ∩ σ2] (τ ⟶ ρ1) ∩ (τ ⟶ ρ2) ⇒ ↑[σ1 ∩ σ2] τ ⟶ ρ1 ∩ ρ2
    | F_ArrowUnion : ∀ σ1 σ2 τ1 τ2 ρ : term, ↑[σ1 ∩ σ2] (τ1 ⟶ ρ) ∩ (τ2 ⟶ ρ) ⇒ ↑[σ1 ∩ σ2] τ1 ∪ τ2 ⟶ ρ
    where "↑[ σ ] τ" := (Filter σ τ).
    Hint Constructors Filter : SubtypeHints.

    Inductive Ideal : term ⇒ term ⇒ Prop :=
    | I_Refl : ∀ σ : term,  [⋃ ANF] σ ⇒ ↓[σ] σ
    | I_Inter1 : ∀ σ τ ρ : term, ↓[σ] τ ⇒ ↓[σ] τ ∩ ρ
    | I_Inter2 : ∀ σ τ ρ : term, ↓[σ] ρ ⇒ ↓[σ] τ ∩ ρ
    | I_Union : ∀ σ τ ρ : term, ↓[σ] τ ⇒ ↓[σ] ρ ⇒ ↓[σ] τ ∪ ρ
    | I_Arrow1 : ∀ σ1 σ2 τ1 τ2 : term, [⋂ ANF] σ1 ⇒ ↑[σ1] σ2 ⇒ ↓[τ1] τ2 ⇒ ↓[σ1 ⟶ τ1] σ2 ⟶ τ2
    | I_Arrow2 : ∀ σ τ1 τ2 : term, ↑[ω] σ ⇒ ↓[τ1] τ2 ⇒ ↓[ω ⟶ τ1] σ ⟶ τ2
    | I_Union1 : ∀ σ1 σ2 τ : term, [⋃ ANF] σ2 ⇒ ↓[σ1] τ ⇒ ↓[σ1 ∪ σ2] τ
    | I_Union2 : ∀ σ1 σ2 τ : term, [⋃ ANF] σ1 ⇒ ↓[σ2] τ ⇒ ↓[σ1 ∪ σ2] τ
    where "↓[ σ ] τ" := (Ideal σ τ).
    Hint Constructors Ideal : SubtypeHints.

    (* Correctness of filters and ideals *)
    Theorem Filter_correct : ∀ σ τ, ↑[σ] τ ⇒ σ ≤ τ.
    Proof with auto using Inter_inf_dual, Union_sup_dual with SubtypeHints.
      intros ? ? H.
      induction H...
      - etransitivity; [eassumption|]...
      - etransitivity; [|apply R_InterDistrib]...
      - etransitivity; [|apply R_UnionDistrib]...
    Qed.
    Hint Resolve Filter_correct : SubtypeHints.
    Hint Extern 1 (_ ≤ _) =>
    lazymatch goal with
    | H : ↑[ω] _ |- _ => apply (Filter_correct) in H; try rewrite <- H; (clear H) + (try rewrite <- H in *; clear H)
    end : SubtypeHints.

    Theorem Ideal_correct : ∀ σ τ, ↓[σ] τ ⇒ τ ≤ σ.
    Proof with auto using Inter_inf_dual, Union_sup_dual with SubtypeHints.
      intros ? ? H.
      induction H...
    Qed.
    Hint Resolve Ideal_correct : SubtypeHints.

    (* Filters and ideals have some normal form *)
    Lemma Filter_isFilter: ∀ σ τ, ↑[σ] τ ⇒ isFilter σ.
    Proof.
      intros ? ? H; induction H; auto; constructor; auto.
    Qed.
    Hint Extern 0 (isFilter ?σ) =>
      match goal with
      | H : ↑[?σ] _ |- _ => apply (Filter_isFilter _ _ H)
      end : SubtypeHints.

    Lemma Ideal_isDANF: ∀ σ τ, ↓[σ] τ ⇒ [⋃ ANF] σ.
    Proof.
      intros ? ? H; induction H; auto with SubtypeHints.
    Qed.
    Hint Resolve Ideal_isDANF : SubtypeHints.
    Hint Extern 0 ([⋃ ANF] ?σ) =>
      match goal with
      | H : ↓[?σ] _ |- _ => apply (Ideal_isDANF _ _ H)
      end : SubtypeHints.

    (* Tactic: cast ρ to σ in filter (or ideals) (may produce new goals) *)
    Ltac cast_filter ρ σ :=
      lazymatch σ with
      | ω => match ρ with
             | Var _ => apply F_OmegaTopV
             | _ ⟶ _ => apply F_OmegaTopA
             | _ ∩ _ => apply F_OmegaTopI
             end
      | _ => lazymatch ρ with
             | σ ∩ _ => apply F_Inter1
             | _ ∩ σ => apply F_Inter2
             end
      end.
    Ltac cast_ideal ρ σ :=
      lazymatch ρ with
      | σ ∪ _ => apply I_Union1
      | _ ∪ σ => apply I_Union2
      end.

    (* Helper lemmas to destruct filter and ideal hypotheses *)
    Lemma FilterInter : ∀ σ τ ρ, ↑[σ] τ ∩ ρ ⇒ ↑[σ] τ ∧ ↑[σ] ρ.
      intros ? ? ? H.
      assert (Fσ : isFilter σ) by (auto with SubtypeHints).
      induction Fσ; split; inv H;
        auto with SubtypeHints;
        lazymatch goal with
        (* Inductive case *)
        | IH : ↑[?σ] ?τ ⇒ _, H : ↑[?σ] ?τ |- ↑[?ρ] _ =>
          (* cast ρ to σ *)
          cast_filter ρ σ; trivial;
            (* apply the inductive hypothesis *)
            apply IH; trivial
        end.
    Qed.

    Lemma IdealInter : ∀ σ τ ρ, ↓[σ] τ ∩ ρ ⇒ ↓[σ] τ ∨ ↓[σ] ρ.
      intros ? ? ? H.
      assert (Iσ : [⋃ ANF] σ) by (auto with SubtypeHints).
      induction Iσ; inv H; auto with SubtypeHints; decide_nf;
        lazymatch goal with
        (* Inductive case *)
        | IH : ↓[?σ] ?τ1 ∩ ?τ2 ⇒ ?prop, H : ↓[?σ] ?τ1 ∩ ?τ2 |- ↓[?ρ] ?τ1 ∨ ↓[?ρ] ?τ2 =>
          (* apply the inductive hypothesis *)
          destruct (IH H); [left|right];
            (* cast ρ to σ *)
            cast_ideal ρ σ; assumption
        end.
    Qed.

    Lemma FilterUnion : ∀ σ τ ρ, ↑[σ] τ ∪ ρ ⇒ ↑[σ] τ ∨ ↑[σ] ρ.
      intros ? ? ? H.
      assert (Fσ : isFilter σ) by (auto with SubtypeHints).
      induction Fσ; inv H; auto;
        lazymatch goal with
        (* Inductive case *)
        | IH : ↑[?σ] ?τ1 ∪ ?τ2 ⇒ ?prop, H : ↑[?σ] ?τ1 ∪ ?τ2 |- ↑[?ρ] ?τ1 ∨ ↑[?ρ] ?τ2 =>
          (* apply the inductive hypothesis *)
          destruct (IH H); [left|right];
            (* cast ρ to σ *)
            cast_filter ρ σ; assumption
        end.
    Qed.

    Lemma IdealUnion : ∀ σ τ ρ, ↓[σ] τ ∪ ρ ⇒ ↓[σ] τ ∧ ↓[σ] ρ.
      intros ? ? ? H.
      assert (Iσ : [⋃ ANF] σ) by (auto with SubtypeHints).
      induction Iσ; split; inv H;
        auto with SubtypeHints; decide_nf;
          lazymatch goal with
          (* Inductive case *)
          | IH : ↓[?σ] ?τ ⇒ _, H : ↓[?σ] ?τ |- ↓[?ρ] _ =>
            (* cast ρ to σ *)
            cast_ideal ρ σ; trivial;
              (* apply the inductive hypothesis *)
              apply IH; trivial
          end.
    Qed.

    Lemma FilterArrow : ∀ σ σ' τ τ', ↑[σ ⟶ σ'] τ ⟶ τ' ⇒ (↑[ω] τ ⟶ τ' ∨ (τ ≤ σ  ∧ σ' ≤ τ')).
    Proof.
      intros ? ? ? ? H; inv H; auto 3 with SubtypeHints.
    Qed.

    Lemma Filter_omega : ∀ σ τ, isFilter σ ⇒ ↑[ω] τ ⇒ ↑[σ] τ.
    Proof.
      induction 1; auto with SubtypeHints.
    Qed.

    Lemma IdealnoOmega : ∀ σ, ¬ ↓[ σ] ω.
    Proof.
      induction σ; intro H; inv H;
        auto with SubtypeHints; decide_nf.
    Qed.

    Lemma IdealnoOmegaArrow : ∀ σ, ¬ ↓[ σ] ω ⟶ ω.
    Proof.
      induction σ; intro H; inv H;
        auto with SubtypeHints; decide_nf;
        eapply IdealnoOmega; eassumption.
    Qed.

    Hint Extern 1 =>
    lazymatch goal with
    | H : ↑[?σ ∩ ?τ] (?ρ ⟶ _) ∩ (?ρ ⟶ _) |- _ => apply F_ArrowInter in H
    | H : ↑[?σ ∩ ?τ] (_ ⟶ ?ρ) ∩ (_ ⟶ ?ρ) |- _ => apply F_ArrowUnion in H
    | H : ↑[_] _ ∪ _ |- _ => apply FilterUnion in H; destruct H
    | H : ↑[_] _ ∩ _ |- _ => apply FilterInter in H; destruct H
    | H : ↑[_ ⟶ _] _ ⟶ _ |- _ => apply FilterArrow in H; destruct H as [|[ ]]
    | H : ↑[ω] _ ⟶ _ |- _ => inv H
    | H : ↑[Var _] _ ⟶ _ |- _ => inv H
    end : SubtypeHints.

    Ltac destruct_ideal :=
      repeat lazymatch goal with
             | H : ↓[_] ω |- _ => apply IdealnoOmega in H; exfalso; trivial
             | H : ↓[_] ω ⟶ ω |- _ => apply IdealnoOmegaArrow in H; exfalso; trivial
             | H : ↓[_] _ ∪ _ |- _ => apply IdealUnion in H; destruct H
             | H : ↓[_] _ ∩ _ |- _ => apply IdealInter in H; destruct H
             | H : ↓[_ ∪ _] _ ⟶ _ |- _ => inv H
             | H : ↓[_ ⟶ _] _ ⟶ _ |- _ => inv H
             | H : ↓[Var _] _ ⟶ _ |- _ => inv H
             end.

    Lemma FilterArrow' : ∀ σ τ' ρ, ↑[ σ] τ' ⟶ ρ ⇒ ∀ τ ρ', τ ≤ τ' ⇒ ρ ≤ ρ' ⇒ ↑[ σ] τ ⟶ ρ'.
    Proof.
      intros ? ? ? H.
      assert (Fσ : isFilter σ) by (auto with SubtypeHints).
      induction Fσ.
      - intros ? ? ? H1.
        constructor; inv H.
        induction H1; auto 10 with SubtypeHints.
      - auto with SubtypeHints.
      - apply FilterArrow in H; destruct H as [|[ ]]; auto with SubtypeHints.
      - eauto with SubtypeHints.
    Qed.

    (* Main properties: filters (resp. ideal) are closed by upcasting (resp. downcasting) *)
    (* As a result, we get completeness of filters and ideals *)
    Lemma Filter_closed : ∀ σ τ1 τ2,
        ↑[σ] τ1 ⇒ τ1 ≤ τ2 ⇒ ↑[σ] τ2.
    Proof.
      induction 2; auto with SubtypeHints;
        solve [eapply FilterArrow'; eassumption|
               apply Filter_omega; auto with SubtypeHints|
               assert (Fσ : isFilter σ) by (auto with SubtypeHints);
               induction Fσ; auto 10 with SubtypeHints].
    Qed.
    Hint Extern 0 (↑[?σ] ?τ2) =>
    lazymatch goal with
    | H : ↑[σ] ?τ1, H' : ?τ1 ≤ τ2 |- ↑[σ] τ2 => apply (Filter_closed _ _ _ H H')
    end : SubtypeHints.

    Theorem Filter_complete : ∀ σ, isFilter σ ⇒ ∀ τ, σ ≤ τ ⇒ ↑[σ] τ.
    Proof.
      intros; eapply Filter_closed; try eassumption.
      apply F_Refl; assumption.
    Qed.
    Hint Resolve Filter_complete : SubtypeHints.

    Section Ideal_closed.
      (* This hint is local to the section; and help use the inductive hypotheses *)
      Hint Extern 1 (↓[?ρ] _) =>
      (* Because of a bug in auto, auto fails to use the generated hypothesis; so foo helps it *)
      let foo σ HHH :=
          lazymatch ρ with
          | _ ∪ _ => cast_ideal ρ σ; trivial; apply HHH
          | ω ⟶ _ => apply I_Arrow2; [|apply HHH]
          | _ ⟶ _ => apply I_Arrow1; [| |apply HHH]
          end
      in
      (* The variable τ of the inductive hypothesis cannot be infered by auto,
         so this tactic instantiates it *)
      lazymatch goal with
      | H : ∀ τ, ↓[?σ] τ ⇒ ∀ τ' : term, τ' ≤ τ ⇒ ↓[?σ] τ', H' : ↓[?σ] ?τ |- _ =>
      assert (HHH : ∀ τ' : term, τ' ≤ τ ⇒ ↓[ σ] τ') by (exact (H τ H')); clear H H'; foo σ HHH
    | H : ∀ τ, ↓[?σ] τ ⇒ ∀ τ' : term, τ' ≤ τ ⇒ ↓[?σ] τ', H' : ?τ ≤ ?σ |- _ =>
      assert (HHH : ↓[ σ] τ) by (refine (H _ (I_Refl _ _) _ H'); trivial); clear H H'; foo σ HHH
      end.

      Lemma Ideal_closed : ∀ σ, [⋃ ANF] σ ⇒ ∀ τ1, ↓[σ] τ1 ⇒ ∀ τ2, τ2 ≤ τ1 ⇒ ↓[σ] τ2.
      Proof.
        intros until 1; uanf_ind σ;
          lazymatch goal with
          | H : _ ≤ _ |- _ => induction H;
                                destruct_ideal;
                                decide_nf;
                                auto with SubtypeHints
          end.
      Qed.
    End Ideal_closed.

    Theorem Ideal_complete : ∀ σ, [⋃ ANF] σ ⇒ ∀ τ, τ ≤ σ ⇒ ↓[σ] τ.
    Proof.
      intros; eapply Ideal_closed; try eassumption.
      apply I_Refl; assumption.
    Qed.

    (* Now we can use filters and ideals to prove lemmas about subtyping *)
    Lemma Omega_free_Omega : ∀ s, Omega_free s ⇒ ¬ s ~= Omega.
    Proof.
      intros ? H [_ H2].
      apply Filter_complete in H2; trivial with SubtypeHints.
      induction s; inv H; inv H2; auto with SubtypeHints.
    Qed.

    Lemma Omega_IUANF : ∀ σ, [ ⋂ [ ⋃ ANF]] σ ⇒ ¬ ω ≤ σ.
    Proof.
      induction σ as [|? H1 ? H2|? H1 ? H2|? H1 ? H2|];
        intros; intro Hyp; (apply Filter_complete in Hyp; [|constructor]); inv Hyp;
          solve [apply H2; auto 2 with SubtypeHints|
                 apply H1; auto 2 with SubtypeHints|
                 decide_nf].
    Qed.

    (* Rewriting functions *)

    (* First rewriting function: do Omega-related simplifications *)
    Fixpoint deleteOmega (σ : term) : {τ | τ ~= σ ∧ (Omega_free τ ∨ τ = ω)}.
      refine(match σ with
             | σ ⟶ τ => let (σ,pfσ) := deleteOmega σ in
                        let (τ,pfτ) := deleteOmega τ in
                        match τ as x return τ = x ⇒ _ with
                        | ω => λ _, exist _ ω _
                        | _ => λ _, exist _ (σ ⟶ τ) _
                        end eq_refl
             | σ ∩ τ => let (σ,pfσ) := deleteOmega σ in
                        let (τ,pfτ) := deleteOmega τ in
                        match σ as x return σ = x ⇒ _ with
                        | ω => λ _, exist _ τ _
                        | _ => λ _, match τ as x return τ = x ⇒ _ with
                                    | ω => λ _, exist _ σ _
                                        | _ => λ _, exist _ (σ ∩ τ) _
                                        end eq_refl
                        end eq_refl
             | σ ∪ τ => let (σ,pfσ) := deleteOmega σ in
                        let (τ,pfτ) := deleteOmega τ in
                        match σ as x return σ = x ⇒ _ with
                        | ω => λ _, exist _ ω _
                        | _ => λ _, match τ as x return τ = x ⇒ _ with
                                        | ω => λ _, exist _ ω _
                                        | _ => λ _, exist _ (σ ∪ τ) _
                                        end eq_refl
                        end eq_refl
             | Var α => exist _ (Var α) _
             | ω => exist _ ω _
             end); clear deleteOmega; subst; simpl in *;
        first[destruct pfσ as [? [|]];
              destruct pfτ as [? [|]]; subst|
              auto with SubtypeHints];
        first[match goal with | H : Omega_free ω |- _ => inversion H end|
              discriminate|
              split; auto with SubtypeHints].
    Defined.

    (* Distribution functions *)
    Fixpoint distrArrow (σ τ : term) (pfσ : [⋃ [⋂ ANF]] σ ∨ σ = ω) (pfτ : [⋂ [⋃ ANF]] τ) :
      {σ' | σ' ~= σ ⟶ τ ∧ [⋂ ANF] σ'}.
      refine(match σ as x return σ = x ⇒ _ with
             | σ1 ∪ σ2 => λ _, let (σ1,pfσ1) := distrArrow σ1 τ _ _ in
                                   let (σ2,pfσ2) := distrArrow σ2 τ _ _ in
                                   exist _ (σ1 ∩ σ2) _
             | _ => λ _,
                      (fix distrArrow' σ τ (pfσ:[⋂ ANF] σ ∨ σ = ω) (pfτ:[⋂ [⋃ ANF]] τ) : {σ' | σ' ~= σ ⟶ τ ∧ [⋂ ANF] σ'} :=
                         match τ as x return τ = x ⇒ _ with
                         | τ1 ∩ τ2 => λ _, let (τ1,pfτ1) := distrArrow' σ τ1 _ _ in
                                               let (τ2,pfτ2) := distrArrow' σ τ2 _ _ in
                                               exist _ (τ1 ∩ τ2) _
                         | _ => λ _, exist _ (σ ⟶ τ) _
                         end eq_refl) σ τ _ pfτ
             end eq_refl); subst; (destruct pfσ; [|try discriminate]); simpl in *;
        auto with SubtypeHints.
    Defined.

    Fixpoint distrUnion (σ τ : term) (pfσ : [⋂ [⋃ ANF]] σ) (pfτ : [⋂ [⋃ ANF]] τ) :
      {σ' | σ' ~= σ ∪ τ ∧ [⋂ [⋃ ANF]] σ'}.
      refine(match σ as x return σ = x ⇒ _ with
             | σ1 ∩ σ2 => λ _, let (σ1,pfσ1) := distrUnion σ1 τ _ _ in
                                   let (σ2,pfσ2) := distrUnion σ2 τ _ _ in
                                   exist _ (σ1 ∩ σ2) _
             | _ => λ _,
                      (fix distrUnion' σ τ (pfσ:[⋃ ANF] σ) (pfτ:[⋂ [⋃ ANF]] τ) : {σ' | σ' ~= σ ∪ τ ∧ [⋂ [⋃ ANF]] σ'} :=
                         match τ as x return τ = x ⇒ _ with
                         | τ1 ∩ τ2 => λ _, let (τ1,pfτ1) := distrUnion' σ τ1 _ _ in
                                               let (τ2,pfτ2) := distrUnion' σ τ2 _ _ in
                                               exist _ (τ1 ∩ τ2) _
                         | _ => λ _, exist _ (σ ∪ τ) _
                         end eq_refl) σ τ _ pfτ
             end eq_refl); subst; simpl in *;
        auto with SubtypeHints.
    Defined.

    Fixpoint distrInter (σ τ : term) (pfσ : [⋃ [⋂ ANF]] σ) (pfτ : [⋃ [⋂ ANF]] τ) :
      {σ' | σ' ~= σ ∩ τ ∧ [⋃ [⋂ ANF]] σ'}.
      refine(match σ as x return σ = x ⇒ _ with
             | σ1 ∪ σ2 => λ _, let (σ1,pfσ1) := distrInter σ1 τ _ _ in
                                   let (σ2,pfσ2) := distrInter σ2 τ _ _ in
                                   exist _ (σ1 ∪ σ2) _
             | _ => λ _,
                      (fix distrInter' σ τ (pfσ:[⋂ ANF] σ) (pfτ:[⋃ [⋂ ANF]] τ) : {σ' | σ' ~= σ ∩ τ ∧ [⋃ [⋂ ANF]] σ'} :=
                         match τ as x return τ = x ⇒ _ with
                         | τ1 ∪ τ2 => λ _, let (τ1,pfτ1) := distrInter' σ τ1 _ _ in
                                               let (τ2,pfτ2) := distrInter' σ τ2 _ _ in
                                               exist _ (τ1 ∪ τ2) _
                         | _ => λ _, exist _ (σ ∩ τ) _
                         end eq_refl) σ τ _ pfτ
             end eq_refl); subst; simpl in *;
        auto with SubtypeHints.
    Defined.

    (* Mutually recursive functions for CANF and DANF *)
    Fixpoint _CANF  (σ : term) : (Omega_free σ ∨ σ = ω) ⇒ {τ | τ ~= σ ∧ CANF τ}
    with _DANF  (σ : term) : (Omega_free σ ∨ σ = ω) ⇒ {τ | τ ~= σ ∧ DANF τ}.
    Proof.
      - refine(match σ with
               | Var α => λ _, exist _ (Var α) _
               | σ ⟶ τ => λ pf,
                            let (σ,pfσ) := _DANF σ _ in
                            let (τ,pfτ) := _CANF τ _ in
                            let (σ',pfσ') := distrArrow σ τ _ _ in
                            exist _ σ' _
               | σ ∩ τ => λ pf,
                            let (σ,pfσ) := _CANF σ _ in
                            let (τ,pfτ) := _CANF τ _ in
                            exist _ (σ ∩ τ) _
               | σ ∪ τ => λ pf, let (σ,pfσ) := _CANF σ _ in
                                let (τ,pfτ) := _CANF τ _ in
                                let (σ',pfσ') := distrUnion σ τ _ _ in
                                exist _ σ' _
               | ω => λ _, exist _ ω _
               end); try (destruct pf; [|discriminate]); simpl in *;
          match goal with
          | |- _ ∨ _ => auto with SubtypeHints
          | |- _ ∧ _ => split; [trivial|]
          | _ => idtac
          end;
          try (destruct pfσ as [Hσ [?|?]]; [|subst; exfalso; match type of Hσ with
                                                             | ω ~= ?σ' => apply (Omega_free_Omega σ')
                                                             end; auto 2 with SubtypeHints; fail]);
          try (destruct pfτ as [Hτ [?|?]]; [|subst; exfalso; match type of Hτ with
                                                             | ω ~= ?τ' => apply (Omega_free_Omega τ')
                                                             end; auto 2 with SubtypeHints; fail]);
          auto with SubtypeHints.
      - refine(match σ with
               | Var α => λ _, exist _ (Var α) _
               | σ ⟶ τ => λ pf,
                            let (σ,pfσ) := _DANF σ _ in
                            let (τ,pfτ) := _CANF τ _ in
                            let (σ',pfσ') := distrArrow σ τ _ _ in
                            exist _ σ' _
               | σ ∪ τ => λ pf,
                            let (σ,pfσ) := _DANF σ _ in
                            let (τ,pfτ) := _DANF τ _ in
                            exist _ (σ ∪ τ) _
               | σ ∩ τ => λ pf,
                            let (σ,pfσ) := _DANF σ _ in
                            let (τ,pfτ) := _DANF τ _ in
                            let (σ',pfσ') := distrInter σ τ _ _ in
                            exist _ σ' _
               | ω => λ _, exist _ ω _
               end); try (destruct pf; [|discriminate]); simpl in *;
          match goal with
          | |- _ ∨ _ => auto with SubtypeHints
          | |- _ ∧ _ => split; [trivial|]
          | _ => idtac
          end;
          try (destruct pfσ as [Hσ [?|?]]; [|subst; exfalso; match type of Hσ with
                                                             | ω ~= ?σ' => apply (Omega_free_Omega σ')
                                                             end; auto 2 with SubtypeHints; fail]);
          try (destruct pfτ as [Hτ [?|?]]; [|subst; exfalso; match type of Hτ with
                                                             | ω ~= ?τ' => apply (Omega_free_Omega τ')
                                                             end; auto 2 with SubtypeHints; fail]);
          auto with SubtypeHints.
    Defined.

    (* Main subtyping algorithm *)
    Definition main_algo : ∀ pair : term * term,
        DANF (fst pair) ⇒ CANF (snd pair) ⇒
        {fst pair ≤ snd pair} + {¬ fst pair ≤ snd pair}.
      refine (Fix wf_main_algo _ _). intros [σ τ] rec.
      refine (match (σ,τ) as x return x = (σ,τ) ⇒ _ with
              | (_, ω) => λ eq _ _, left _
              | (ω, _) => λ eq _ Cτ, right _
              | (σ1 ∪ σ2, _) => λ eq _ _, match rec (σ1,τ) _ _ _ with
                                              | left _ => match rec (σ2,τ) _ _ _ with
                                                          | left _ => left _
                                                          | right _ => right _
                                                          end
                                              | right _ => right _
                                              end
              | (_, τ1 ∩ τ2) => λ eq _ _, match rec (σ,τ1) _ _ _ with
                                              | left _ => match rec (σ,τ2) _ _ _ with
                                                          | left _ => left _
                                                          | right _ => right _
                                                          end
                                              | right _ => right _
                                              end
              | (σ1 ⟶ σ2, τ1 ⟶ τ2) => λ eq Dσ Cτ, match rec (τ1,σ1) _ _ _ with
                                                      | left _ => match rec (σ2,τ2) _ _ _ with
                                                                  | left _ => left _
                                                                  | right HAA => right _
                                                                  end
                                                      | right HAA => right _
                                                      end
              | (σ1 ∩ σ2, _) => λ eq Dσ Cτ, match rec (σ1,τ) _ _ _ with
                                                | left _ => left _
                                                | right _ => match rec (σ2,τ) _ _ _ with
                                                             | left _ => left _
                                                             | right _ => right _
                                                             end
                                                end
              | (_, τ1 ∪ τ2) => λ eq Dσ Cτ, match rec (σ,τ1) _ _ _ with
                                                | left _ => left _
                                                | right _ => match rec (σ,τ2) _ _ _ with
                                                             | left _ => left _
                                                             | right _ => right _
                                                             end
                                                end
              | (Var α, Var β) => λ eq _ _, if 𝕍.eq_dec α β then left _ else right _
              | _ => λ eq _ _, right _
              end eq_refl); inv eq; simpl in *;
        match goal with
        | |- main_algo_order _ _ => red; simpl; omega
        | |- ?σ ≤ ?σ => reflexivity
        | H : ?x |- ?x => assumption
        | |- CANF _ => auto with SubtypeHints
        | |- DANF _ => auto with SubtypeHints
        (* Correctness *)
        | |- _ ≤ ω => auto with SubtypeHints
        | |- _ ≤ _ ∩ _ => auto with SubtypeHints
        | |- _ ∪ _ ≤ _ => auto with SubtypeHints
        | |- _ ∩ _ ≤ _ => apply Inter_inf_dual; auto
        | |- _ ≤ _ ∪ _ => apply Union_sup_dual; auto
        | |- _ ⟶ _ ≤ _ ⟶ _ => apply R_CoContra; trivial
        (* Completeness *)
        | |- ¬ ω ≤ _ => apply Omega_IUANF; auto with SubtypeHints
        | |- ¬ _ ∪ _ ≤ _ => intro; apply Union_sup' in H; auto
        | |- ¬ _ ≤ _ ∩ _ => intro; apply Inter_inf' in H; auto
        | |- ¬ ?σ ≤ _ => intro H; apply Ideal_complete in H; [|auto with SubtypeHints];
                           match σ with
                           | _ ∩ _ => apply IdealInter in H; inversion H as [H'|H'];
                                        apply Ideal_correct in H'; auto
                           | _ ⟶ _ => inv H; [apply HAA; reflexivity| |]; auto with SubtypeHints
                           | _ => inv H; auto with SubtypeHints
                           end
        end.
    Defined.

    (* Composition of all the previous algorithms *)
    Definition decide_subtype : ∀ σ τ, {σ ≤ τ} + {¬ σ ≤ τ}.
    Proof.
      intros.
      refine (let (σ1,pfσ) := deleteOmega σ in let (Hσ1,pfσ) := pfσ in
              let (τ1,pfτ) := deleteOmega τ in let (Hτ1,pfτ) := pfτ in
              let (σ2,pfσ) := _DANF σ1 pfσ in let (Hσ2,pfσ) := pfσ in
              let (τ2,pfτ) := _CANF τ1 pfτ in let (Hτ2,pfτ) := pfτ in
              match main_algo (σ2,τ2) pfσ pfτ with
              | left H => left _
              | right H => right _
              end);
        rewrite <- Hτ1, <- Hσ1, <- Hτ2, <- Hσ2; assumption.
    Defined.
  End SubtypeRelation.
End Types.

(* Module nat_var <: VariableAlphabet. *)
(*   Definition t := nat. *)
(*   Definition eq := @eq nat. *)
(*   Definition eq_equiv : Equivalence eq. *)
(*   Proof. *)
(*     constructor. *)
(*     constructor. *)
(*     red. *)
(*     intros. *)
(*     now symmetry. *)
(*     red. *)
(*     intros; etransitivity; eauto. *)
(*   Defined. *)

(*   Definition eq_dec : ∀ x y : t, {x = y} + {x ≠ y}. *)
(*     decide equality. *)
(*   Defined. *)
(* End nat_var. *)

(* Module foo := nat_var <+ Types. *)

(* Import foo. *)
(* Definition is_subtype := SubtypeRelation.decide_subtype. *)

(* Definition s1 := Var 0. *)
(* Definition s2 := Var 1. *)
(* Definition t1 := Var 2. *)
(* Definition t2 := Var 3. *)

(* Definition type_1 := (t1 ⟶ s1) ∩ (t2 ⟶ s2). *)
(* Definition type_2 := (t1 ∪ t2) ⟶ (s1 ∩ s2). *)

(* Eval hnf in (is_subtype type_1 type_2). (* explodes my computer *) *)
(* Eval hnf in (is_subtype type_2 type_1). (* explodes my computer *) *)
