Require Import Classes.Morphisms.
Require Import Relations.
Require Import Structures.Equalities.
Require Import Omega.
Require PreOrderTactic.

(* Dummy module type *)
Module Type SetTyp <: Typ.
  Parameter t : Set.
End SetTyp.

(* Module type for the variables: equality has to be decidable *)
Module Type VariableAlphabet <: UsualDecidableType :=
  SetTyp <+ HasUsualEq <+ UsualIsEq <+ HasEqDec.

Module Types (VAlpha : VariableAlphabet).
  Definition 𝕍 := VAlpha.t.
  Definition 𝕍_eq_dec: forall α β : 𝕍, { α = β } + { α <> β } := VAlpha.eq_dec.

  (* Our type syntax *)
  Inductive term : Set :=
  | Var : 𝕍 -> term
  | Arrow : term -> term -> term
  | Inter : term -> term -> term
  | Union : term -> term -> term
  | Omega : term.
  Infix "→" := (Arrow) (at level 60, right associativity).
  Notation "(→)" := Arrow (only parsing).
  Infix "∩" := (Inter) (at level 35, right associativity).
  Notation "(∩)" := (Inter) (only parsing).
  Infix "∪" := (Union) (at level 30, right associativity).
  Notation "(∪)" := (Union) (only parsing).
  Notation "'ω'" := (Omega).

  Module SubtypeRelation.
    Reserved Infix "≤" (at level 70).
    Reserved Infix "~=" (at level 70).

    (* The subtyping axioms, as defined in the theory Ξ of
       Barbanera, Franco, Mariangiola Dezani-Ciancaglini, and Ugo Deliguoro. "Intersection and union types: syntax and semantics." Information and Computation 119.2 (1995): 202-230. *)
    Inductive Subtype : term -> term -> Prop :=
    | R_InterMeetLeft : forall σ τ, σ ∩ τ ≤ σ
    | R_InterMeetRight : forall σ τ, σ ∩ τ ≤ τ
    | R_InterIdem : forall τ, τ ≤ τ ∩ τ
    | R_UnionMeetLeft : forall σ τ, σ ≤ σ ∪ τ
    | R_UnionMeetRight : forall σ τ, τ ≤ σ ∪ τ
    | R_UnionIdem : forall τ, τ ∪ τ ≤ τ
    | R_InterDistrib : forall σ τ ρ,
        (σ → ρ) ∩ (σ → τ) ≤ σ → ρ ∩ τ
    | R_UnionDistrib : forall σ τ ρ,
        (σ → ρ) ∩ (τ → ρ) ≤ σ ∪ τ → ρ
    | R_InterSubtyDistrib: forall σ σ' τ τ',
        σ ≤ σ' -> τ ≤ τ' -> σ ∩ τ ≤ σ' ∩ τ'
    | R_UnionSubtyDistrib: forall σ σ' τ τ',
        σ ≤ σ' -> τ ≤ τ' -> σ ∪ τ ≤ σ' ∪ τ'
    | R_InterUnionDistrib: forall σ τ ρ,
        σ ∩ (τ ∪ ρ) ≤ (σ ∩ τ) ∪ (σ ∩ ρ)
    | R_CoContra : forall σ σ' τ τ',
        σ ≤ σ' -> τ ≤ τ' -> σ' → τ ≤ σ → τ'
    | R_OmegaTop : forall σ, σ ≤ ω
    | R_OmegaArrow : ω ≤ ω → ω
    | R_Reflexive : forall σ, σ ≤ σ
    | R_Transitive : forall σ τ ρ, σ ≤ τ -> τ ≤ ρ -> σ ≤ ρ
    where "σ ≤ τ" := (Subtype σ τ).
    Notation "(≤)" := (Subtype) (only parsing).

    (* The equivalence relation *)
    Definition equiv (σ τ : term) : Prop := (σ ≤ τ) /\ (τ ≤ σ).
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
    Hint Extern 0 (_ <> _) => discriminate.
    Hint Extern 0 => lazymatch goal with
                     | H : ?x <> ?x |- _ => contradiction
                     end.
    Hint Extern 1 => lazymatch goal with
                     | H : _ /\ _ |- _ => destruct H
                     | H : _ \/ _ |- _ => destruct H
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
    Fact Inter_inf : forall σ τ ρ, σ ≤ τ -> σ ≤ ρ -> σ ≤ τ ∩ ρ.
    Proof with auto with SubtypeHints.
      intros.
      transitivity (σ ∩ σ)...
    Qed.
    Hint Resolve Inter_inf : SubtypeHints.

    Fact Inter_inf' : forall σ τ ρ, σ ≤ τ ∩ ρ -> (σ ≤ τ) /\ (σ ≤ ρ).
    Proof with auto with SubtypeHints.
      intros; split;
        etransitivity;
        try eassumption...
    Qed.

    (* Don't put it in auto or it may be slow *)
    Fact Inter_inf_dual : forall σ τ ρ, (σ ≤ ρ) \/ (τ ≤ ρ) -> σ ∩ τ ≤ ρ.
    Proof with auto with SubtypeHints.
      intros σ τ ? [? | ?];
        [transitivity σ | transitivity τ]...
    Qed.

    Fact Union_sup : forall σ τ ρ, σ ≤ ρ -> τ ≤ ρ -> σ ∪ τ ≤ ρ.
    Proof with auto with SubtypeHints.
      intros.
      transitivity (ρ ∪ ρ)...
    Qed.
    Hint Resolve Union_sup : SubtypeHints.

    Fact Union_sup' : forall σ τ ρ, σ ∪ τ ≤ ρ -> (σ ≤ ρ) /\ (τ ≤ ρ).
    Proof with auto with SubtypeHints.
      intros; split;
        etransitivity;
        try eassumption...
    Qed.

    (* Don't put it in auto or it may be slow *)
    Fact Union_sup_dual : forall σ τ ρ, (σ ≤ τ) \/ (σ ≤ ρ) -> σ ≤ τ ∪ ρ.
    Proof with auto with SubtypeHints.
      intros ? τ ρ [? | ?];
        [transitivity τ | transitivity ρ]...
    Qed.

    Fact OmegaArrow : forall σ τ, ω ≤ τ -> ω ≤ σ → τ.
    Proof with auto with SubtypeHints.
      intro; transitivity (ω → ω)...
    Qed.
    Hint Resolve OmegaArrow : SubtypeHints.

    (* Ask auto to automatically simplify the hypotheses *)
    Hint Extern 1 (_ ≤ _) =>
    lazymatch goal with
    | H : ω ≤ _ |- _ => try rewrite <- H; (clear H) + (try rewrite <- H in *; clear H)
    | H : ?σ ≤ ?τ ∩ ?ρ |- _ => apply Inter_inf' in H; destruct H
    | H : ?σ ∪ ?τ ≤ ?ρ |- _ => apply Union_sup' in H; destruct H
    end : SubtypeHints.

    Goal forall τ ρ τ0, τ ≤ ρ -> ω ≤ τ -> τ0 ≤ ρ ∩ τ.
    Proof.
      intros.
      time(auto with SubtypeHints). (* 0.03s *)
    Qed.
    (* Ask auto to use preorder if the goal is atomic *)
    Hint Extern 300 (?x ≤ ?y) =>
    lazymatch x with
    | _ _ _ => fail
    | _ => lazymatch y with
           | _ _ _ => fail
           | _ => preorder
           end
    end : SubtypeHints.

    Goal forall τ ρ τ0, τ0 ≤ ρ -> ω ≤ τ -> τ0 ≤ ρ ∩ τ.
    Proof.
      time(auto with SubtypeHints). (* 0.15s *)
    Qed.

    Fact UnionInterDistrib : forall σ τ ρ, (σ ∪ τ) ∩ (σ ∪ ρ) ≤ σ ∪ (τ ∩ ρ).
    Proof with auto with SubtypeHints.
      intros.
      etransitivity; [apply R_InterUnionDistrib|]...
      apply Union_sup; [apply Union_sup_dual|]...
      transitivity (ρ ∩ (σ ∪ τ))...
      etransitivity; [apply R_InterUnionDistrib|]...
    Qed.
    Hint Resolve UnionInterDistrib : SubtypeHints.

    (* For more tactics, we show the operators are compatible with the relations *)
    Instance Inter_Proper_ST : Proper ((≤) ==> (≤) ==> (≤)) (∩). (* class morphism *)
    Proof with auto with SubtypeHints.
      compute...
    Qed.

    Instance Union_Proper_ST : Proper ((≤) ==> (≤) ==> (≤)) (∪).
    Proof with auto with SubtypeHints.
      compute...
    Qed.

    Instance Arr_Proper_ST : Proper (transp _ (≤) ==> (≤) ==> (≤)) (→).
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

    Instance Arr_Proper_EQ : Proper ((~=) ==> (~=) ==> (~=)) (→).
    Proof with auto with SubtypeHints.
      compute...
    Qed.

    Hint Extern 2 (?R _ _ ~= ?R _ _) =>
    lazymatch R with
    | (∩) => apply Inter_Proper_EQ
    | (∪) => apply Union_Proper_EQ
    | (→) => apply Arr_Proper_EQ
    end : SubtypeHints.

    Goal forall τ ρ τ0, τ0 ≤ ρ -> ω ≤ τ -> τ0 ≤ ρ ∩ τ.
    Proof.
      time(auto with SubtypeHints). (* 0.016s *)
    Qed.

    (* Syntactical predicates on terms *)
    Inductive Generalize (c : term -> term -> term) (P : term -> Prop) : term -> Prop :=
    | G_nil : forall σ, P σ -> Generalize c P σ
    | G_cons : forall σ τ, Generalize c P σ -> Generalize c P τ -> Generalize c P (c σ τ).
    Hint Constructors Generalize : SubtypeHints.

    (* Notations: [ ⋂ P ] x means x is a generalized intersection of terms verifying P *)
    Notation "[ ⋂ P ]" := (Generalize (∩) P).
    Notation "[ ⋃ P ]" := (Generalize (∪) P).

    (* Arrow Normal Form *)
    Inductive ANF : term -> Prop :=
    | VarisANF : forall α, ANF (Var α)
    | ArrowisANF : forall σ τ, [⋂ ANF] σ -> [⋃ ANF] τ -> ANF (σ → τ)
    | ArrowisANF' : forall τ, [⋃ ANF] τ -> ANF (ω → τ).
    Hint Constructors ANF : SubtypeHints.

    (* Conjunctive/Disjunctive Normal Forms *)
    Definition CANF (σ : term) : Prop := [⋂ [⋃ ANF]] σ \/ σ = ω.
    Definition DANF (σ : term) : Prop := [⋃ [⋂ ANF]] σ \/ σ = ω.
    Hint Unfold CANF : SubtypeHints.
    Hint Unfold DANF : SubtypeHints.

    (* Terms without Omega (with one exception) *)
    Inductive Omega_free : term -> Prop :=
    | Of_Var : forall α, Omega_free (Var α)
    | Of_Union : forall σ τ, Omega_free σ -> Omega_free τ -> Omega_free (σ ∪ τ)
    | Of_Inter : forall σ τ, Omega_free σ -> Omega_free τ -> Omega_free (σ ∩ τ)
    | Of_Arrow1 : forall σ, Omega_free σ -> Omega_free (ω → σ)
    | Of_Arrow2 : forall σ τ, Omega_free σ -> Omega_free τ -> Omega_free (σ → τ).
    Hint Constructors Omega_free : SubtypeHints.

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
                  | H : [⋃ _] (_ → _) |- _ => inv H
                  | H : [⋃ _] (Var _) |- _ => inv H
                  | H : [⋃ _] ω |- _ => inv H
                  | H : [⋂ ANF] (_ ∩ _) |- _ => inversion H as [? H'|]; [inversion H'|]; subst; clear H
                  | H : [⋂ [⋃ ANF]] (_ ∩ _) |- _ => inversion H as [? H'|];
                                                    [inversion H' as [? H''|]; inversion H''|];
                                                    subst; clear H
                  | H : [⋂ _] (_ ∪ _) |- _ => inv H
                  | H : [⋂ _] (_ → _) |- _ => inv H
                  | H : [⋂ _] (Var _) |- _ => inv H
                  | H : [⋂ _] ω |- _ => inv H
                  | H : ANF (ω → _) |- _ => inversion H as [|? ? H'|];
                                            [inversion H' as [? H''|]; inversion H''|]; subst; clear H
                  | H : ANF (_ → _) |- _ => inv H
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
             | |- ANF (ω → _) => apply ArrowisANF'
             | |- ANF (_ → _) => constructor
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

    Goal forall τ ρ τ0, τ0 ≤ ρ -> ω ≤ τ -> τ0 ≤ ρ ∩ τ.
    Proof.
      time(auto with SubtypeHints). (* 0.01s *)
    Qed.

    (* Terms on which we'll define filters *)
    Unset Elimination Schemes.
    Inductive isFilter : term -> Prop :=
    | OmegaisFilter : isFilter ω
    | VarisFilter : forall α, isFilter (Var α)
    | ArrowisFilter : forall σ τ, isFilter (σ → τ)
    | InterisFilter : forall σ τ, isFilter σ -> isFilter τ -> isFilter (σ ∩ τ).
    Set Elimination Schemes.
    Hint Constructors isFilter : SubtypeHints.

    (* The recursion scheme uses P ω as an inductive hypothesis *)
    Lemma isFilter_ind : forall P : term -> Prop,
        P ω ->
        (forall α : 𝕍, P ω -> P (Var α)) ->
        (forall σ τ : term, P ω -> P (σ → τ)) ->
        (forall σ τ : term, isFilter σ -> P σ -> isFilter τ -> P τ -> P ω -> P (σ ∩ τ)) ->
        forall σ : term, isFilter σ -> P σ.
    Proof.
      intros P fω fα fA fI.
      exact (fix foo σ Fσ : P σ := match Fσ in isFilter σ return P σ with
                                   | OmegaisFilter => fω
                                   | VarisFilter α => fα α fω
                                   | ArrowisFilter σ τ => fA σ τ fω
                                   | InterisFilter σ τ Fσ Fτ => fI σ τ Fσ (foo σ Fσ) Fτ (foo τ Fτ) fω
                                   end).
    Qed.

    Reserved Notation "↑[ σ ] τ" (at level 65).
    Reserved Notation "↓[ σ ] τ" (at level 65).
    Inductive Filter : term -> term -> Prop :=
    | F_Refl : forall σ : term, isFilter σ -> ↑[σ] σ
    | F_Inter : forall σ τ ρ : term, ↑[σ] τ -> ↑[σ] ρ -> ↑[σ] τ ∩ ρ
    | F_Union1 : forall σ τ ρ : term, ↑[σ] τ -> ↑[σ] τ ∪ ρ
    | F_Union2 : forall σ τ ρ : term, ↑[σ] ρ -> ↑[σ] τ ∪ ρ
    | F_Arrow1 : forall σ1 σ2 τ1 τ2 : term, σ2 ≤ σ1 -> τ1 ≤ τ2 -> ↑[σ1 → τ1] σ2 → τ2
    | F_Arrow2 : forall σ1 σ2 τ1 τ2 ρ1 ρ2 : term, ↑[σ1 ∩ σ2] τ1 → ρ1 -> τ2 ≤ τ1 -> ρ1 ≤ ρ2 -> ↑[σ1 ∩ σ2] τ2 → ρ2
    | F_OmegaTopV : forall (α : 𝕍) (τ : term), ↑[ω] τ -> ↑[Var α] τ
    | F_OmegaTopA : forall σ1 σ2 τ : term, ↑[ω] τ -> ↑[σ1 → σ2] τ
    | F_OmegaTopI : forall σ1 σ2 τ : term, isFilter (σ1 ∩ σ2) -> ↑[ω] τ -> ↑[σ1 ∩ σ2] τ
    | F_Omega : forall σ τ : term, ↑[ω] τ -> ↑[ω] σ → τ
    | F_Inter1 : forall σ1 σ2 τ : term, isFilter σ2 -> ↑[σ1] τ -> ↑[σ1 ∩ σ2] τ
    | F_Inter2 : forall σ1 σ2 τ : term, isFilter σ1 -> ↑[σ2] τ -> ↑[σ1 ∩ σ2] τ
    | F_ArrowInter : forall σ1 σ2 τ ρ1 ρ2 : term, ↑[σ1 ∩ σ2] (τ → ρ1) ∩ (τ → ρ2) -> ↑[σ1 ∩ σ2] τ → ρ1 ∩ ρ2
    | F_ArrowUnion : forall σ1 σ2 τ1 τ2 ρ : term, ↑[σ1 ∩ σ2] (τ1 → ρ) ∩ (τ2 → ρ) -> ↑[σ1 ∩ σ2] τ1 ∪ τ2 → ρ
    where "↑[ σ ] τ" := (Filter σ τ).

    Hint Constructors Filter : SubtypeHints.

    Inductive Ideal : term -> term -> Prop :=
    | I_Refl : forall σ : term,  [⋃ ANF] σ -> ↓[σ] σ
    | I_Inter1 : forall σ τ ρ : term, ↓[σ] τ -> ↓[σ] τ ∩ ρ
    | I_Inter2 : forall σ τ ρ : term, ↓[σ] ρ -> ↓[σ] τ ∩ ρ
    | I_Union : forall σ τ ρ : term, ↓[σ] τ -> ↓[σ] ρ -> ↓[σ] τ ∪ ρ
    | I_Arrow1 : forall σ1 σ2 τ1 τ2 : term, [⋂ ANF] σ1 -> ↑[σ1] σ2 -> ↓[τ1] τ2 -> ↓[σ1 → τ1] σ2 → τ2
    | I_Arrow2 : forall σ τ1 τ2 : term, ↑[ω] σ -> ↓[τ1] τ2 -> ↓[ω → τ1] σ → τ2
    | I_Union1 : forall σ1 σ2 τ : term, [⋃ ANF] σ2 -> ↓[σ1] τ -> ↓[σ1 ∪ σ2] τ
    | I_Union2 : forall σ1 σ2 τ : term, [⋃ ANF] σ1 -> ↓[σ2] τ -> ↓[σ1 ∪ σ2] τ
    where "↓[ σ ] τ" := (Ideal σ τ).

    Hint Constructors Ideal : SubtypeHints.
    Goal forall τ ρ τ0, τ0 ≤ ρ -> ω ≤ τ -> τ0 ≤ ρ ∩ τ.
    Proof.
      time(auto with SubtypeHints). (* 0.01s *)
    Qed.

    Lemma Filter_correct : forall σ τ, ↑[σ] τ -> σ ≤ τ.
    Proof with auto using Inter_inf_dual, Union_sup_dual with SubtypeHints.
      intros ? ? H.
      induction H...
      - etransitivity; [eassumption|]...
      - etransitivity; [|apply R_InterDistrib]...
      - etransitivity; [|apply R_UnionDistrib]...
    Qed.
    Hint Resolve Filter_correct : SubtypeHints.

    Goal forall τ ρ τ0, τ0 ≤ ρ -> ω ≤ τ -> τ0 ≤ ρ ∩ τ.
    Proof.
      time(auto with SubtypeHints). (* 0.01s *)
    Qed.

    Hint Extern 1 (_ ≤ _) =>
    lazymatch goal with
    | H : ↑[ω] _ |- _ => apply (Filter_correct) in H; try rewrite <- H; (clear H) + (try rewrite <- H in *; clear H)
    end : SubtypeHints.

    Goal forall τ ρ τ0, τ0 ≤ ρ -> ω ≤ τ -> τ0 ≤ ρ ∩ τ.
    Proof.
      time(auto with SubtypeHints). (* 0.01s *)
    Qed.

    Lemma Filter_isFilter: forall σ τ, ↑[σ] τ -> isFilter σ.
    Proof.
      intros ? ? H; induction H; auto; constructor; auto.
    Qed.
    Hint Extern 0 (isFilter ?σ) =>
      match goal with
      | H : ↑[?σ] _ |- _ => apply (Filter_isFilter _ _ H)
      end : SubtypeHints.

    (* cast ρ to σ (may produce new goals) *)
    Ltac cast_filter ρ σ :=
      lazymatch σ with
      | ω => match ρ with
             | Var _ => apply F_OmegaTopV
             | _ → _ => apply F_OmegaTopA
             | _ ∩ _ => apply F_OmegaTopI
             end
      | _ => lazymatch ρ with
             | σ ∩ _ => apply F_Inter1
             | _ ∩ σ => apply F_Inter2
             end
      end.

    Goal forall τ ρ τ0, τ0 ≤ ρ -> ω ≤ τ -> τ0 ≤ ρ ∩ τ.
    Proof.
      time(auto with SubtypeHints). (* 0.01s *)
    Qed.

    Lemma FilterInter : forall σ τ ρ, ↑[σ] τ ∩ ρ -> ↑[σ] τ /\ ↑[σ] ρ.
      intros ? ? ? H.
      assert (Fσ : isFilter σ) by (auto with SubtypeHints).
      induction Fσ; split; inv H;
        auto with SubtypeHints;
        lazymatch goal with
        (* Inductive case *)
        | IH : ↑[?σ] ?τ -> _, H : ↑[?σ] ?τ |- ↑[?ρ] _ =>
          (* cast ρ to σ *)
          cast_filter ρ σ; trivial;
            (* apply the inductive hypothesis *)
            apply IH; trivial
        end.
    Qed.

    Lemma FilterUnion : forall σ τ ρ, ↑[σ] τ ∪ ρ -> ↑[σ] τ \/ ↑[σ] ρ.
      intros ? ? ? H.
      assert (Fσ : isFilter σ) by (auto with SubtypeHints).
      induction Fσ; inv H; auto;
        lazymatch goal with
        (* Inductive case *)
        | IH : ↑[?σ] ?τ1 ∪ ?τ2 -> ?prop, H : ↑[?σ] ?τ1 ∪ ?τ2 |- ↑[?ρ] ?τ1 \/ ↑[?ρ] ?τ2 =>
          (* apply the inductive hypothesis *)
          destruct (IH H); [left|right];
            (* cast ρ to σ *)
            cast_filter ρ σ; assumption
        end.
    Qed.

    Lemma FilterArrow : forall σ σ' τ τ', ↑[σ → σ'] τ → τ' -> (↑[ω] τ → τ' \/ (τ ≤ σ  /\ σ' ≤ τ')).
    Proof.
      intros ? ? ? ? H; inv H; auto 3 with SubtypeHints.
    Qed.

    Hint Extern 1 =>
    lazymatch goal with
    | H : ↑[?σ ∩ ?τ] (?ρ → _) ∩ (?ρ → _) |- _ => apply F_ArrowInter in H
    | H : ↑[?σ ∩ ?τ] (_ → ?ρ) ∩ (_ → ?ρ) |- _ => apply F_ArrowUnion in H
    | H : ↑[_] _ ∪ _ |- _ => apply FilterUnion in H; destruct H
    | H : ↑[_] _ ∩ _ |- _ => apply FilterInter in H; destruct H
    | H : ↑[_ → _] _ → _ |- _ => apply FilterArrow in H; destruct H as [|[ ]]
    | H : ↑[ω] _ → _ |- _ => inv H
    | H : ↑[Var _] _ → _ |- _ => inv H
    end : SubtypeHints.

    Goal forall τ ρ τ0, τ0 ≤ ρ -> ω ≤ τ -> τ0 ≤ ρ ∩ τ.
    Proof.
      time(auto with SubtypeHints). (* 0.01s *)
    Qed.

    Lemma Filter_omega : forall σ τ, isFilter σ -> ↑[ω] τ -> ↑[σ] τ.
    Proof.
      induction 1; auto with SubtypeHints.
    Qed.

    Lemma FilterArrow' : forall σ τ' ρ, ↑[ σ] τ' → ρ -> forall τ ρ', τ ≤ τ' -> ρ ≤ ρ' -> ↑[ σ] τ → ρ'.
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

    Lemma Filter_closed : forall σ τ1 τ2,
        ↑[σ] τ1 -> τ1 ≤ τ2 -> ↑[σ] τ2.
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

    Lemma Filter_complete : forall σ, isFilter σ -> forall τ, σ ≤ τ -> ↑[σ] τ.
    Proof.
      intros; eapply Filter_closed; try eassumption.
      apply F_Refl; assumption.
    Qed.
    Hint Resolve Filter_complete : SubtypeHints.

    (* Unicode starts dying below this point *)

    Lemma Ideal_correct : forall σ τ, ↓[σ] τ -> τ ≤ σ.
    Proof with auto using Inter_inf_dual, Union_sup_dual with SubtypeHints.
      intros ? ? H.
      induction H...
    Qed.
    Hint Resolve Ideal_correct : SubtypeHints.

    Lemma Ideal_isDANF: forall σ τ, ↓[σ] τ -> [⋃ ANF] σ.
    Proof.
      intros ? ? H; induction H; auto with SubtypeHints.
    Qed.
    Hint Resolve Ideal_isDANF : SubtypeHints.
    Hint Extern 0 ([⋃ ANF] ?σ) =>
      match goal with
      | H : ↓[?σ] _ |- _ => apply (Ideal_isDANF _ _ H)
      end : SubtypeHints.

    Ltac cast_ideal ρ σ :=
      lazymatch ρ with
      | σ ∪ _ => apply I_Union1
      | _ ∪ σ => apply I_Union2
      end.

    Lemma IdealUnion : forall σ τ ρ, ↓[σ] τ ∪ ρ -> ↓[σ] τ /\ ↓[σ] ρ.
      intros ? ? ? H.
      assert (Iσ : [⋃ ANF] σ) by (auto with SubtypeHints).
      induction Iσ; split; inv H;
        auto with SubtypeHints; decide_nf;
          lazymatch goal with
          (* Inductive case *)
          | IH : ↓[?σ] ?τ -> _, H : ↓[?σ] ?τ |- ↓[?ρ] _ =>
            (* cast ρ to σ *)
            cast_ideal ρ σ; trivial;
              (* apply the inductive hypothesis *)
              apply IH; trivial
          end.
    Qed.

    Lemma IdealInter : forall σ τ ρ, ↓[σ] τ ∩ ρ -> ↓[σ] τ \/ ↓[σ] ρ.
      intros ? ? ? H.
      assert (Iσ : [⋃ ANF] σ) by (auto with SubtypeHints).
      induction Iσ; inv H; auto with SubtypeHints; decide_nf;
        lazymatch goal with
        (* Inductive case *)
        | IH : ↓[?σ] ?τ1 ∩ ?τ2 -> ?prop, H : ↓[?σ] ?τ1 ∩ ?τ2 |- ↓[?ρ] ?τ1 \/ ↓[?ρ] ?τ2 =>
          (* apply the inductive hypothesis *)
          destruct (IH H); [left|right];
            (* cast ρ to σ *)
            cast_ideal ρ σ; assumption
        end.
    Qed.

    Lemma InterANF_isFilter : forall σ, [ ⋂ ANF] σ -> isFilter σ.
    Proof.
      induction 1 as [? H|].
      inversion H; auto with SubtypeHints.
      constructor; trivial.
    Qed.
    Hint Extern 0 (isFilter ?σ) =>
    match goal with
    | H : [ ⋂ ANF] σ |- _ => apply InterANF_isFilter
    end : SubtypeHints.

    Lemma Uanf_ind : forall P : term -> Prop,
        (forall α, P (Var α)) ->
        (forall σ τ, P σ -> P τ -> P (σ ∪ τ)) ->
        (forall σ τ, P τ -> P (σ → τ)) ->
        (forall σ, [⋃ ANF] σ -> P σ).
      intros P fV fU fA.
      refine (fix foo (σ : term) := match σ with
                                    | Var α => fun _ => fV α
                                    | σ → τ => fun pf => fA _ τ (foo τ _)
                                    | σ ∪ τ => fun pf => fU σ τ (foo σ _) (foo τ _)
                                    | σ ∩ τ => fun pf => _
                                    | ω => fun pf => _
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

    Lemma IdealnoOmega : forall σ, ~ ↓[ σ] ω.
    Proof.
      induction σ; intro H; inv H;
        auto with SubtypeHints; decide_nf.
    Qed.

    Lemma IdealnoOmegaArrow : forall σ, ~ ↓[ σ] ω → ω.
    Proof.
      induction σ; intro H; inv H;
        auto with SubtypeHints; decide_nf;
        eapply IdealnoOmega; eassumption.
    Qed.

    Ltac destruct_ideal :=
      repeat lazymatch goal with
             | H : ↓[_] ω |- _ => apply IdealnoOmega in H; exfalso; trivial
             | H : ↓[_] ω → ω |- _ => apply IdealnoOmegaArrow in H; exfalso; trivial
             | H : ↓[_] _ ∪ _ |- _ => apply IdealUnion in H; destruct H
             | H : ↓[_] _ ∩ _ |- _ => apply IdealInter in H; destruct H
             | H : ↓[_ ∪ _] _ → _ |- _ => inv H
             | H : ↓[_ → _] _ → _ |- _ => inv H
             | H : ↓[Var _] _ → _ |- _ => inv H
             end.

    Section Ideal_closed.
      (* This hint is local to the section; and help use the inductive hypotheses *)
      Hint Extern 1 (↓[?ρ] _) =>
      (* For an unknown reason, auto fails to use the generated hypothesis; so foo helps it *)
      let foo σ HHH :=
          lazymatch ρ with
          | _ ∪ _ => cast_ideal ρ σ; trivial; apply HHH
          | ω → _ => apply I_Arrow2; [|apply HHH]
          | _ → _ => apply I_Arrow1; [| |apply HHH]
          end
      in
      (* The variable τ cannot be infered by auto, so this tactic instantiates it *)
      lazymatch goal with
      | H : forall τ, ↓[?σ] τ -> forall τ' : term, τ' ≤ τ -> ↓[?σ] τ', H' : ↓[?σ] ?τ |- _ =>
      assert (HHH : forall τ' : term, τ' ≤ τ -> ↓[ σ] τ') by (exact (H τ H')); clear H H'; foo σ HHH
    | H : forall τ, ↓[?σ] τ -> forall τ' : term, τ' ≤ τ -> ↓[?σ] τ', H' : ?τ ≤ ?σ |- _ =>
      assert (HHH : ↓[ σ] τ) by (refine (H _ (I_Refl _ _) _ H'); trivial); clear H H'; foo σ HHH
      end.

      Lemma Ideal_closed : forall σ, [⋃ ANF] σ -> forall τ1, ↓[σ] τ1 -> forall τ2, τ2 ≤ τ1 -> ↓[σ] τ2.
      Proof.
        time(intros until 1; uanf_ind σ;
             lazymatch goal with
             | H : _ ≤ _ |- _ => induction H;
                                 destruct_ideal;
                                 decide_nf;
                                 auto with SubtypeHints
             end).
      Qed.
    End Ideal_closed.

    Lemma Ideal_complete : forall σ, [⋃ ANF] σ -> forall τ, τ ≤ σ -> ↓[σ] τ.
    Proof.
      intros; eapply Ideal_closed; try eassumption.
      apply I_Refl; assumption.
    Qed.

    (* Rewriting functions *)

    (* First rewriting function: do Omega-related simplifications *)

    Hint Extern 1 (_ ~= _ ) =>
    repeat lazymatch goal with
    | H : ?x ~= ω |- context[?x] => rewrite H; clear H
    | H : ω ~= ?x |- context[?x] => rewrite <- H; clear H
    | H : ?x ~= _ |- context[?x] => rewrite H; clear H
           end : SubtypeHints.

    Definition deleteOmega : forall σ : term, {τ | τ ~= σ /\ (Omega_free τ \/ τ = ω)}.
    Proof.
      refine(fix deleteOmega (σ : term) :=
               match σ with
               | σ → τ => let (σ,pfσ) := deleteOmega σ in
                          let (τ,pfτ) := deleteOmega τ in
                          match τ as x return τ = x -> _ with
                          | ω => fun _ => exist _ ω _
                          | _ => fun _ => exist _ (σ → τ) _
                          end eq_refl
               | σ ∩ τ => let (σ,pfσ) := deleteOmega σ in
                          let (τ,pfτ) := deleteOmega τ in
                          match σ as x return σ = x -> _ with
                          | ω => fun _ => exist _ τ _
                          | _ => fun _ => match τ as x return τ = x -> _ with
                                          | ω => fun _ => exist _ σ _
                                          | _ => fun _ => exist _ (σ ∩ τ) _
                                          end eq_refl
                          end eq_refl
               | σ ∪ τ => let (σ,pfσ) := deleteOmega σ in
                          let (τ,pfτ) := deleteOmega τ in
                          match σ as x return σ = x -> _ with
                          | ω => fun _ => exist _ ω _
                          | _ => fun _ => match τ as x return τ = x -> _ with
                                          | ω => fun _ => exist _ ω _
                                          | _ => fun _ => exist _ (σ ∪ τ) _
                                          end eq_refl
                          end eq_refl
               | Var α => exist _ (Var α) _
               | ω => exist _ ω _
               end); clear deleteOmega; subst; simpl in *;
        time (first[destruct pfσ as [? [|]];
                    destruct pfτ as [? [|]]; subst|
                    auto with SubtypeHints];
              first[match goal with | H : Omega_free ω |- _ => inversion H end|
                    discriminate|
                    split; auto with SubtypeHints]).
    Defined.

    Lemma InterArrowEquiv : forall σ1 σ2 τ ρ1 ρ2, σ1 ~= τ → ρ1 -> σ2 ~= τ → ρ2 ->  σ1 ∩ σ2 ~= τ → ρ1 ∩ ρ2.
    Proof.
      intros ? ? ? ? ? H H'.
      rewrite H, H'.
      auto with SubtypeHints.
    Qed.
    Hint Resolve InterArrowEquiv : SubtypeHints.

    Lemma UnionArrowEquiv : forall σ1 σ2 τ1 τ2 ρ, σ1 ~= τ1 → ρ -> σ2 ~= τ2 → ρ ->  σ1 ∩ σ2 ~= τ1 ∪ τ2 → ρ.
    Proof.
      intros ? ? ? ? ? H H'.
      rewrite H, H'.
      auto with SubtypeHints.
    Qed.
    Hint Resolve UnionArrowEquiv : SubtypeHints.

    Definition distrArrow : forall (σ τ : term), ([⋃ [⋂ ANF]] σ \/ σ = ω) -> [⋂ [⋃ ANF]] τ ->
                                                 {σ' | σ' ~= σ → τ /\ [⋂ ANF] σ'}.
    Proof.
      refine(fix distrArrow σ τ pfσ pfτ :=
               match σ as x return σ = x -> _ with
               | σ1 ∪ σ2 => fun _ => let (σ1,pfσ1) := distrArrow σ1 τ _ _ in
                                     let (σ2,pfσ2) := distrArrow σ2 τ _ _ in
                                     exist _ (σ1 ∩ σ2) _
               | _ => fun _ =>
                        (fix distrArrow' σ τ (pfσ:[⋂ ANF] σ \/ σ = ω) (pfτ:[⋂ [⋃ ANF]] τ) : {σ' | σ' ~= σ → τ /\ [⋂ ANF] σ'} :=
                           match τ as x return τ = x -> _ with
                           | τ1 ∩ τ2 => fun _ => let (τ1,pfτ1) := distrArrow' σ τ1 _ _ in
                                                 let (τ2,pfτ2) := distrArrow' σ τ2 _ _ in
                                                 exist _ (τ1 ∩ τ2) _
                           | _ => fun _ => exist _ (σ → τ) _
                           end eq_refl) σ τ _ pfτ
               end eq_refl); subst; (destruct pfσ; [|try discriminate]); simpl in *;
        time(auto with SubtypeHints).
    Defined.

    Lemma UnionEquiv1 : forall σ1 σ2 τ1 τ2 τ3, σ1 ~= τ1 ∪ τ2 -> σ2 ~= τ1 ∪ τ3 -> σ1 ∩ σ2 ~= τ1 ∪ (τ2 ∩ τ3).
    Proof.
      intros ? ? ? ? ? H H'.
      rewrite H, H'.
      auto with SubtypeHints.
    Qed.
    Hint Resolve UnionEquiv1 : SubtypeHints.

    Lemma UnionEquiv2 : forall σ1 σ2 τ1 τ2 τ3, σ1 ~= τ1 ∪ τ3 -> σ2 ~= τ2 ∪ τ3 -> σ1 ∩ σ2 ~= (τ1 ∩ τ2) ∪ τ3.
    Proof.
      intros ? ? ? ? ? H H'.
      rewrite H, H'.
      transitivity (τ3 ∪ (τ1 ∩ τ2)); auto with SubtypeHints.
    Qed.
    Hint Resolve UnionEquiv2 : SubtypeHints.

    Definition distrUnion : forall (σ τ : term), [⋂ [⋃ ANF]] σ -> [⋂ [⋃ ANF]] τ ->
                                                 {σ' | σ' ~= σ ∪ τ /\ [⋂ [⋃ ANF]] σ'}.
    Proof.
      refine(fix distrUnion σ τ pfσ pfτ :=
               match σ as x return σ = x -> _ with
               | σ1 ∩ σ2 => fun _ => let (σ1,pfσ1) := distrUnion σ1 τ _ _ in
                                     let (σ2,pfσ2) := distrUnion σ2 τ _ _ in
                                     exist _ (σ1 ∩ σ2) _
               | _ => fun _ =>
                        (fix distrUnion' σ τ (pfσ:[⋃ ANF] σ) (pfτ:[⋂ [⋃ ANF]] τ) : {σ' | σ' ~= σ ∪ τ /\ [⋂ [⋃ ANF]] σ'} :=
                           match τ as x return τ = x -> _ with
                           | τ1 ∩ τ2 => fun _ => let (τ1,pfτ1) := distrUnion' σ τ1 _ _ in
                                                 let (τ2,pfτ2) := distrUnion' σ τ2 _ _ in
                                                 exist _ (τ1 ∩ τ2) _
                           | _ => fun _ => exist _ (σ ∪ τ) _
                           end eq_refl) σ τ _ pfτ
               end eq_refl); subst; simpl in *;
        time(auto with SubtypeHints).
    Defined.

    Lemma InterEquiv1 : forall σ1 σ2 τ1 τ2 τ3, σ1 ~= τ1 ∩ τ2 -> σ2 ~= τ1 ∩ τ3 -> σ1 ∪ σ2 ~= τ1 ∩ (τ2 ∪ τ3).
    Proof.
      intros ? ? ? ? ? H H'.
      rewrite H, H'.
      auto with SubtypeHints.
    Qed.
    Hint Resolve InterEquiv1 : SubtypeHints.

    Lemma InterEquiv2 : forall σ1 σ2 τ1 τ2 τ3, σ1 ~= τ1 ∩ τ3 -> σ2 ~= τ2 ∩ τ3 -> σ1 ∪ σ2 ~= (τ1 ∪ τ2) ∩ τ3.
    Proof.
      intros ? ? ? ? ? H H'.
      rewrite H, H'.
      transitivity (τ3 ∩ (τ1 ∪ τ2)); auto with SubtypeHints.
    Qed.
    Hint Resolve InterEquiv2 : SubtypeHints.

    Definition distrInter : forall (σ τ : term), [⋃ [⋂ ANF]] σ -> [⋃ [⋂ ANF]] τ ->
                                                 {σ' | σ' ~= σ ∩ τ /\ [⋃ [⋂ ANF]] σ'}.
    Proof.
      refine(fix distrUnion σ τ pfσ pfτ :=
               match σ as x return σ = x -> _ with
               | σ1 ∪ σ2 => fun _ => let (σ1,pfσ1) := distrUnion σ1 τ _ _ in
                                     let (σ2,pfσ2) := distrUnion σ2 τ _ _ in
                                     exist _ (σ1 ∪ σ2) _
               | _ => fun _ =>
                        (fix distrUnion' σ τ (pfσ:[⋂ ANF] σ) (pfτ:[⋃ [⋂ ANF]] τ) : {σ' | σ' ~= σ ∩ τ /\ [⋃ [⋂ ANF]] σ'} :=
                           match τ as x return τ = x -> _ with
                           | τ1 ∪ τ2 => fun _ => let (τ1,pfτ1) := distrUnion' σ τ1 _ _ in
                                                 let (τ2,pfτ2) := distrUnion' σ τ2 _ _ in
                                                 exist _ (τ1 ∪ τ2) _
                           | _ => fun _ => exist _ (σ ∩ τ) _
                           end eq_refl) σ τ _ pfτ
               end eq_refl); subst; simpl in *;
        time(auto with SubtypeHints).
    Defined.

    Lemma Omega_free_Omega : forall s, Omega_free s -> s ~= Omega -> False.
    Proof.
      intros ? H [_ H2].
      apply Filter_complete in H2; trivial with SubtypeHints.
      induction s; inv H; inv H2; auto with SubtypeHints.
    Qed.

    Lemma general_inheritance : forall f g P s, Generalize f P s -> Generalize f (Generalize g P) s.
    Proof.
      intros ? ? ? ? H; induction H.
      - constructor; constructor; assumption.
      - constructor 2; assumption.
    Qed.
    Hint Resolve general_inheritance : SubtypeHints.

    Hint Extern 1 =>
    match goal with
    | H : Omega_free ω |- _ => inversion H
    | H : Omega_free (_ _ _) |- _ => inv H
    end : SubtypeHints.

    Fixpoint _CANF  (σ : term) : (Omega_free σ \/ σ = ω) -> {τ | τ ~= σ /\ CANF τ}
    with _DANF  (σ : term) : (Omega_free σ \/ σ = ω) -> {τ | τ ~= σ /\ DANF τ}.
    Proof.
      - refine(match σ with
               | Var α => fun _ => exist _ (Var α) _
               | σ → τ => fun pf =>
                            let (σ,pfσ) := _DANF σ _ in
                            let (τ,pfτ) := _CANF τ _ in
                            let (σ',pfσ') := distrArrow σ τ _ _ in
                            exist _ σ' _
               | σ ∩ τ => fun pf =>
                            let (σ,pfσ) := _CANF σ _ in
                            let (τ,pfτ) := _CANF τ _ in
                            exist _ (σ ∩ τ) _
               | σ ∪ τ => fun pf =>
                            let (σ,pfσ) := _CANF σ _ in
                            let (τ,pfτ) := _CANF τ _ in
                            let (σ',pfσ') := distrUnion σ τ _ _ in
                            exist _ σ' _
               | ω => fun _ => exist _ ω _
               end); try (destruct pf; [|discriminate]); simpl in *;
          match goal with
          | |- _ \/ _ => auto with SubtypeHints
          | |- _ /\ _ => split; [trivial|]
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
               | Var α => fun _ => exist _ (Var α) _
               | σ → τ => fun pf =>
                            let (σ,pfσ) := _DANF σ _ in
                            let (τ,pfτ) := _CANF τ _ in
                            let (σ',pfσ') := distrArrow σ τ _ _ in
                            exist _ σ' _
               | σ ∪ τ => fun pf =>
                            let (σ,pfσ) := _DANF σ _ in
                            let (τ,pfτ) := _DANF τ _ in
                            exist _ (σ ∪ τ) _
               | σ ∩ τ => fun pf =>
                            let (σ,pfσ) := _DANF σ _ in
                            let (τ,pfτ) := _DANF τ _ in
                            let (σ',pfσ') := distrInter σ τ _ _ in
                            exist _ σ' _
               | ω => fun _ => exist _ ω _
               end); try (destruct pf; [|discriminate]); simpl in *;
          match goal with
          | |- _ \/ _ => auto with SubtypeHints
          | |- _ /\ _ => split; [trivial|]
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

    Lemma Omega_IUANF : forall σ, [ ⋂ [ ⋃ ANF]] σ -> ~ ω ≤ σ.
    Proof.
      induction σ as [|? H1 ? H2|? H1 ? H2|? H1 ? H2|];
        intros; intro Hyp; (apply Filter_complete in Hyp; [|constructor]); inv Hyp;
          solve [apply H2; auto 2 with SubtypeHints|
                 apply H1; auto 2 with SubtypeHints|
                 decide_nf].
    Qed.

    Fixpoint size (σ : term) : nat :=
      match σ with
      | Var α => 0
      | σ → τ => S((size σ) + (size τ))
      | σ ∩ τ => S((size σ) + (size τ))
      | σ ∪ τ => S((size σ) + (size τ))
      | ω => 0
      end.
    Definition pair_size (x : term * term) : nat :=
      let (s,t) := x in size s + size t.

    Definition main_algo_order : relation (term * term) := (* Relation_Definitions *)
      fun x y =>
        pair_size x < pair_size y.

    Definition wf_main_algo : well_founded main_algo_order := well_founded_ltof _ _.

    Definition main_algo : forall pair : term * term, let (σ,τ) := pair in DANF σ -> CANF τ -> {σ ≤ τ} + {~ σ ≤ τ}.
      refine (Fix wf_main_algo _ _). intros [σ τ] rec.
      refine (match (σ,τ) as x return x = (σ,τ) -> _ with
              | (_, ω) => fun eq _ _ => left _
              | (ω, _) => fun eq _ Cτ => right _
              | (σ1 ∪ σ2, _) => fun eq _ _ => match rec (σ1,τ) _ _ _ with
                                              | left _ => match rec (σ2,τ) _ _ _ with
                                                          | left _ => left _
                                                          | right _ => right _
                                                          end
                                              | right _ => right _
                                              end
              | (_, τ1 ∩ τ2) => fun eq _ _ => match rec (σ,τ1) _ _ _ with
                                              | left _ => match rec (σ,τ2) _ _ _ with
                                                          | left _ => left _
                                                          | right _ => right _
                                                          end
                                              | right _ => right _
                                              end
              | (σ1 → σ2, τ1 → τ2) => fun eq Dσ Cτ => match rec (τ1,σ1) _ _ _ with
                                                      | left _ => match rec (σ2,τ2) _ _ _ with
                                                                  | left _ => left _
                                                                  | right HAA => right _
                                                                  end
                                                      | right HAA => right _
                                                      end
              | (σ1 ∩ σ2, _) => fun eq Dσ Cτ => match rec (σ1,τ) _ _ _ with
                                                | left _ => left _
                                                | right _ => match rec (σ2,τ) _ _ _ with
                                                             | left _ => left _
                                                             | right _ => right _
                                                             end
                                                end
              | (_, τ1 ∪ τ2) => fun eq Dσ Cτ => match rec (σ,τ1) _ _ _ with
                                                | left _ => left _
                                                | right _ => match rec (σ,τ2) _ _ _ with
                                                             | left _ => left _
                                                             | right _ => right _
                                                             end
                                                end
              | (Var α, Var β) => fun eq _ _ => if 𝕍_eq_dec α β then left _ else right _
              | _ => fun eq _ _ => right _
              end eq_refl); inv eq;
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
        | |- _ → _ ≤ _ → _ => apply R_CoContra; trivial
        (* Completeness *)
        | |- ~ ω ≤ _ => apply Omega_IUANF; auto with SubtypeHints
        | |- ~ _ ∪ _ ≤ _ => intro; apply Union_sup' in H; auto
        | |- ~ _ ≤ _ ∩ _ => intro; apply Inter_inf' in H; auto
        | |- ~ ?σ ≤ _ => intro H; apply Ideal_complete in H; [|auto with SubtypeHints];
                           match σ with
                           | _ ∩ _ => apply IdealInter in H; inversion H as [H'|H'];
                                        apply Ideal_correct in H'; auto
                           | _ → _ => inv H; [apply HAA; reflexivity| |]; auto with SubtypeHints
                           | _ => inv H; auto with SubtypeHints
                           end
        end.
    Defined.

    Definition decide_subtype : forall σ τ, {σ ≤ τ} + {~ σ ≤ τ}.
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


Module CoqExample.
  Module NatVar <: VariableAlphabet.
    Definition t := nat.
    Definition eq_dec := eq_nat_dec.
    Include HasUsualEq.
    Include UsualIsEq.
  End NatVar.
  Module NatVarTypes := NatVar <+ Types.
  Import NatVarTypes.
  Import NatVarTypes.SubtypeRelation.

  Definition α := (Var 1).
  Definition β := (Var 2).
  Definition γ := (Var 3).
  Definition δ := (Var 4).
  Definition ε := (Var 5).
  Definition ζ := (Var 6).

  Example subtype_proof :=
    decide_subtype
      (((α → β) → δ) ∩ ((α → γ) → δ) ∩ (ε → ζ) ∩ (ε → α))
      (((α → β ∩ ε) → δ) ∩ (ε → ζ ∩ α)).

  Example non_subtype_proof :=
    decide_subtype
      (((α → β) → δ) ∩ ((α → γ) → δ) ∩ (ε → ζ) ∩ (ε → α))
      (((α → β → ε) → δ) ∩ (ε → ζ ∩ α)).

  (* Run this:  Eval compute in subtype_proof *)
End CoqExample.
