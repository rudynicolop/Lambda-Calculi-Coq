Require Export Coq.Program.Basics Coq.Classes.RelationClasses
        Coq.Lists.List Coq.Arith.PeanoNat
        Coq.micromega.Lia Coq.Arith.Compare_dec.
Export ListNotations.

Infix "$" := apply (at level 41, right associativity).

Ltac inv H := inversion H; subst; clear H.

Ltac compare_destruct :=
  match goal with
  | |- context [lt_dec ?a ?b]
    => destruct (lt_dec a b) as [? | ?] eqn:?
  | |- context [lt_eq_lt_dec ?a ?b]
    => destruct (lt_eq_lt_dec a b) as [[? | ?] | ?] eqn:?
  | |- context [match ?n with 0 => _ | S _ => _ end]
    => destruct n as [| ?]
  end.
(**[]*)

Ltac compare_destruct_star := repeat (compare_destruct; simpl).

Ltac clean_compare := compare_destruct_star; try lia; auto.

(** * Binary Relations *)

Definition deterministic {A : Type} (R : A -> A -> Prop) : Prop :=
  forall a a1 a2, R a a1 -> R a a2 -> a1 = a2.

Ltac ind_det :=
  match goal with
  | |- deterministic _
    => intros ? ? a2 H1;
      generalize dependent a2;
      induction H1; intros ? H2; inv H2; auto
  end.
(**[]*)

(** Reflexive-Transitive Closure of a Relation. *)

Reserved Notation "a1 '~~>' a2" (at level 40).

Inductive refl_trans_closure {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| refl_closure a :
    a ~~>  a
| trans_closure a1 a2 a3 :
    R a1 a2 ->
    a2 ~~>  a3 ->
    a1 ~~>  a3
where "a1 '~~>' a2" := (refl_trans_closure _ a1 a2).
(**[]*)

Section ReflTransClosureProp.
  Context {A : Type}.
  Variable (R : A -> A -> Prop).
  
  Global Instance refl_trans_closure_reflexive
    : Reflexive (refl_trans_closure R).
  Proof using Type.
    intros ?; apply refl_closure.
  Qed.

  Lemma inject_trans_closure : forall a1 a2,
      R a1 a2 -> refl_trans_closure R a1 a2.
  Proof using Type.
    intros; apply trans_closure with a2;
      auto using reflexivity.
  Qed.

  Global Instance refl_trans_closure_transitive
    : Transitive (refl_trans_closure R).
  Proof using Type.
    intros x y z Hxy Hyz; generalize dependent z.
    induction Hxy; intros z Hyz; try assumption.
    apply IHHxy in Hyz.
    apply trans_closure with a2; assumption.
  Qed.
End ReflTransClosureProp.
