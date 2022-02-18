Require Export Lambda.Util Coq.Program.Equality.

Inductive type : Set :=
| Base
| Arrow (t1 t2 : type).
(**[]*)

Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Notation "⊥" := Base (at level 0) : ty_scope.
Notation "t1 '→' t2" := (Arrow t1 t2) (at level 5, right associativity) : ty_scope.
Open Scope ty_scope.

Fixpoint teqb (t1 t2 : type) : bool :=
  match t1, t2 with
  | ⊥, ⊥ => true
  | T1 → t1, T2 → t2 => teqb T1 T2 && teqb t1 t2
  | _, _ => false
  end.
(**[]*)

Section TypeEq.
  Local Hint Resolve andb_true_intro : core.
  
  Lemma teqb_refl : forall t, teqb t t = true.
  Proof.
    intro t; induction t; simpl; intuition.
  Qed.
  
  Hint Rewrite Bool.andb_true_iff : core.
  
  Lemma eq_teqb : forall t1 t2, teqb t1 t2 = true -> t1 = t2.
  Proof.
    intro t1; induction t1; intros []; simpl;
      autorewrite with core; intuition;
        f_equal; eauto.
  Qed.
  
  Local Hint Resolve eq_teqb : core.
  Local Hint Resolve teqb_refl : core.
  Hint Rewrite teqb_refl : core.
  
  Lemma teqb_eq : forall t1 t2, teqb t1 t2 = true <-> t1 = t2.
  Proof.
    intuition; subst; trivial.
  Qed.
  
  Local Hint Resolve teqb_eq : core.
  Hint Rewrite teqb_eq : core.
  Local Hint Constructors Bool.reflect : core.
  
  Lemma teqb_reflect : forall t1 t2,
      Bool.reflect (t1 = t2) (teqb t1 t2).
  Proof.
    intros t1 t2.
    destruct (teqb t1 t2) eqn:Hteqb; auto.
    constructor. intros H.
    apply teqb_eq in H.
    rewrite H in Hteqb. discriminate.
  Qed.
End TypeEq.
