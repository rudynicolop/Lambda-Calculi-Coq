Require Import Coq.Arith.PeanoNat.
Require Import Lambda.Util.

(** * De Bruijn Syntax of Terms *)

Inductive expr : Set :=
| Var (n : nat)
| Lam (e : expr)
| App (e1 e2 : expr).
(**[]*)

Declare Scope expr_scope.
Delimit Scope expr_scope with expr.

Notation "'λ' e" := (Lam e) (at level 10) : expr_scope.
Notation "e1 ⋅ e2" := (App e1 e2) (at level 8, left associativity) : expr_scope.
Notation "! n" := (Var n) (at level 0) : expr_scope.

Open Scope expr_scope.

(** Shifts free variables above a cutoff [c] using [op] (inc or dec). *)
Fixpoint shift (op : nat -> nat) (c : nat) (e : expr) : expr :=
  match e with
  | !n => if n <? c then !n else Var $ op n
  | λ e => Lam $ shift op (S c) e
  | e1 ⋅ e2 => App (shift op c e1) (shift op c e2)
  end.
(**[]*)

Definition shift_up : expr -> expr := shift S 0.

Definition shift_down : expr -> expr := shift pred 0.

(** Substitution [e{esub/m}]. *)
Fixpoint sub (m : nat) (esub e : expr) : expr :=
  match e with
  | !n => if m =? n then esub else !n
  | λ e => Lam $ sub (S m) (shift_up esub) e
  | e1 ⋅ e2 => App (sub m esub e1) $ sub m esub e2
  end.
(**[]*)

(** Beta-reduction [(λx.e1) e2 -> e1{e2/x}]. *)
Definition beta_reduce (e1 e2 : expr) : expr :=
  shift_down $ sub 0 (shift_up e2) e1.
(**[]*)

(** * Reduction Strategies *)

Inductive shallow_value : expr -> Prop :=
| shl_var n : shallow_value !n
| shl_lam e : shallow_value (λ e).
(**[]*)

Inductive is_lambda : expr -> Prop :=
| IsLambda e : is_lambda (λ e).
(**[]*)

Inductive deep_value : expr -> Prop :=
| dp_var n :
    deep_value !n
| dp_lam e :
    deep_value e ->
    deep_value (λ e)
| dp_app e1 e2 :
    ~ is_lambda e1 ->
    deep_value e1 ->
    deep_value e2 ->
    deep_value (e1 ⋅ e2).
(**[]*)

(** Call-by-value. *)

Reserved Notation "e1 '-->' e2" (at level 40).

Inductive cbv_reduce : expr -> expr -> Prop :=
| cbv_beta e1 e2 :
    shallow_value e2 ->
    (λ e1) ⋅ e2 -->  beta_reduce e1 e2
| cbv_right e1 e2 e2' :
    shallow_value e1 ->
    e2 -->  e2' ->
    e1 ⋅ e2 -->  e1 ⋅ e2'
| cbv_left e1 e1' e2 :
    e1 -->  e1' ->
    e1 ⋅ e2 -->  e1' ⋅ e2
where "e1 '-->' e2" := (cbv_reduce e1 e2).

(** Call-by-name. *)

Reserved Notation "e1 '==>' e2" (at level 40).

Inductive cbn_reduce : expr -> expr -> Prop :=
| cbn_beta e1 e2 :
    (λ e1) ⋅ e2 ==>  beta_reduce e1 e2
| cbn_step e1 e1' e2 :
    e1 ==>  e1' ->
    e1 ⋅ e2 ==>  e1' ⋅ e2
where "e1 '==>' e2" := (cbn_reduce e1 e2).

(** Normal-order. *)

Reserved Notation "e1 '>->' e2" (at level 40).

Inductive normal_reduce : expr -> expr -> Prop :=
| normal_beta e1 e2 :
    (λ e1) ⋅ e2 >-> beta_reduce e1 e2
| normal_lambda e e' :
    e >-> e' ->
    λ e >-> λ e'
| normal_right n e2 e2' :
    e2 >-> e2' ->
    !n ⋅ e2 >-> !n ⋅ e2'
| normal_left e1 e1' e2 :
    ~ is_lambda e1 ->
    e1 >-> e1' ->
    e1 ⋅ e2 >-> e1' ⋅ e2
where "e1 '>->' e2" := (normal_reduce e1 e2).

(** Applicative-order. *)

Reserved Notation "e1 '⇢' e2" (at level 40).

Inductive appl_reduce : expr -> expr -> Prop :=
| appl_beta e1 e2 :
    deep_value e1 ->
    deep_value e2 ->
    (λ e1) ⋅ e2 ⇢ beta_reduce e1 e2
| appl_lambda e e' :
    e ⇢ e' ->
    λ e ⇢ λ e'
| appl_right e1 e2 e2' :
    deep_value e1 ->
    e2 ⇢ e2' ->
    e1 ⋅ e2 ⇢ e1 ⋅ e2'
| appl_left e1 e1' e2 :
    e1 ⇢ e1' ->
    e1 ⋅ e2 ⇢ e1' ⋅ e2
where "e1 '⇢' e2" := (appl_reduce e1 e2).
(**[]*)

Ltac not_is_lambda_lambda :=
  match goal with
  | H: ~ is_lambda (λ _)
    |- _ => exfalso; apply H; constructor
  end.
(**[]*)

Ltac cbv_step_lambda :=
  match goal with
  | H: λ _ -->  _ |- _ => inv H
  end.
(**[]*)

Ltac cbn_step_lambda :=
  match goal with
  | H: λ _ ==>   _ |- _ => inv H
  end.
(**[]*)

Ltac normal_step_app_var :=
  match goal with
  | H: !_ >-> _ |- _ => inv H
  end.
(**[]*)

Section Shallow.
  Local Hint Constructors shallow_value : core.

  Lemma cbv_reduce_value : forall e e',
      e -->  e' -> ~ shallow_value e.
  Proof. intros ? ? H Hv; inv H; inv Hv. Qed.

  Lemma cbn_reduce_value : forall e e',
      e ==>  e' -> ~ shallow_value e.
  Proof. intros ? ? H Hv; inv H; inv Hv. Qed.
End Shallow.

Section Deep.
  Local Hint Constructors deep_value : core.
  Local Hint Extern 0 => not_is_lambda_lambda : core.

  Lemma appl_reduce_value : forall e e',
      e ⇢ e' -> ~ deep_value e.
  Proof.
    intros ? ? H Hv; induction H; inv Hv; auto 2.
  Qed.

  Lemma normal_reduce_value : forall e e',
      e >-> e' -> ~ deep_value e.
  Proof.
    intros ? ? H Hv; induction H; inv Hv; auto 2.
  Qed.
End Deep.

Ltac contra_cbv_value :=
  match goal with
  | H: ?e -->  _, Hv: shallow_value ?e
    |- _ => apply cbv_reduce_value in H; contradiction
  end.
(**[]*)

Ltac contra_appl_value :=
  match goal with
  | H: ?e ⇢ _, Hv: deep_value ?e
    |- _ => apply appl_reduce_value in H; contradiction
  end.
(**[]*)

Ltac contra_cbn_value :=
  match goal with
  | H: ?e ==>  _, Hv: shallow_value ?e
    |- _ => apply cbn_reduce_value in H; contradiction
  end.
(**[]*)

Ltac contra_normal_value :=
  match goal with
  | H: ?e >-> _, Hv: deep_value ?e
    |- _ => apply normal_reduce_value in H; contradiction
  end.
(**[]*)

Section Determinism.
  Section CBV.
    Local Hint Extern 0 => contra_cbv_value : core.
    Local Hint Extern 0 => cbv_step_lambda : core.

    Theorem cbv_deterministic : deterministic cbv_reduce.
    Proof. ind_det; f_equal; eauto 2. Qed.
  End CBV.

  Section CBN.
    Local Hint Extern 0 => cbn_step_lambda : core.
    
    Theorem cbn_deterministic : deterministic cbn_reduce.
    Proof. ind_det; f_equal; eauto 2. Qed.
  End CBN.

  Local Hint Extern 0 => not_is_lambda_lambda : core.
  
  Section NORMAL.
    Local Hint Extern 0 => normal_step_app_var : core.
    
    Theorem normal_deterministic : deterministic normal_reduce.
    Proof. ind_det; f_equal; eauto 2. Qed.
  End NORMAL.

  Section APPL.
    Local Hint Extern 0 => contra_appl_value : core.

    Local Hint Extern 1 =>
    match goal with
    | H: λ ?e ⇢ _, Hv: deep_value ?e
      |- _ => inv H
    end : core.    
    
    Theorem appl_deterministic : deterministic appl_reduce.
    Proof. ind_det; f_equal; eauto 2. Qed.
  End APPL.
End Determinism.

Section ValueEXM.
  Local Hint Constructors is_lambda : core.
  
  Lemma is_lambda_exm : forall e,
    is_lambda e \/ ~ is_lambda e.
  Proof. intros []; auto 2; right; intros H; inv H. Qed.

  Remove Hints is_lambda : core.
  Local Hint Constructors shallow_value : core.

  Lemma shallow_value_exm : forall e,
      shallow_value e \/ ~ shallow_value e.
  Proof. intros []; auto 2; right; intros H; inv H. Qed.

  Remove Hints shallow_value : core.
  Local Hint Constructors deep_value : core.
  (*Local Hint Resolve is_lambda_exm : core.*)

  Lemma deep_value_exm : forall e,
      deep_value e \/ ~ deep_value e.
  Proof.
    induction e as
        [ n
        | e [IHe | IHe]
        | e1 [IHe1 | IHe1] e2 [IHe2 | IHe2]]; auto 3;
    try match goal with
        | H: ~ deep_value ?e |- context [?e]
          => right; intros H'; inv H'; contradiction
        end.
    - destruct (is_lambda_exm e1) as [He1 | He1]; auto 3.
      right; intros H'; inv H'; contradiction.
  Qed.
End ValueEXM.

Notation "e1 '-->*' e2" := (refl_trans_closure cbv_reduce e1 e2) (at level 40).
Notation "e1 '==>*' e2" := (refl_trans_closure cbn_reduce e1 e2) (at level 40).

Section Confluence.
  Local Hint Resolve refl_closure : core.
  Local Hint Resolve inject_trans_closure : core.
  
  Section CBV_CBN.
    Local Hint Extern 0 => cbv_step_lambda : core.
    Local Hint Extern 0 => cbn_step_lambda : core.
    Local Hint Constructors cbv_reduce : core.
    Local Hint Constructors cbn_reduce : core.
    Local Hint Extern 0 => contra_cbn_value : core.
    
    Theorem cbv_cbn_confluent : forall e e1 e2,
      e -->  e1 -> e ==>  e2 -> exists e', e1 -->* e' /\ e2 ==>* e'.
    Proof.
      intros e e1 e2 Hcbv.
      generalize dependent e2.
      induction Hcbv; intros ? Hcbn; inv Hcbn; eauto 3.
      - clear IHHcbv; destruct (shallow_value_exm e2') as [Hv | Hv].
        + exists (beta_reduce e3 e2'). split.
          * apply trans_closure with (beta_reduce e3 e2'); auto 2.
          * unfold beta_reduce, "$". admit.
        + admit.
      - apply IHHcbv in H2 as [e'' [Hcbv' Hcbn']]; clear IHHcbv.
        exists (e'' ⋅ e2); split.
        + clear e1 e1'0 Hcbn' Hcbv.
          induction Hcbv'; auto 1.
          transitivity (a2 ⋅ e2); auto 3.
        + clear e1 e1' Hcbv Hcbv'.
          induction Hcbn'; auto 1.
          transitivity (a2 ⋅ e2); auto 3.
    Admitted.
  End CBV_CBN.
End Confluence.
