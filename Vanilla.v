Require Import Coq.Arith.PeanoNat Coq.micromega.Lia.
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
  | !n =>  ! if n <? c then n else op n
  | λ e => λ (shift op (S c) e)
  | e1 ⋅ e2 => (shift op c e1) ⋅ (shift op c e2)
  end.
(**[]*)

Definition shift_up : expr -> expr := shift S 0.

Definition shift_down : expr -> expr := shift pred 0.

Lemma shift_c_down_up : forall e c,
    shift pred c (shift S c e) = e.
Proof.
  induction e; intros; simpl; f_equal; auto.
  destruct (n <? c) eqn:Hni;
    simpl; try rewrite Hni; auto.
  assert (H: S n <? c = false).
  { rewrite Nat.ltb_ge in *; lia. }
  rewrite H; reflexivity.
Qed.

Lemma shift_down_up : forall e,
    shift_down (shift_up e) = e.
Proof.
  intros e; unfold shift_down, shift_up.
  apply shift_c_down_up.
Qed.

(** Substitution [e{esub/m}]. *)
Fixpoint sub (m : nat) (esub e : expr) : expr :=
  match e with
  | !n => if m =? n then esub else !n
  | λ e => λ (sub (S m) (shift_up esub) e)
  | e1 ⋅ e2 => (sub m esub e1) ⋅ (sub m esub e2)
  end.
(**[]*)

(** Beta-reduction [(λx.e1) e2 -> e1{e2/x}]. *)
Definition beta_reduce (e1 e2 : expr) : expr :=
  shift_down (sub 0 (shift_up e2) e1).
(**[]*)

Lemma shift_sub : forall e es m,
    shift pred m (sub m es (shift S m e)) = e.
Proof.
  induction e; intros es m; simpl; f_equal; auto.
  - destruct (n <? m) eqn:Hnm.
    + assert (m =? n = false).
      { rewrite Nat.ltb_lt in Hnm.
        rewrite Nat.eqb_neq. lia. }
      rewrite H; simpl; rewrite Hnm; reflexivity.
    + destruct (m =? S n) eqn:HmSn; simpl.
      * rewrite Nat.ltb_ge in Hnm.
        rewrite Nat.eqb_eq in HmSn; subst. lia.
      * assert (S n <? m = false).
        { rewrite Nat.ltb_ge in *.
          rewrite Nat.eqb_neq in *. lia. }
        rewrite H; reflexivity.
Qed.

(** * Reduction Strategies *)

(** Non-determistic reduction. *)
Reserved Notation "e1 '-->' e2" (at level 40).

Inductive step : expr -> expr -> Prop :=
| step_beta e1 e2 :
    (λ e1) ⋅ e2 -->  beta_reduce e1 e2
| step_lambda e e' :
    e -->  e' ->
    λ e -->  λ e'
| step_app_l e1 e1' e2 :
    e1 -->  e1' ->
    e1 ⋅ e2 -->  e1' ⋅ e2
| step_app_r e1 e2 e2' :
    e2 -->  e2' ->
    e1 ⋅ e2 -->  e1 ⋅ e2'
where "e1 '-->' e2" := (step e1 e2).
(**[]*)

(** No beta-reduxes. *)
Inductive normal_form : expr -> Prop :=
| nf_var n :
    normal_form !n
| nf_app n e :
    normal_form e ->
    normal_form (!n ⋅ e)
| nf_lam e :
    normal_form e ->
    normal_form (λ e).
(**[]*)

Section NormalForm.
  Theorem normal_form_step : forall e e',
    normal_form e -> ~ e -->  e'.
  Proof.
    intros e e' HN; generalize dependent e';
      induction HN; intros ? H'; inv H'.
    - inv H2.
    - apply IHHN in H2; contradiction.
    - apply IHHN in H0; contradiction.
  Qed.
End NormalForm.

Notation "e1 '-->*' e2" := (refl_trans_closure step e1 e2) (at level 40).

(** Termination condition. *)
Definition halts (e e' : expr) : Prop :=
  e -->* e' /\ normal_form e'.

Section Confluence.
  Local Hint Constructors step : core.    
  Local Hint Resolve inject_trans_closure : core.
  Local Hint Resolve refl_closure : core.

  Lemma reduce_lambda : forall e e',
      e -->* e' -> λ e -->* λ e'.
  Proof.
    intros e e' H; induction H; auto 1.
    transitivity (λ a2); auto 3.
  Qed.

  Lemma reduce_app_l : forall e1 e1' e2,
      e1 -->* e1' -> e1 ⋅ e2 -->* e1' ⋅ e2.
  Proof.
    intros e1 e1' e2 H; induction H; auto 1.
    transitivity (a2 ⋅ e2); auto 3.
  Qed.

  Lemma reduce_app_r : forall e1 e2 e2',
      e2 -->* e2' -> e1 ⋅ e2 -->* e1 ⋅ e2'.
  Proof.
    intros e1 e2 e2' H; induction H; auto 1.
    transitivity (e1 ⋅ a2); auto 3.
  Qed.

  Local Hint Resolve reduce_lambda : core.
  Local Hint Resolve reduce_app_l : core.
  Local Hint Resolve reduce_app_r : core.

  Conjecture beta_reduce_inner_l : forall e1 e1' e2,
      e1 -->  e1' -> beta_reduce e1 e2 -->* beta_reduce e1' e2.

  Conjecture beta_reduce_inner_r : forall e1 e2 e2',
      e2 -->  e2' -> beta_reduce e1 e2 -->* beta_reduce e1 e2'.
  
  Theorem confluence : forall e e1 e2,
      e -->  e1 -> e -->  e2 -> exists e', e1 -->* e' /\ e2 -->* e'.
  Proof.
    intros ? ? e2 H1;
      generalize dependent e2;
      induction H1; intros ? H2; inv H2; eauto 3.
    - inv H3; exists (beta_reduce e' e2); split; auto.
      apply beta_reduce_inner_l; assumption.
    - exists (beta_reduce e1 e2'); split; auto.
      apply beta_reduce_inner_r; assumption.
    - pose proof IHstep _ H0 as [? [? ?]]; eauto.
    - inversion H1; subst.
      pose proof IHstep _ H1 as [? [? ?]]; clear IHstep.
      exists (beta_reduce e' e2); split; auto.
      apply beta_reduce_inner_l; assumption.
    - pose proof IHstep _ H4 as [? [? ?]]; eauto.
    - clear IHstep. exists (e1' ⋅ e2'); split; eauto.
    - clear IHstep. exists (beta_reduce e3 e2'); split; auto.
      apply beta_reduce_inner_r; assumption.
    - clear IHstep. exists (e1' ⋅ e2'); split; eauto.
    - pose proof IHstep _ H4 as [? [? ?]]; eauto.
  Qed.

  Local Hint Resolve confluence : core.
  Local Hint Constructors refl_trans_closure : core.

  Corollary confluence_star :  forall e e1 e2,
      e -->* e1 -> e -->* e2 -> exists e', e1 -->* e' /\ e2 -->* e'.
  Proof.
    (*intros ? ? ? He1 He2; inv He1; inv He2; eauto.*)
    (*intros e e1 e2 He1; generalize dependent e2;
      induction He1; intros ? He2; inv He2; eauto.
    apply IHHe1.
    pose proof IHHe1 _ He1 as [e' [He1' He2']].*)
  Abort.
End Confluence.

(** Deterministic reduction. *)

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

Reserved Notation "e1 '⟶' e2" (at level 40).

Inductive cbv_reduce : expr -> expr -> Prop :=
| cbv_beta e1 e2 :
    shallow_value e2 ->
    (λ e1) ⋅ e2 ⟶  beta_reduce e1 e2
| cbv_app_r e1 e2 e2' :
    shallow_value e1 ->
    e2 ⟶  e2' ->
    e1 ⋅ e2 ⟶  e1 ⋅ e2'
| cbv_app_l e1 e1' e2 :
    e1 ⟶  e1' ->
    e1 ⋅ e2 ⟶   e1' ⋅ e2
where "e1 '⟶' e2" := (cbv_reduce e1 e2).

(** Call-by-name. *)

Reserved Notation "e1 '==>' e2" (at level 40).

Inductive cbn_reduce : expr -> expr -> Prop :=
| cbn_beta e1 e2 :
    (λ e1) ⋅ e2 ==>  beta_reduce e1 e2
| cbn_app_l e1 e1' e2 :
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
| normal_app_r n e2 e2' :
    e2 >-> e2' ->
    !n ⋅ e2 >-> !n ⋅ e2'
| normal_app_l e1 e1' e2 :
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
| appl_app_r e1 e2 e2' :
    deep_value e1 ->
    e2 ⇢ e2' ->
    e1 ⋅ e2 ⇢ e1 ⋅ e2'
| appl_app_l e1 e1' e2 :
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
  | H: λ _ ⟶  _ |- _ => inv H
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
      e ⟶   e' -> ~ shallow_value e.
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
  | H: ?e ⟶  _, Hv: shallow_value ?e
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

Section InjectStep.
  Local Hint Constructors step : core.

  Theorem cbv_step : forall e e', e ⟶  e' -> e -->  e'.
  Proof. intros ? ? H; induction H; auto 2. Qed.

  Theorem cbn_step : forall e e', e ==>  e' -> e -->  e'.
  Proof. intros ? ? H; induction H; auto 2. Qed.

  Theorem normal_step : forall e e', e >-> e' -> e -->  e'.
  Proof. intros ? ? H; induction H; auto 2. Qed.

  Theorem appl_step : forall e e', e ⇢ e' -> e -->  e'.
  Proof. intros ? ? H; induction H; auto 2. Qed.
End InjectStep.

Notation "e1 >->* e2" := (refl_trans_closure normal_reduce e1 e2) (at level 40).

Section Normalizing.
  Local Hint Resolve inject_trans_closure : core.
  Local Hint Resolve refl_closure : core.
  Local Hint Constructors normal_reduce : core.

  Lemma normal_reduce_lambda : forall e e',
      e >->* e' -> λ e >->* λ e'.
  Proof.
    intros e e' H; induction H; auto 1.
    transitivity (λ a2); auto 3.
  Qed.

  Lemma normal_reduce_app_l : forall e1 e1' e2,
      e1 >->* e1' -> e1 ⋅ e2 >->* e1' ⋅ e2.
  Proof.
    intros e1 e1' e2 H; induction H; auto 1.
    transitivity (a2 ⋅ e2); auto 3.
    apply inject_trans_closure.
    apply normal_app_l.
  Abort.

  Lemma normal_reduce_app_r : forall e1 e2 e2',
      e2 >->* e2' -> e1 ⋅ e2 >->* e1 ⋅ e2'.
  Proof.
    intros e1 e2 e2' H; induction H; auto 1.
    transitivity (e1 ⋅ a2); auto 3.
  Abort.

  Local Hint Resolve normal_reduce_lambda : core.
  (*Local Hint Resolve normal_reduce_app_l : core.*)
  (*Local Hint Resolve normal_reduce_app_r : core.*)
  Local Hint Constructors normal_form : core.
  
  Theorem normal_halts : forall e e',
    halts e e' -> e >->* e'.
  Proof.
    intros e e' [He Hnf].
    induction He; inv Hnf; auto.
    - assert (a2 >->* !n) by auto; clear IHHe. admit.
    - assert (a2 >->* !n ⋅ e) by auto; clear IHHe. admit.
    - assert (a2 >->* λ e) by auto; clear IHHe. admit.
  Abort.
End Normalizing.

Section Examples.
  Example omega_term : expr := λ !0 ⋅ !0.

  Example omega_does_not_halt :
    forall e, ~ halts (omega_term ⋅ omega_term) e.
  Proof.
    intros e [Ho Hnf].
    remember (omega_term ⋅ omega_term) as oo eqn:Hoo.
    induction Ho; subst.
    - inv Hnf.
    - apply IHHo; auto; clear a3 Hnf Ho IHHo; inv H; simpl; try reflexivity.
      + inv H3. inv H0. inv H3. inv H3.
      + inv H3. inv H0. inv H3. inv H3.
  Qed.
End Examples.
