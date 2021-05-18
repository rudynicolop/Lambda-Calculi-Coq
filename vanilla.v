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
  | !n => Var $ if n <? c then n else op n
  | λ e => Lam $ shift op (S c) e
  | e1 ⋅ e2 => App (shift op c e1) (shift op c e2)
  end.
(**[]*)

Lemma shif_id : forall e c,
    shift (fun n => n) c e = e.
Proof.
  induction e; intros; simpl; unfold "$"; f_equal; auto.
  destruct (n <? c); reflexivity.
Qed.

Lemma shift_compose : forall f h e c,
    shift (compose f h) c e = compose (shift f c) (shift h c) e.
Proof.
  unfold compose. induction e; intros; simpl; unfold "$"; f_equal; auto.
  destruct (n <? c) eqn:Hnc; try rewrite Hnc; auto.
Abort.

Definition shift_up : expr -> expr := shift S 0.

Definition shift_down : expr -> expr := shift pred 0.

Lemma shift_c_down_comm : forall e c1 c2,
    shift pred c1 (shift pred c2 e) = shift pred c2 (shift pred c1 e).
Proof.
  induction e; intros; simpl;  unfold "$" in *; f_equal; auto.
  (*destruct (n <? c2) eqn:Hc2; destruct (n <? c1) eqn:Hc1;
    simpl; repeat rewrite Hc1; repeat rewrite Hc2; auto; unfold "$".
    + assert (H: pred n <? c2 = true).
      { rewrite Nat.ltb_lt in *. lia. }
      rewrite H; reflexivity.
    + assert (H: pred n <? c1 = true).
      { rewrite Nat.ltb_lt in *. lia. }
      rewrite H; reflexivity.
    + destruct n as [| n]; simpl.
      * destruct (0 <? c1); destruct (0 <? c2); reflexivity.
      * rewrite Nat.ltb_ge in *.
        Search (_ <? _ = negb (_ <=? _)).
        repeat rewrite Nat.ltb_antisym.
        Search (if (negb _) then _ else _).
        repeat rewrite Bool.if_negb.
        destruct (c1 <=? n) eqn:Hc1';
          destruct (c2 <=? n) eqn:Hc2'; try reflexivity;
            rewrite Nat.leb_le in *;
            rewrite Nat.leb_gt in *.
        ** assert (c2 = S n) by lia; subst. admit.
        ** admit.*)
Abort.

Lemma shift_c_down_comm_0 : forall e c,
    shift pred c (shift pred 0 e) = shift pred 0 (shift pred c e).
Proof.
  induction e; intros; simpl; unfold "$"; f_equal; auto.
Abort.

Lemma shift_c_down_up : forall e c,
    shift pred c (shift S c e) = e.
Proof.
  induction e; intros; simpl; unfold "$" in *; f_equal; auto.
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
  | λ e => Lam $ sub (S m) (shift_up esub) e
  | e1 ⋅ e2 => App (sub m esub e1) $ sub m esub e2
  end.
(**[]*)

(*Lemma sub_shift_c_down_up : forall c m esub e,
    shift pred c (sub m (shift S c m esub) e) =*)

(** Beta-reduction [(λx.e1) e2 -> e1{e2/x}]. *)
Definition beta_reduce (e1 e2 : expr) : expr :=
  shift_down $ sub 0 (shift_up e2) e1.
(**[]*)

Lemma sub_beta_reduce : forall e1 e2 m es,
    sub m es (beta_reduce e1 e2) =
    beta_reduce
      (sub (S m) (shift_up es) e1)
      (sub m es e2).
Proof.
  unfold beta_reduce, "$"; simpl.
  induction e1
    as [ [| n1]
       | e1 IHe1
       | e11 IHe11 e21 IHe21 ]; intros; simpl.
  - repeat rewrite shift_down_up. reflexivity.
  - destruct (m =? n1) eqn:Hmn1; auto.
Abort.

Lemma shift_sub : forall e es m,
    shift pred m (sub m es (shift S m e)) = e.
Proof.
  induction e; intros es m; simpl; f_equal; unfold "$"; auto.
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
  - rewrite IHe; reflexivity.
Qed.

Lemma sub_beta_c : forall e1 e2 es c m,
  sub m es (shift pred c (sub c (shift S c e2) e1)) =
  shift pred c (sub c (shift S c (sub m es e2)) (sub (S m) (shift S c es) e1)).
Proof.
  induction e1; intros e2 es c m; simpl; unfold shift_up, "$".
  - admit.
  - f_equal. Fail rewrite <- IHe1. admit.
  - f_equal; auto.
Abort.
  (*induction e1; intros [] es c m; simpl; unfold "$".
  - destruct (c =? n) eqn:Hcn; destruct (n0 <? c) eqn:Hcn0;
      destruct (m =? n0) eqn:Hmn0; destruct n as [| n];
        simpl; repeat rewrite Hcn; repeat rewrite Hcn0;
          repeat rewrite Hmn0; simpl; unfold "$"; admit.*)
    (*+ rewrite shift_c_down_up; reflexivity.
    + rewrite Nat.eqb_eq in *; subst.
      destruct (n0 =? n) eqn:Hnn0; simpl.
      * rewrite shift_sub. reflexivity.
      * rewrite Nat.eqb_refl;
          rewrite shift_c_down_up; reflexivity.
    + rewrite Nat.eqb_eq in *; subst.
      rewrite Nat.ltb_lt in Hcn0. lia.
    + rewrite Nat.eqb_eq in *; subst.
      destruct (m =? n) eqn:Hmn; simpl; auto.
      * rewrite Nat.ltb_lt in *;
          rewrite Nat.eqb_eq in *;
          rewrite Nat.eqb_neq in *; subst. admit.
      * rewrite Nat.eqb_refl; simpl; rewrite Hcn0; reflexivity.
    +*) 
  (*- destruct (c =? n) eqn:Hcn; destruct n as [| n];
      simpl; unfold shift_up, "$"; try rewrite Hcn; simpl; unfold "$"; f_equal.
    + repeat rewrite shift_c_down_up. reflexivity.
    + rewrite Nat.eqb_eq in *; subst.
      repeat rewrite shift_c_down_up.
      destruct (m =? n) eqn:Hmn; simpl.
      * rewrite Nat.eqb_eq in *; subst.
        rewrite shift_sub. admit.
      * rewrite Nat.eqb_refl; simpl; unfold "$"; f_equal.
        rewrite shift_c_down_up. reflexivity.
    + destruct (0 <? c) eqn:Hcn'; destruct (m =? 0) eqn:Hm0; auto; admit.
    + destruct (S n <? c) eqn:HSnc;
        destruct (m =? n) eqn:Hmn.
      * rewrite Nat.eqb_eq in *; subst.
        assert (HnSn: n =? S n = false).
        { rewrite Nat.eqb_neq; lia. }
        rewrite HnSn. rewrite shift_sub. admit.
      * destruct (m =? S n) eqn:HmSn.
        ** rewrite Nat.eqb_eq in *; subst.
           simpl; rewrite Hcn; simpl; rewrite HSnc. admit.
        ** simpl; rewrite Hcn; simpl; rewrite HSnc; reflexivity.
      * rewrite Nat.eqb_eq in *; subst.
        rewrite shift_sub. reflexivity.
      * simpl; rewrite Hcn; simpl; rewrite HSnc; reflexivity.
  - admit.
  - admit.*)

(** * Reduction Strategies *)

(** Non-determistic reduction. *)
Module NonDet.
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

  Notation "e1 '-->*' e2" := (refl_trans_closure step e1 e2) (at level 40).

  Section Conf.
    Local Hint Constructors step : core.
      
    Lemma sub_reduce_sub : forall e e' es m,
        e -->  e' -> sub m es e -->  sub m es e'.
    Proof.
      intros e e' es m H; generalize dependent m;
        generalize dependent es;
        induction H; intros es m;
          simpl; unfold "$"; eauto.
      assert (sub m es (beta_reduce e1 e2) =
              beta_reduce (sub (S m) (shift_up es) e1) (sub m es e2)).
      { unfold beta_reduce, shift_down, shift_up, "$".
        induction e1; simpl; unfold "$".
        - admit.
        - f_equal. Fail rewrite <- IHe1. admit.
        - f_equal; auto.
    Abort.

    Lemma shift_pred_reduce : forall e e' c,
        e -->  e' -> shift pred c e -->  shift pred c e'.
    Proof.
      intros e e' c H; generalize dependent c;
        induction H; intros c; simpl; unfold "$"; auto.
      unfold beta_reduce, shift_down.
    Abort.

    Lemma shift_sub_reduce_term : forall e1 e2 e c,
        e1 -->  e2 ->
        shift pred c (sub c e e1) -->  shift pred c (sub c e e2).
    Proof.
      intros e1 e2 e c H; generalize dependent c;
        generalize dependent e;
        induction H; intros; simpl; unfold "$"; auto.
      - assert (shift pred c (sub c e (beta_reduce e1 e2)) =
                beta_reduce
                  (shift pred (S c) (sub (S c) (shift_up e) e1))
                  (shift pred c (sub c e e2))).
        { unfold beta_reduce, shift_up, shift_down, "$"; simpl.
    Abort.
    
    Lemma beta_reduce_subterm_l : forall e1 e2 e,
        e1 -->  e2 ->
        beta_reduce e1 e -->  beta_reduce e2 e.
    Proof.
      intros e1 e2 e H; generalize dependent e;
        induction H; intros;
          unfold beta_reduce, shift_down, shift_up, "$" in *; simpl in *;
            unfold "$" in *; auto.
      - admit.
      - constructor. admit.
    Abort.
    
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

    Theorem confluence : forall e e1 e2,
        e -->  e1 -> e -->  e2 -> exists e', e1 -->* e' /\ e2 -->* e'.
    Proof.
      intros ? ? e2 H1;
        generalize dependent e2;
        induction H1; intros ? H2; inv H2; eauto 3.
      - inv H3. exists (beta_reduce e' e2); split; auto. admit.
      - exists (beta_reduce e1 e2'); split; auto. admit.
      - pose proof IHstep _ H0 as [? [? ?]]; eauto.
      - inversion H1; subst.
        pose proof IHstep _ H1 as [? [? ?]]; clear IHstep.
        exists (beta_reduce e' e2); split; auto. admit.
      - pose proof IHstep _ H4 as [? [? ?]]; eauto.
      - clear IHstep. exists (e1' ⋅ e2'); split; eauto.
      - clear IHstep. exists (beta_reduce e3 e2'); split; auto. admit.
      - clear IHstep. exists (e1' ⋅ e2'); split; eauto.
      - pose proof IHstep _ H4 as [? [? ?]]; eauto.
    Admitted.
End Conf.        
End NonDet.

(** Deterministic reduction. *)
Module Det.
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
End Det.
