Require Import Coq.Arith.PeanoNat Coq.micromega.Lia Coq.Arith.Compare_dec.
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

(** Shifts free variables in [e] above a cutoff [c] up by [i]. *)
Fixpoint lift (c i : nat) (e : expr) : expr :=
  match e with
  | !n => ! match lt_dec n c with
           | left _ => n
           | right _ => n + i
           end
  | λ e => λ (lift (S c) i e)
  | e1 ⋅ e2 => (lift c i e1) ⋅ (lift c i e2)
  end.
(**[]*)

(** Substitution [e{esub/i}]. *)
Fixpoint subst (i : nat) (esub e : expr) : expr :=
  match e with
  | !n => match lt_eq_lt_dec i n with
         | inleft (left _) => ! (pred n)
         | inleft (right _) => lift 0 i esub
         | inright _ => !n
         end
  | λ e => λ (subst (S i) esub e)
  | e1 ⋅ e2 => (subst i esub e1) ⋅ (subst i esub e2)
  end.
(**[]*)

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

Section FrenchLemmas.
  (** The confluence proof reqiured
      evidence of some properties of
      shifting of de Bruijn indices.
      What these properties were was
      elusive to me, so I have looked
      to the work of a wise French person,
      who formalized the Calculus of Constructions in Coq.
      [http://www.lix.polytechnique.fr/~barras/CoqInCoq/Termes.html] *)

  Lemma lift0 : forall e k, lift k 0 e = e.
  Proof.
    induction e; intros; simpl;
      clean_compare; f_equal; auto 1.
  Qed.

  Lemma simpl_lift : forall e n p k i,
      i <= k + n -> k <= i ->
      lift i p (lift k n e) = lift k (p + n) e.
  Proof.
    induction e; intros; simpl;
      clean_compare; f_equal; auto 2; try lia.
    apply IHe; lia.
  Qed.

  Local Hint Extern 0 => rewrite simpl_lift by lia; reflexivity : core.

  Lemma permute_lift : forall e n k p i,
      i <= k -> lift i p (lift k n e) = lift (p + k) n (lift i p e).
  Proof.
    induction e; intros; simpl;
      clean_compare; f_equal; auto 2; try lia.
    rewrite IHe by lia. f_equal; lia.
  Qed.

  Local Hint Extern 0 => rewrite permute_lift by lia; reflexivity : core.
  
  Lemma simpl_subst : forall M N n p k,
      p <= n + k -> k <= p ->
      subst p N (lift k (S n) M) = lift k n M.
  Proof.
    induction M; intros; simpl;
      clean_compare; f_equal; auto 2; try lia.
    apply IHM; lia.
  Qed.

  Local Hint Extern 0 => rewrite simpl_subst by lia; reflexivity : core.
  
  Lemma commute_lift_subst : forall M N n p k,
      k <= p ->
      lift k n (subst p N M) = subst (n + p) N (lift k n M).
  Proof.
    induction M; intros; simpl;
      clean_compare;
      try (f_equal; auto 2; lia).
    f_equal; rewrite IHM by lia.
    f_equal; lia.
  Qed.

  Local Hint Extern 0 => rewrite commute_lift_subst by lia; reflexivity : core.

  Lemma distr_lift_subst : forall M N n p k,
      lift (p + k) n (subst p N M) = subst p (lift k n N) (lift (S (p + k)) n M).
  Proof.
    induction M; intros; simpl;
      clean_compare;
      try (f_equal; auto 2; lia).
    f_equal; rewrite <- IHM; f_equal; lia.
  Qed.

  Lemma distr_lift_subst0 : forall M N n k,
      lift k n (subst 0 N M) = subst 0 (lift k n N) (lift (S k) n M).
  Proof.
    intros. replace k with (0 + k) at 1 by lia.
    replace k with (0 + k) at 3 by lia.
    apply distr_lift_subst.
  Qed.
  
  Lemma distr_sub : forall M N P n p,
      subst (p + n) P (subst p N M) =
      subst p (subst n P N) (subst (S (p + n)) P M).
  Proof.
    induction M; intros; simpl;
      clean_compare; try (f_equal; auto 2; lia).
    f_equal; rewrite <- IHM; f_equal; lia.
  Qed.

  Lemma distr_sub0 : forall M N P n,
      subst n P (subst 0 N M) =
      subst 0 (subst n P N) (subst (S n) P M).
  Proof.
    intros. replace n with (0 + n) at 1 by lia.
    replace n with (0 + n) at 3 by lia.
    apply distr_sub.
  Qed.
End FrenchLemmas.

(** * Reduction Strategies *)

(** Non-determistic reduction. *)
Reserved Notation "e1 '-->' e2" (at level 40).

Inductive step : expr -> expr -> Prop :=
| step_beta e1 e2 :
    (λ e1) ⋅ e2 -->  subst 0 e2 e1
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

Inductive is_lambda : expr -> Prop :=
| IsLambda e : is_lambda (λ e).
(**[]*)

Ltac not_is_lambda_lambda :=
  match goal with
  | H: ~ is_lambda (λ _)
    |- _ => exfalso; apply H; constructor
  end.
(**[]*)

(** No beta-reduxes. *)
Inductive normal_form : expr -> Prop :=
| nf_var n :
    normal_form !n
| nf_app e1 e2 :
    ~ is_lambda e1 ->
    normal_form e1 ->
    normal_form e2 ->
    normal_form (e1 ⋅ e2)
| nf_lam e :
    normal_form e ->
    normal_form (λ e).
(**[]*)

Section NormalForm.
  Local Hint Extern 0 => not_is_lambda_lambda : core.
  Hint Constructors is_lambda : core.

  Ltac contra_step :=
    match goal with
    | H: ?e -->  _, IH : (forall _, ~ ?e -->  _)
      |- _ => apply IH in H; contradiction
    end.

  Hint Extern 0 => contra_step : core.

  Theorem normal_form_step : forall e e',
    normal_form e -> ~ e -->  e'.
  Proof.
    intros e e' HN; generalize dependent e';
      induction HN; intros ? H'; inv H'; auto 2.
  Qed.
End NormalForm.

Notation "e1 '-->*' e2" := (refl_trans_closure step e1 e2) (at level 40).

(** Termination condition. *)
Definition halts (e e' : expr) : Prop :=
  e -->* e' /\ normal_form e'.

Section Confluence.
  Local Hint Constructors step : core.
  Local Hint Constructors refl_trans_closure : core.
  Local Hint Resolve inject_trans_closure : core.

  Lemma reduce_lambda : forall e e',
      e -->* e' -> λ e -->* λ e'.
  Proof. intros e e' H; induction H; eauto 3. Qed.

  Lemma reduce_app_l : forall e1 e1' e2,
      e1 -->* e1' -> e1 ⋅ e2 -->* e1' ⋅ e2.
  Proof. intros e1 e1' e2 H; induction H; eauto 3. Qed.

  Lemma reduce_app_r : forall e1 e2 e2',
      e2 -->* e2' -> e1 ⋅ e2 -->* e1 ⋅ e2'.
  Proof. intros e1 e2 e2' H; induction H; eauto 3. Qed.

  Local Hint Resolve reduce_lambda : core.
  Local Hint Resolve reduce_app_l : core.
  Local Hint Resolve reduce_app_r : core.
  
  Lemma reduce_app : forall e1 e1' e2 e2',
      e1 -->* e1' -> e2 -->* e2' -> e1 ⋅ e2 -->* e1' ⋅ e2'.
  Proof.
    intros ? ? ? ? H1 H2; inv H1; inv H2; eauto 3.
    transitivity (e1' ⋅ e2); eauto 3.
  Qed.

  Local Hint Resolve reduce_app : core.
  
  Lemma sub_right_step : forall er er' el c,
      er -->  er' -> subst c el er -->  subst c el er'.
  Proof.
    intros ? ? el c Her;
      generalize dependent c;
      generalize dependent el;
      induction Her; intros; simpl; auto 2.
    rewrite distr_sub0; auto 1.
  Qed.

  Lemma lift_step : forall e e' c i,
      e -->  e' -> lift c i e -->  lift c i e'.
  Proof.
    intros ? ? c i He;
      generalize dependent i;
      generalize dependent c;
      induction He; intros; simpl; clean_compare.
    rewrite distr_lift_subst0; auto 1.
  Qed.

  Local Hint Resolve lift_step : core.
  
  Lemma sub_left_step : forall er el el' c,
      el -->  el' -> subst c el er -->* subst c el' er.
  Proof. induction er; intros; simpl; clean_compare. Qed.

  Local Hint Resolve sub_right_step : core.
  Local Hint Resolve sub_left_step : core.
  
  Theorem confluence : forall e e1 e2,
      e -->  e1 -> e -->  e2 -> exists e', e1 -->* e' /\ e2 -->* e'.
  Proof.
    intros ? ? e2 H1;
      generalize dependent e2;
      induction H1; intros ? H2; inv H2; eauto 7.
    - inv H3; eauto 6.
    - pose proof IHstep _ H0 as [? [? ?]]; eauto 5.
    - inversion H1; subst.
      pose proof IHstep _ H1 as [? [? ?]];
        clear IHstep; eauto 6.
    - pose proof IHstep _ H4 as [? [? ?]]; eauto 5.
    - pose proof IHstep _ H4 as [? [? ?]]; eauto 5.
  Qed.
End Confluence.

(** Deterministic reduction. *)

Inductive shallow_value : expr -> Prop :=
| shl_var n : shallow_value !n
| shl_lam e : shallow_value (λ e).
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
    (λ e1) ⋅ e2 ⟶  subst 0 e2 e1
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
    (λ e1) ⋅ e2 ==>  subst 0 e2 e1
| cbn_app_l e1 e1' e2 :
    e1 ==>  e1' ->
    e1 ⋅ e2 ==>  e1' ⋅ e2
where "e1 '==>' e2" := (cbn_reduce e1 e2).

(** Normal-order. *)

Reserved Notation "e1 '>->' e2" (at level 40).

Inductive normal_reduce : expr -> expr -> Prop :=
| normal_beta e1 e2 :
    (λ e1) ⋅ e2 >-> subst 0 e2 e1
| normal_lambda e e' :
    e >-> e' ->
    λ e >-> λ e'
| normal_app_r e1 e2 e2' :
    ~ is_lambda e1 ->
    normal_form e1 ->
    e2 >-> e2' ->
    e1 ⋅ e2 >-> e1 ⋅ e2'
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
    (λ e1) ⋅ e2 ⇢ subst 0 e2 e1
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

Section NormalFormReduce.
  Local Hint Constructors normal_form : core.
  Local Hint Extern 0 => not_is_lambda_lambda : core.

  Lemma normal_form_reduce : forall e e',
      e >-> e' -> ~ normal_form e.
  Proof.
    intros ? ? He Hnf; induction He; inv Hnf; auto 2.
  Qed.
End NormalFormReduce.

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
  | H: ?e >-> _, Hv: normal_form ?e
    |- _ => apply normal_form_reduce in H; contradiction
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
    Local Hint Extern 0 => contra_normal_value : core.
    
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
    - assert (a2 >->* e1 ⋅ e2) by auto; clear IHHe. admit.
    - assert (a2 >->* λ e) by auto; clear IHHe. admit.
  Abort.
End Normalizing.

Section Examples.
  Example omega_term : expr := λ !0 ⋅ !0.

  Local Hint Unfold omega_term : core.
  Local Hint Extern 0 => not_is_lambda_lambda : core.
  Local Hint Constructors is_lambda : core.

  Example omega_does_not_halt :
    forall e, ~ halts (omega_term ⋅ omega_term) e.
  Proof.
    intros e [Ho Hnf].
    remember (omega_term ⋅ omega_term) as oo eqn:Hoo.
    induction Ho; subst.
    - inv Hnf; apply H1; constructor.
    - apply IHHo; auto; clear a3 Hnf Ho IHHo; inv H; simpl; try reflexivity.
      + inv H3. inv H0; inv H3.
      + inv H3. inv H0; inv H3.
  Qed.
End Examples.
