Require Import Lambda.Util.
Require Import Coq.Lists.List Coq.Arith.PeanoNat Coq.micromega.Lia.
Import ListNotations.

(** * De Bruijn Syntax *)

Inductive type : Set :=
| Base
| Arrow (t1 t2 : type).
(**[]*)

Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Notation "⊥" := Base (at level 0) : ty_scope.
Notation "t1 '→' t2" := (Arrow t1 t2) (at level 5, right associativity) : ty_scope.
Open Scope ty_scope.

Inductive expr : Set :=
| Var (n : nat)
| Lam (t : type) (e : expr)
| App (e1 e2 : expr).
(**[]*)

Declare Scope expr_scope.
Delimit Scope expr_scope with expr.
Notation "'λ' t '⇒' e" := (Lam t e) (at level 10) : expr_scope.
Notation "e1 ⋅ e2" := (App e1 e2) (at level 8, left associativity) : expr_scope.
Notation "! n" := (Var n) (at level 0) : expr_scope.
Open Scope expr_scope.

Example id : expr := λ ⊥ ⇒ !0.
Example f2' : expr := λ ⊥ → ⊥ ⇒ λ ⊥ ⇒ !1 ⋅ !0.
Example t1 : type := (⊥ → ⊥) → ⊥ → ⊥.

(** * Static Semantics *)

Reserved Notation "Γ '⊢' e '∈' τ" (at level 40).

Inductive check (Γ : list type) : expr -> type -> Prop :=
| chk_var n τ :
    nth_error Γ n = Some τ ->
    Γ ⊢ !n ∈ τ
| chk_lam τ τ' e :
    (τ :: Γ) ⊢ e ∈ τ' ->
    Γ ⊢ λ τ ⇒ e ∈ τ → τ'
| chk_app τ τ' e1 e2 :
    Γ ⊢ e1 ∈ τ → τ' ->
    Γ ⊢ e2 ∈ τ ->
    Γ ⊢ e1 ⋅ e2 ∈ τ'
where "Γ '⊢' e '∈' τ" := (check Γ e τ).
(**[]*)

Theorem type_unique : forall Γ e τ1 τ2,
    Γ ⊢ e ∈ τ1 -> Γ ⊢ e ∈ τ2 -> τ1 = τ2.
Proof.
  intros g e; generalize dependent g;
    induction e; intros ? ? ? Ht1 Ht2; inv Ht1; inv Ht2.
  - rewrite H0 in H1; inv H1; reflexivity.
  - f_equal; eauto 2.
  - pose proof IHe1 _ _ _ H1 H2 as IH1;
      pose proof IHe2 _ _ _ H3 H5 as IH2.
    inv IH1; reflexivity.
Qed.

(** * Dynamic Semantics *)

Inductive is_lambda : expr -> Prop :=
| lambda_is_lambda t e : is_lambda (λ t ⇒ e).
(**[]*)

(** Normal-form. *)
Inductive normal : expr -> Prop :=
| nf_var n :
    normal !n
| nf_lam τ e :
    normal e ->
    normal (λ τ ⇒ e)
| nf_app e1 e2 :
    ~ is_lambda e1 ->
    normal e1 ->
    normal e2 ->
    normal (e1 ⋅ e2).
(**[]*)

(** TODO: this implementation is
    difficult to prove correct.
    I need a single [Fixpoint] to perform substitution/beta-reduction. *)

(** Shifts free variables above a cutoff [c] using [op] (inc or dec). *)
Fixpoint shift (op : nat -> nat) (c : nat) (e : expr) : expr :=
  match e with
  | !n =>  ! if n <? c then n else op n
  | λ τ ⇒ e => λ τ ⇒ (shift op (S c) e)
  | e1 ⋅ e2 => (shift op c e1) ⋅ (shift op c e2)
  end.
(**[]*)

Lemma shift_c_down_up : forall e c,
    shift pred c (shift S c e) = e.
Proof.
  induction e; intros; simpl; f_equal; auto 1.
  destruct (n <? c) eqn:Hnc;
    simpl; try rewrite Hnc; try reflexivity.
  assert (HSnc: S n <? c = false).
  { rewrite Nat.ltb_ge in *; lia. }
  rewrite HSnc; reflexivity.
Qed.

(*Definition shift_up : expr -> expr := shift S 0.*)

(*Definition shift_down : expr -> expr := shift pred 0.*)

(*Lemma shift_down_up : forall e,
    shift_down (shift_up e) = e.
Proof.
  unfold shift_down, shift_up.
  exact (fun e => shift_c_down_up e 0).
Qed.*)

(** Substitution [e{esub/m}]. *)
Fixpoint sub (m : nat) (esub e : expr) : expr :=
  match e with
  | !n => if m =? n then esub else !n
  | λ τ ⇒ e => λ τ ⇒ (sub (S m) (shift S 0 esub) e)
  | e1 ⋅ e2 => (sub m esub e1) ⋅ (sub m esub e2)
  end.
(**[]*)

Definition beta_reduce_c (c : nat) (e1 e2 : expr) : expr :=
  shift pred c (sub c (shift S 0 e2) e1).
(**[]*)

(** Beta-reduction [(λx.e1) e2 -> e1{e2/x}]. *)
Definition beta_reduce (e1 e2 : expr) : expr := beta_reduce_c 0 e1 e2.
  (*shift_down (sub 0 (shift_up e2) e1).*)
(**[]*)

(** Normal-order Reduction. *)

Reserved Notation "e1 '-->' e2" (at level 40).

Inductive step : expr -> expr -> Prop :=
| step_beta τ e1 e2 :
    (λ τ ⇒ e1) ⋅ e2 -->  beta_reduce e1 e2
| step_lambda τ e e' :
    e -->  e' ->
    λ τ ⇒ e -->  λ τ ⇒ e'
| step_app_r e1 e2 e2' :
    ~ is_lambda e1 ->
    normal e1 ->
    e2 -->  e2' ->
    e1 ⋅ e2 -->  e1 ⋅ e2'
| step_app_l e1 e1' e2 :
    ~ is_lambda e1 ->
    e1 -->  e1' ->
    e1 ⋅ e2 -->  e1' ⋅ e2
where "e1 '-->' e2" := (step e1 e2).
(**[]*)

Ltac not_is_lambda :=
  match goal with
  | H: ~ is_lambda (λ _ ⇒ _) |- _ => exfalso
  end.
(**[]*)

Ltac inv_step_var :=
  match goal with
  | H: !_ -->  _ |- _ => inv H
  end.

Section NormalForm.
  Local Hint Extern 0 => inv_step_var : core.
  Local Hint Extern 1 => not_is_lambda : core.
  Local Hint Constructors is_lambda : core.

  Ltac contra_step :=
    match goal with
    | H: ?e -->  _, IH : (forall _, ~ ?e -->  _)
      |- _ => apply IH in H; contradiction
    end.

  Local Hint Extern 0 => contra_step : core.
  
  Lemma normal_form_step : forall e e',
      normal e -> ~ e -->  e'.
  Proof.
    intros ? e' Hnf; generalize dependent e';
      induction Hnf; intros ? ?; auto 2.
    - inv H; auto 1.
    - inv H0; auto 2.
  Qed.
End NormalForm.

Ltac normal_form_step_contra :=
  match goal with
  | Hnf: normal ?e, He: ?e -->  _
    |- _ => pose proof normal_form_step _ _ Hnf He;
          contradiction
  end.
(**[]*)

Section Determinism.
  Local Hint Constructors is_lambda : core.
  Local Hint Extern 1 => not_is_lambda : core.
  Local Hint Extern 0 => inv_step_var : core.
  Local Hint Extern 0 => normal_form_step_contra : core.
  (*Local Hint Resolve normal_form_step : core.*)

  Theorem step_deterministic : deterministic step.
  Proof. ind_det; f_equal; eauto 2. Qed.
End Determinism.

Section CanonicalForms.
  Lemma nth_error_nil : forall A n,
    @nth_error A [] n = None.
  Proof. intros ? []; reflexivity. Qed.

  Hint Rewrite nth_error_nil : core.
  Local Hint Extern 1 => not_is_lambda : core.
  Local Hint Constructors is_lambda : core.

  Lemma is_lambda_exm : forall e,
      is_lambda e \/ ~ is_lambda e.
  Proof.
    intros [];
      try (right; intros H; inv H; contradiction);
      intuition.
  Qed.
  
  Lemma canonical_forms_lambda : forall e τ τ',
    normal e -> [] ⊢ e ∈ τ → τ' -> exists e', e = λ τ ⇒ e'.
  Proof.
    intros ? t t' Hnf;
      generalize dependent t';
      generalize dependent t;
      induction Hnf; intros ? ? Ht; inv Ht;
      autorewrite with core in *; try discriminate; eauto 2.
    apply IHHnf1 in H2 as [? ?]; subst; auto 3.
  Qed.
End CanonicalForms.

Section Progress.
  Local Hint Constructors normal : core.
  Local Hint Constructors step : core.

  Lemma triv : forall e, normal e \/ exists e', e -->  e'.
  Proof.
    induction e; eauto.
    - destruct IHe as [? | [? ?]]; eauto.
    - destruct (is_lambda_exm e1) as [HL | ?];
        try inv HL; eauto.
      destruct IHe1 as [? | [? ?]];
        destruct IHe2 as [? | [? ?]]; eauto.
  Qed.

  (* TODO: progress is trivially true
     b/c there do not exist "stuck" terms. *)
  Theorem progress_stlc : forall e τ,
    [] ⊢ e ∈ τ -> normal e \/ exists e', e -->  e'.
  Proof. intros. apply triv. Qed.
  (*intros ? ? H.
    remember [] as g eqn:Hg.
    induction H; subst; eauto.
    - 
      repeat match goal with
             | IH: (normal ?e \/ exists _, ?e -->  _)
               |- _ => destruct IH as [? | [? ?]]
             | Ht: [] ⊢ ?e ∈ _ → _, Hnf: normal ?e
               |- _ => pose proof canonical_forms_lambda _ _ _ Hnf Ht as [? ?]
             end; eauto.
  Admitted.*)
End Progress.

Section Substituion.
  Local Hint Constructors check : core.
  Hint Rewrite shift_c_down_up : core.
  Hint Rewrite Nat.eqb_eq : core.
  Hint Rewrite Nat.eqb_neq : core.

  Lemma substition_lemma' : forall Γ τ τ' e e' c,
    (τ' :: Γ) ⊢ e ∈ τ -> Γ ⊢ e' ∈ τ' -> Γ ⊢ beta_reduce_c c e e' ∈ τ.
  Proof.
    intros g t t' e.
    generalize dependent t';
      generalize dependent t;
      generalize dependent g.
    unfold beta_reduce_c.
    induction e; intros ? ? ? ? ? He He'; inv He;
      simpl in *; eauto 4.
    - destruct (c =? n) eqn:Hcn; destruct n;
        simpl in *; autorewrite with core in *; subst;
          autorewrite with core in *.
      + inv H0; assumption.
      + admit.
      + admit.
      + admit.
    - constructor.
      eapply IHe; admit.
  Abort.
    
  Lemma substition_lemma : forall Γ τ τ' e e',
    (τ' :: Γ) ⊢ e ∈ τ -> Γ ⊢ e' ∈ τ' -> Γ ⊢ beta_reduce e e' ∈ τ.
  Proof.
    intros g t t' e.
    generalize dependent t';
      generalize dependent t;
      generalize dependent g.
    induction e; intros ? ? ? ? He He'; inv He;
      unfold beta_reduce, beta_reduce_c in *; simpl in *; eauto 4.
    - destruct n; simpl in *;
        autorewrite with core; auto 2.
      inv H0; assumption.
    - constructor.
  Abort.
End Substituion.

Section Preservation.
  Local Hint Constructors check : core.

  Theorem preservation : forall e e' Γ τ,
    e -->  e' -> Γ ⊢ e ∈ τ -> Γ ⊢ e' ∈ τ.
  Proof.
    intros ? ? g t He; generalize dependent t;
      generalize dependent g;
      induction He; intros ? ? Ht; inv Ht; eauto.
    - inv H1. (* TODO: sigh, of course *)
  Abort.
End Preservation.
