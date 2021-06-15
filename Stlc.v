Require Import Lambda.Util Coq.Program.Equality.
Require Import FunctionalExtensionality.

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

(** Shifts free variables above a cutoff [c] up by [i]. *)
Fixpoint shift (c i : nat) (e : expr) : expr :=
  match e with
  | !n =>  ! match lt_dec n c with
            | left _ => n
            | right _ => n + i
            end
  | λ τ ⇒ e => λ τ ⇒ (shift (S c) i e)
  | e1 ⋅ e2 => (shift c i e1) ⋅ (shift c i e2)
  end.
(**[]*)

Ltac destroy_arith :=
  intros; simpl; clean_compare;
  try (f_equal; auto 2; lia).

Section ShiftLemmas.
  Lemma shift0 : forall e k, shift k 0 e = e.
  Proof. induction e; destroy_arith. Qed.

  Lemma simpl_shift : forall e n p k i,
      i <= k + n -> k <= i ->
      shift i p (shift k n e) = shift k (p + n) e.
  Proof.
    induction e; destroy_arith.
    f_equal; apply IHe; lia.
  Qed.

  Local Hint Extern 0 => rewrite simpl_shift by lia; reflexivity : core.

  Lemma permute_shift : forall e n k p i,
      i <= k -> shift i p (shift k n e) = shift (p + k) n (shift i p e).
  Proof.
    induction e; destroy_arith.
    f_equal; rewrite IHe; f_equal; lia.
  Qed.

  Local Hint Extern 0 => rewrite permute_shift by lia; reflexivity : core.
End ShiftLemmas.

(** Substitution [e{esub/i}].
    [5 6 7 (esub/6) = 4 (shift 0 6 esub) 7]
 *)
Fixpoint sub (i : nat) (esub e : expr) : expr :=
  match e with
  | !n => match lt_eq_lt_dec i n with
         | inleft (left _) => ! (pred n)
         | inleft (right _) => shift 0 i esub
         | inright _ => !n
         end
  | λ τ ⇒ e => λ τ ⇒ (sub (S i) esub e)
  | e1 ⋅ e2 => (sub i esub e1) ⋅ (sub i esub e2)
  end.
(**[]*)

Section SubShiftLemmas.
  Local Hint Extern 0 => rewrite simpl_shift by lia; reflexivity : core.
  Local Hint Extern 0 => rewrite permute_shift by lia; reflexivity : core.

  Lemma simpl_sub : forall M N n p k,
    p <= n + k -> k <= p ->
    sub p N (shift k (S n) M) = shift k n M.
  Proof.
    induction M; destroy_arith.
    f_equal; apply IHM; lia.
  Qed.

  Local Hint Extern 0 => rewrite simpl_sub by lia; reflexivity : core.

  Lemma commute_shift_sub : forall M N n p k,
      k <= p ->
      shift k n (sub p N M) = sub (n + p) N (shift k n M).
  Proof.
    induction M; destroy_arith.
    f_equal; rewrite IHM; f_equal; lia.
  Qed.

  Local Hint Extern 0 => rewrite commute_shift_sub by lia; reflexivity : core.
  
  Lemma distr_shift_sub : forall M N n p k,
      shift (p + k) n (sub p N M) = sub p (shift k n N) (shift (S (p + k)) n M).
  Proof.
    induction M; destroy_arith.
    f_equal; rewrite <- IHM; f_equal; lia.
  Qed.

  Lemma distr_sub : forall M N P n p,
      sub (p + n) P (sub p N M) =
      sub p (sub n P N) (sub (S (p + n)) P M).
  Proof.
    induction M; destroy_arith.
    f_equal; rewrite <- IHM; f_equal; lia.
  Qed.
End SubShiftLemmas.

(** Beta-reduction [(λx.e1) e2 -> e1{e2/x}]. *)
Definition beta_reduce (e1 e2 : expr) : expr := sub 0 e2 e1.
(**[]*)

Lemma distr_shift_beta : forall M N n k,
    shift k n (beta_reduce M N) = beta_reduce (shift (S k) n M) (shift k n N).
Proof.
  intros; unfold beta_reduce.
  replace k with (0 + k) at 1 by lia.
  replace k with (0 + k) at 3 by lia.
  apply distr_shift_sub.
Qed.

Lemma distr_sub_beta : forall M N P n,
    sub n P (beta_reduce M N) =
    beta_reduce (sub (S n) P M) (sub n P N).
Proof.
  intros; unfold beta_reduce.
  replace n with (0 + n) at 1 by lia.
  replace n with (0 + n) at 3 by lia.
  apply distr_sub.
Qed.

(** Call-by-value Reduction. *)

Inductive is_lam : expr -> Prop :=
| is_lam_intro t e : is_lam (λ t ⇒ e).

Inductive stuck : expr -> Prop :=
| stuck_var n :
    stuck !n
| stuck_lam t e :
    stuck (λ t ⇒ e)
| stuck_app e1 e2 :
    ~ is_lam e1 ->
    stuck e1 -> stuck e2 -> stuck (e1 ⋅ e2).
(**[]*)

Reserved Notation "e1 '-->' e2" (at level 40).

Inductive step : expr -> expr -> Prop :=
| step_beta τ e1 e2 :
    stuck e2 ->
    (λ τ ⇒ e1) ⋅ e2 -->  beta_reduce e1 e2
| step_app_r e1 e2 e2' :
    stuck e1 ->
    e2 -->  e2' ->
    e1 ⋅ e2 -->  e1 ⋅ e2'
| step_app_l e1 e1' e2 :
    e1 -->  e1' ->
    e1 ⋅ e2 -->  e1' ⋅ e2
where "e1 '-->' e2" := (step e1 e2).
(**[]*)

Ltac inv_step_bad :=
  match goal with
  | H: !_ -->  _ |- _ => inv H
  | H: λ _ ⇒ _ -->  _ |- _ => inv H
  end.

Section NormalForm.
  Local Hint Constructors stuck : core.

  Ltac contra_step :=
    match goal with
    | H: ?e -->  _, IH : (forall _, ~ ?e -->  _)
      |- _ => apply IH in H; contradiction
    end.

  Local Hint Extern 0 => contra_step : core.
  Local Hint Extern 0 => inv_step_bad : core.
  Local Hint Constructors is_lam : core.

  Lemma step_nstuck : forall e e',
      e -->  e' -> ~ stuck e.
  Proof.
    intros ? ? Hs Hstk;
      induction Hs; inv Hstk; eauto.
  Qed.
  
  Lemma stuck_step : forall e e',
      stuck e -> ~ e -->  e'.
  Proof.
    intros ? e' Hv;
      generalize dependent e';
      induction Hv; intros ? He; inv He; eauto.
  Qed.
End NormalForm.

Ltac stuck_step_contra :=
  match goal with
  | Hnf: stuck ?e, He: ?e -->  _
    |- _ => pose proof stuck_step _ _ Hnf He;
          contradiction
  end.
(**[]*)

Section Determinism.
  Local Hint Constructors is_lam : core.
  Local Hint Constructors stuck : core.
  Local Hint Extern 0 => inv_step_bad : core.
  Local Hint Extern 0 => stuck_step_contra : core.

  Theorem step_deterministic : deterministic step.
  Proof. ind_det; f_equal; eauto 2. Qed.
End Determinism.

Section CanonicalForms.
  Lemma nth_error_nil : forall A n,
    @nth_error A [] n = None.
  Proof. intros ? []; reflexivity. Qed.

  Hint Rewrite nth_error_nil : core.
  Local Hint Constructors stuck : core.
  Local Hint Constructors is_lam : core.

  Lemma is_lam_exm : forall e, is_lam e \/ ~ is_lam e.
  Proof.
    intros []; intuition;
      right; intros H; inv H; contradiction.
  Qed.

  Local Hint Resolve is_lam_exm : core.

  Lemma stuck_exm : forall e,
      stuck e \/ ~ stuck e.
  Proof.
    intro e;
      induction e as
        [ n
        | t e ?
        | e1 [IHe1 | IHe1] e2 [IHe2 | IHe2]];
      intuition;
      try (right; intros H; inv H; contradiction).
    destruct (is_lam_exm e1); intuition.
    right; intros H'; inv H'; contradiction.
  Qed.
  
  Lemma canonical_forms_lambda : forall e τ τ',
    stuck e -> [] ⊢ e ∈ τ → τ' -> exists e', e = λ τ ⇒ e'.
  Proof.
    intros ? t t' Hnf;
      generalize dependent t';
      generalize dependent t;
      induction Hnf; intros ? ? Ht; inv Ht;
        autorewrite with core in *; try discriminate; eauto.
    apply IHHnf1 in H2 as [? ?]; subst.
    exfalso; eauto.
  Qed.
End CanonicalForms.

Section Progress.
  Local Hint Constructors stuck : core.
  Local Hint Constructors step : core.
  Hint Rewrite nth_error_nil : core.

  Lemma progress_thm : forall e t,
      [] ⊢ e ∈ t ->
      stuck e \/ exists e', e -->  e'.
  Proof.
    induction e; intros ? Ht; inv Ht;
      autorewrite with core in *;
      eauto 3; try discriminate. right.
    pose proof IHe1 _ H1 as [? | [? ?]]; eauto 3.
    pose proof IHe2 _ H3 as [? | [? ?]]; eauto 3.
    pose proof canonical_forms_lambda _ _ _ H H1 as [? ?]; subst; eauto 3.
  Qed.
End Progress.

Section Substituion.
  (** Lemmas inspired by:
      [http://www.lix.polytechnique.fr/~barras/CoqInCoq/Types.html] *)
  
  Local Hint Constructors check : core.
  Hint Rewrite distr_sub_beta : core.
  Hint Rewrite shift0 : core.
  Hint Rewrite Nat.eqb_eq : core.
  Hint Rewrite Nat.eqb_neq : core.
  Hint Rewrite nth_error_nil : core.

  Lemma nth_error_length : forall A n l (a : A),
      nth_error l n = Some a -> n < length l.
  Proof.
    induction n; destruct l; intros; simpl in *;
      try discriminate; try lia.
    apply IHn in H. lia.
  Qed.

  Lemma under_prefix : forall e τ Γ Γ',
      Γ ⊢ e ∈ τ -> (Γ ++ Γ') ⊢ e ∈ τ.
  Proof.
    induction e; intros τ g g' H;
      inv H; simpl in *;
        autorewrite with core in *;
        try discriminate; eauto.
    - constructor.
      rewrite nth_error_app1; eauto using nth_error_length.
    - constructor.
      replace (t :: g ++ g') with ((t :: g) ++ g') by reflexivity.
      eauto.
  Qed.

  Lemma under_empty : forall e τ Γ,
      [] ⊢ e ∈ τ -> Γ ⊢ e ∈ τ.
  Proof.
    intros. replace Γ with ([] ++ Γ) by reflexivity.
    auto using under_prefix.
  Qed.

  Lemma doi : forall a c,
      a < c -> exists b, a + b = c.
  Proof.
    intros ? ? H; induction H.
    - exists 1. lia.
    - destruct IHle as [b ?].
      exists (S b). lia.
  Qed.

  Lemma nth_error_app_plus : forall A (l l' : list A) n,
      nth_error (l ++ l') (length l + n) = nth_error l' n.
  Proof.
    induction l; intros; simpl in *; eauto.
  Qed.

  (** The following theorem statements
      are based of the work of the French.
      [http://www.lix.polytechnique.fr/~barras/CoqInCoq/Types.html] *)
  
  Lemma typ_weak_weak : forall e A Γ' Γ T,
      (Γ' ++ Γ) ⊢ e ∈ T ->
      (Γ' ++ A :: Γ) ⊢ shift (length Γ') 1 e ∈ T.
  Proof.
    induction e; intros ? ? ? ? He;
      inv He; simpl; eauto; constructor.
    - destroy_arith.
      + rewrite nth_error_app1 in * by lia.
        assumption.
      + rewrite nth_error_app2 in * by lia.
        replace (n + 1 - length Γ')
          with (S (n - length Γ')) by lia.
        simpl. assumption.
    - rewrite app_comm_cons.
      replace (S (length Γ'))
        with (length (t :: Γ')) by reflexivity.
      apply IHe. assumption.
  Qed.

  Lemma thinning : forall e Γ T A,
      Γ ⊢ e ∈ T ->
      (A :: Γ) ⊢ shift 0 1 e ∈ T.
  Proof.
    intros.
    replace (A :: Γ)
      with ([] ++ A :: Γ) by reflexivity.
    replace 0 with (length (@nil type)) at 1 by reflexivity.
    apply typ_weak_weak. assumption.
  Qed.

  Lemma thinning_n : forall Γ' Γ e T,
      Γ ⊢ e ∈ T ->
      (Γ' ++ Γ) ⊢ shift 0 (length Γ') e ∈ T.
  Proof.
    induction Γ' as [| h t IHt]; intros; simpl.
    - rewrite shift0. assumption.
    - pose proof thinning as THIN.
      pose proof simpl_shift as SS.
      replace (S (length t))
        with (1 + length t) by reflexivity.
      rewrite <- simpl_shift with (i := 0) by lia.
      apply THIN. apply IHt. assumption.
  Qed.
  
  Lemma typ_sub_weak : forall e e' Γ Γ' τ τ',
      (Γ ++ τ' :: Γ') ⊢ e ∈ τ ->
      Γ' ⊢ e' ∈ τ' ->
      (Γ ++ Γ') ⊢ sub (length Γ) e' e ∈ τ.
  Proof.
    induction e; intros ? ? ? ? ? He He';
      inv He; simpl in *; eauto.
    - destroy_arith.
      + constructor.
        pose proof doi _ _ l as [b Hb]; subst.
        rewrite <- Nat.add_pred_r by lia.
        rewrite nth_error_app_plus in H0.
        rewrite nth_error_app_plus.
        destruct b; try lia; auto.
      + replace n with (length Γ + 0) in H0 by lia.
        rewrite nth_error_app_plus in H0.
        simpl in *. inv H0. clear Heqs.
        apply thinning_n. assumption.
      + constructor.
        rewrite nth_error_app1 in * by lia; auto.
    - constructor.
      replace (t :: Γ ++ Γ')
        with ((t :: Γ) ++ Γ') by reflexivity.
      replace (S (length Γ))
        with (length (t :: Γ)) by reflexivity.
      apply IHe with τ'; simpl; auto.
  Qed.

  Lemma substitution_lemma : forall Γ τ τ' e e',
    (τ' :: Γ) ⊢ e ∈ τ -> Γ ⊢ e' ∈ τ' -> Γ ⊢ beta_reduce e e' ∈ τ.
  Proof.
    intros ? ? ? ? ? He He'; unfold beta_reduce.
    replace Γ with ([] ++ Γ) by reflexivity.
    eapply typ_sub_weak; eauto.
  Qed.
End Substituion.

Section Preservation.
  Local Hint Constructors check : core.

  Theorem preservation : forall e e' Γ τ,
    e -->  e' -> Γ ⊢ e ∈ τ -> Γ ⊢ e' ∈ τ.
  Proof.
    intros ? ? g t He; generalize dependent t;
      generalize dependent g;
      induction He; intros ? ? Ht; inv Ht; eauto.
    - inv H2. eapply substitution_lemma; eauto.
  Qed.
End Preservation.

Notation "e1 '-->*' e2" := (refl_trans_closure step e1 e2) (at level 40).

Section MultiStep.
  Local Hint Constructors step : core.
  Local Hint Constructors refl_trans_closure : core.
  
  Lemma multi_step_app_l : forall e1 e1' e2,
    e1 -->* e1' -> e1 ⋅ e2 -->*  e1' ⋅ e2.
  Proof.
    intros ? ? e2 Hms;
      generalize dependent e2;
      induction Hms; eauto.
  Qed.

  Lemma multi_step_app_r : forall e1 e2 e2',
      stuck e1 -> e2 -->* e2' -> e1 ⋅ e2 -->*  e1 ⋅ e2'.
  Proof.
    intros e1 ? ? ? Hms;
      generalize dependent e1;
      induction Hms; eauto.
  Qed.
End MultiStep.

(** Does a program halt? *)
Definition halts (e : expr) : Prop :=
  exists e', e -->* e' /\ forall e'', ~ e' -->  e''.
(**[]*)

Section NH.
  Local Hint Constructors refl_trans_closure : core.
  Local Hint Resolve stuck_step : core.
  
  Lemma stuck_halts : forall e, stuck e -> halts e.
  Proof. intros ? ?; unfold halts; eauto 4. Qed.
End NH.

Inductive closed : nat -> expr -> Prop :=
| closed_var k n :
    n < k ->
    closed k !n
| closed_lam k t e :
    closed (S k) e ->
    closed k (λ t ⇒ e)
| closed_app k e1 e2 :
    closed k e1 ->
    closed k e2 ->
    closed k (e1 ⋅ e2).
(**[]*)

(** This property is necessary
    to prove some properties of [R]. *)
Lemma type_closed : forall Γ e t,
    Γ ⊢ e ∈ t -> closed (length Γ) e.
Proof.
  intros ? ? ? H; induction H;
    constructor; simpl in *; auto.
  eapply nth_error_length; eauto.
Qed.

Lemma empty_context_closed : forall e t,
    [] ⊢ e ∈ t -> closed 0 e.
Proof.
  intros.
  replace 0 with (@length type []) by reflexivity.
  eapply type_closed; eauto 1.
Qed.

Section FrenchLemmas.
  Local Hint Constructors stuck : core.
  Local Hint Constructors is_lam : core.

  Lemma is_lam_shift : forall e k i,
      is_lam (shift k i e) -> is_lam e.
  Proof.
    intros [] ? ? H; inv H; auto.
  Qed.

  Local Hint Resolve is_lam_shift : core.

  Lemma stuck_shift : forall e k i,
      stuck e -> stuck (shift k i e).
  Proof.
    intros ? k i Hstk;
      generalize dependent i;
      generalize dependent k;
      induction Hstk; simpl;
        destroy_arith; eauto.
  Qed.

  Local Hint Resolve stuck_shift : core.
  
  Lemma stuck_sub : forall e,
      stuck e -> forall i esub, stuck esub -> stuck (sub i esub e).
  Proof.
    intros ? Hv; induction Hv; intros; simpl; auto.
    - destroy_arith; auto 1.
    - constructor; eauto.
  Abort.
  
  Local Hint Constructors step : core.
  (* Local Hint Resolve stuck_sub : core. *)
  
  Lemma sub_step : forall e e' es i,
      stuck es ->
      e -->  e' ->
      sub i es e -->  sub i es e'.
  Proof.
    intros ? ? ? es i H.
      generalize dependent es;
      generalize dependent i.
      induction H; intros; simpl; eauto.
      rewrite distr_sub_beta; auto.
  Abort.
  
  Lemma beta_reduce_step : forall e1 e1' e2,
      stuck e2 ->
      e1 -->  e1' ->
      beta_reduce e1 e2 -->  beta_reduce e1' e2.
  Proof.
    unfold beta_reduce; intros.
    Fail apply sub_step; assumption.
  Abort.

  Hint Constructors closed : core.
  
  Lemma closed_closed : forall e m n,
      m < n -> closed m e -> closed n e.
  Proof.
    induction e; intros ? ? ? Hm; inv Hm; eauto.
    - constructor. lia.
    - constructor.
      apply IHe with (S m); auto 1; lia.
  Qed.

  Lemma shift_closed : forall k e,
      closed k e -> forall c i, closed (k + i) (shift c i e).
  Proof.
    intros k e Hc; induction Hc;
      intros c i; simpl; eauto.
    constructor. destroy_arith.
  Qed.
End FrenchLemmas.

Section StepEXM.
  Local Hint Constructors step : core.
  Local Hint Constructors stuck : core.
  Local Hint Constructors is_lam : core.

  Lemma nstuck_step_exists : forall e,
      ~ stuck e -> exists e', e -->  e'.
  Proof.
    intro e;
      induction e as
        [ n
        | t e IHe
        | e1 IHe1 e2 IHe2 ]; intros Hstk;
        try (exfalso; auto; contradiction).
    destruct (stuck_exm e1) as [He1 | He1].
    - destruct (stuck_exm e2) as [He2 | He2].
      + destruct (is_lam_exm e1) as [Hl1 | Hl1].
        * inv Hl1; eauto.
        * exfalso; auto.
      + apply IHe2 in He2 as [? ?]; eauto.
    - apply IHe1 in He1 as [? ?]; eauto.
  Qed.

  Local Hint Resolve nstuck_step_exists : core.

  Lemma nstep_stuck : forall e,
      (forall e', ~ e -->  e') -> stuck e.
  Proof.
    intros e H.
    destruct (stuck_exm e) as [Hstk | Hstk]; auto.
    apply nstuck_step_exists in Hstk as [? Hstep].
    apply H in Hstep. contradiction.
  Qed.
        
  Lemma step_exm : forall e,
      (exists e', e -->  e') \/ forall e', ~ e -->  e'.
  Proof.
    intro e;
      pose proof stuck_exm e as [H | H];
      intuition. right; intros e'.
    eapply stuck_step in H; eauto.
  Qed.
End StepEXM.

Section Forall2Context.
  Context {U V : Type}.

  Section Defs.
    Variable R : list U -> V -> U -> Prop.
    Variable ctx : list U.

    Inductive AllCtx2 : list V -> list U -> Prop :=
    | AllCtx2_nil :
        AllCtx2 [] []
    | AllCtx2_cons u us v vs :
        R (us ++ ctx) v u ->
        AllCtx2 vs us ->
        AllCtx2 (v :: vs) (u :: us).
    (**[]*)

    Lemma AllCtx2_length : forall vs us,
        AllCtx2 vs us -> length vs = length us.
    Proof.
      intros vs us H; induction H; simpl; auto.
    Qed.
  End Defs.

  Local Hint Constructors AllCtx2 : core.

  Lemma AllCtx2_sanity : forall (R : V -> U -> Prop) ctx vs us,
      AllCtx2 (fun _ => R) ctx vs us <-> Forall2 R vs us.
  Proof.
    intros ? ? ? ?; split; intros H;
      induction H; auto.
  Qed.

  Lemma AllCtx2_impl : forall (R W : list U -> V -> U -> Prop) ctx vs us,
      (forall ctx v u, R ctx v u -> W ctx v u) ->
      AllCtx2 R ctx vs us -> AllCtx2 W ctx vs us.
  Proof.
    intros R W ctx vs us HRW HR; induction HR; auto.
  Qed.
End Forall2Context.

Lemma Forall2_length : forall A B (R : A -> B -> Prop) a b,
    Forall2 R a b -> length a = length b.
Proof.
  intros A B R a b H; induction H; simpl; auto.
Qed.

Lemma Forall2_impl : forall A B (P Q : A -> B -> Prop) a b,
    (forall a b, P a b -> Q a b) ->
    Forall2 P a b -> Forall2 Q a b.
Proof.
  intros A B P Q a b H HP;
    induction HP; auto.
Qed.

Lemma rev_nil : forall A (l : list A), rev l = [] -> l = [].
Proof.
  intros A l;
    induction l as [| h t IHt] using rev_ind;
    intros H; trivial.
  rewrite rev_unit in H. discriminate.
Qed.

Module JapaneseNorm.
  Lemma sub_closed : forall k e,
    closed k e -> forall n v, sub (k + n) v e = e.
  Proof.
    intros k e HC; induction HC;
      intros; simpl; destroy_arith;
        f_equal; eauto.
  Qed.

  Inductive all_closed (k : nat) : list expr -> Prop :=
  | all_closed_nil :
      all_closed k []
  | all_closed_cons v vs :
      closed (length vs + k) v ->
      all_closed k vs ->
      all_closed k (v :: vs).
  (**[]*)
    
  Section FoldSub.
    Lemma sub_fold_sub : forall k e v vs,
      sub k v (fold_left (fun e v => sub k v e) vs e) =
      fold_left (fun e v => sub k v e) (vs ++ [v]) e.
    Proof.
      intros k e v vs.
      rewrite fold_left_app; simpl.
      reflexivity.
    Qed.

    Lemma distr_fold_sub : forall vs M N n p,
        fold_left (fun e v => sub (p + n) v e) vs (sub p N M) =
        sub p (fold_left (fun e v => sub n v e) vs N)
            (fold_left (fun e v => sub (S (p + n)) v e) vs M).
    Proof.
      intro vs; induction vs as [| v vs IHvs];
        intros M N n p; simpl; trivial.
      rewrite <- IHvs. rewrite distr_sub. reflexivity.
    Qed.

    Lemma distr_fold_br : forall vs M N n,
        fold_left (fun e v => sub n v e) vs (beta_reduce M N) =
        beta_reduce
          (fold_left (fun e v => sub (S n) v e) vs M)
          (fold_left (fun e v => sub n v e) vs N).
    Proof.
      intros vs M N n; unfold beta_reduce.
      replace n with (0 + n) by reflexivity.
      rewrite distr_fold_sub. reflexivity.
    Qed.
    
    Lemma fold_sub_closed_l : forall vs e k n,
        closed k e ->
        fold_left (fun e v => sub (k + n) v e) vs e = e.
    Proof.
      intro vs; induction vs as [| v vs IHvs];
        intros; simpl; trivial.
      rewrite sub_closed by assumption.
      firstorder.
    Qed.

    Local Hint Resolve sub_closed : core.

    Lemma fold_sub_closed_r : forall vs e k n,
        closed k e ->
        fold_right (sub (k + n)) e vs = e.
    Proof.
      intro vs; induction vs as [| v vs IHvs];
        intros; simpl; trivial.
      rewrite IHvs by assumption; auto.
    Qed.

    Local Hint Resolve typ_sub_weak : core.
    
    Lemma fold_typ_sub_weak_l : forall vs ts g,
        AllCtx2 check g vs ts ->
        forall G e t,
          (G ++ ts ++ g) ⊢ e ∈ t ->
          (G ++ g) ⊢ fold_left (fun e v => sub (length G) v e) vs e ∈ t.
    Proof.
      intros vs ts g Hctx;
        induction Hctx; intros G e t Het;
          simpl in *; eauto.
    Qed.

    Lemma fold_typ_sub_weak_r : forall vs ts g,
        AllCtx2 check g vs ts ->
        forall G e t,
          (G ++ rev ts ++ g) ⊢ e ∈ t ->
          (G ++ g) ⊢ fold_right (sub (length G)) e vs ∈ t.
    Proof.
      intros vs ts g Hctx;
        induction Hctx; intros G e t Het;
          simpl in *; trivial.
      apply typ_sub_weak with u.
    Abort.

    Lemma fold_sub_lambda_l : forall vs e t n,
        fold_left (fun e v => sub n v e) vs (λ t ⇒ e) =
        λ t ⇒ (fold_left (fun e v => sub (S n) v e) vs e).
    Proof.
      intro vs; induction vs as [| v vs IHvs];
        intros e t n; simpl; trivial.
    Qed.

    Lemma fold_sub_app_l : forall vs e1 e2 n,
        fold_left (fun e v => sub n v e) vs (e1 ⋅ e2) =
        (fold_left (fun e v => sub n v e) vs e1) ⋅ (fold_left (fun e v => sub n v e) vs e2).
    Proof.
      intro vs; induction vs as [| v vs IHvs];
        intros e t n; simpl; trivial.
    Qed.        
  End FoldSub.

  Fixpoint msub (n : nat) (vs : list expr) (e : expr) : expr :=
    match vs with
    | [] => e
    | v :: vs => msub n vs (sub (n + length vs) v e)
    end.
  (**[]*)

  Section MSub.
    Lemma msub_closed : forall vs e k,
      closed k e ->
      msub k vs e = e.
    Proof.
      intro vs;
        induction vs as [| v vs IHvs];
        intros e k Hek; simpl; trivial.
      rewrite sub_closed by assumption; auto.
    Qed.

    Local Hint Resolve sub_closed : core.

    Lemma typ_msub_weak : forall vs ts g,
        Forall2 (check g) vs ts ->
        forall G e t,
          (G ++ rev ts ++ g) ⊢ e ∈ t ->
          (G ++ g) ⊢ msub (length G) vs e ∈ t.
    Proof.
      intro vs;
        induction vs as [| v vs IHvs];
        intros [| t ts] g HF2 G e τ Het;
        inv HF2; simpl in *; trivial.
      apply IHvs with (ts := ts); auto.
      assert (Hlen : length vs = length ts) by eauto using Forall2_length.
      rewrite Hlen. rewrite <- (rev_length ts).
      rewrite <- app_length. rewrite app_assoc.
      eapply typ_sub_weak; eauto.
      rewrite <- app_assoc in Het; simpl in Het.
      rewrite app_assoc in Het. assumption.
    Qed.
    
    Lemma msub_lambda : forall vs e t n,
        msub n vs (λ t ⇒ e) = λ t ⇒ (msub (S n) vs e).
    Proof.
      intro vs; induction vs as [| v vs IHvs];
        intros e t n; simpl; trivial.
    Qed.

    Lemma msub_app : forall vs e1 e2 n,
        msub n vs (e1 ⋅ e2) = (msub n vs e1) ⋅ (msub n vs e2).
    Proof.
      intro vs; induction vs as [| v vs IHvs];
        intros e1 e2 n; simpl; trivial.
    Qed.

    Lemma msub_single : forall n v e,
        msub n [v] e = sub n v e.
    Proof.
      intros n v e; simpl.
      rewrite Nat.add_comm. reflexivity.
    Qed.

    Lemma msub_append : forall vs1 vs2 e n,
        msub n (vs1 ++ vs2) e = msub n vs2 (msub (n + length vs2) vs1 e).
    Proof.
      intro vs1; induction vs1 as [| v1 vs1 IHvs1];
        intros vs2 e n; simpl; trivial.
      rewrite IHvs1. rewrite app_length.
      rewrite (Nat.add_comm (length vs1) (length vs2)).
      rewrite Nat.add_assoc. reflexivity.
    Qed.

    Lemma msub_sub : forall vs n e v,
        sub n v (msub (S n) vs e) = msub n (vs ++ [v]) e.
    Proof.
      intros vs n e v.
      rewrite <- msub_single.
      rewrite msub_append; simpl.
      repeat f_equal; lia.
    Qed.

    Lemma sub_msub : forall vs n k e v,
        sub n v (msub (n + k) vs e) = msub n (vs ++ [v]) e.
    Proof.
      intro vs; induction vs as [| v vs IHvs];
        intros n k e e'; simpl.
      - f_equal; lia.
      - rewrite IHvs.
    Abort.

    Lemma msub_var : forall vs v k n,
        Forall (closed k) vs ->
        nth_error vs n = Some v ->
        msub k vs !n = v.
    Proof.
      intro vs; induction vs as [| v vs IHvs];
        intros e k n Hvs Hnth; inv Hvs; simpl.
      - rewrite nth_error_nil in Hnth; discriminate.
      - destruct n as [| n]; simpl in *; destroy_arith.
        + inv Hnth. rewrite e0.
          rewrite shift0. apply msub_closed; auto.
        + inv Hnth. rewrite IHvs with (v := e); auto.
          admit.
        + rewrite e0. admit.
        + rewrite IHvs with (v := e); auto.
    Abort.
  End MSub.
  
  (** Strongly normalizing. *)
  Inductive SN (e : expr) : Prop :=
  | SN_intro :
      (forall e', e -->  e' -> SN e') -> SN e.
  (**[]*)

  Section SNProp.
    Local Hint Constructors refl_trans_closure : core.
    
    Lemma SN_halts : forall e, SN e -> halts e.
    Proof.
      unfold halts; intros e H; induction H.
      destruct (step_exm e) as [[e' He] | He]; eauto 3.
      apply H0 in He as He'.
      destruct He' as [e'' [He' He'']]; eauto 4.
    Qed.

    Local Hint Constructors step : core.

    Lemma step_SN : forall e e',
        e -->  e' -> SN e -> SN e'.
    Proof.
      intros ? ? ? HSN; inv HSN; eauto.
    Qed.

    Lemma unstep_SN : forall e e',
        e -->  e' -> SN e' -> SN e.
    Proof.
      intros e e' Hs HSN; constructor.
      intros e'' Hs';
        pose proof step_deterministic _ _ _ Hs Hs';
        subst; auto.
    Qed.

    Local Hint Constructors is_lam : core.
    Local Hint Constructors stuck : core.
    Local Hint Resolve step_nstuck : core.

    Lemma stuck_SN : forall v, stuck v -> SN v.
    Proof.
      intros ? Hv; induction Hv;
        constructor; intros ? Hstep; inv Hstep;
          try (exfalso; eauto; contradiction).
      - apply step_nstuck in H4. contradiction.
      - apply step_nstuck in H3. contradiction.
    Qed.

    Local Hint Resolve stuck_SN : core.

    Lemma SN_var : forall n, SN !n.
    Proof. intuition. Qed.

    Lemma SN_lambda : forall t e, SN (λ t ⇒ e).
    Proof. intuition. Qed.

    Local Hint Resolve nstep_stuck : core.
    
    Lemma SN_exists_stuck : forall e,
        SN e -> exists v, stuck v /\ e -->* v.
    Proof.
      intros e Hsn.
      apply SN_halts in Hsn as [e' [Hms He']]; eauto.
    Qed.
  End SNProp.

  (** The logical relation. *)
  Fixpoint R (g : list type) (e : expr) (t : type) : Prop :=
    SN e /\ g ⊢ e ∈ t /\
    match t with
    | ⊥ => True
    | t → t' => forall e2, R g e2 t -> R g (e ⋅ e2) t'
    end.
  (**[]*)

  Section RProp.
    Local Hint Resolve step_SN : core.
    Local Hint Constructors step : core.

    Lemma R_types : forall g e t, R g e t -> g ⊢ e ∈ t.
    Proof.
      intros ? ? []; simpl; firstorder.
    Qed.

    Lemma R_SN : forall g e t, R g e t -> SN e.
    Proof.
      intros ? ? []; simpl; firstorder.
    Qed.

    Local Hint Resolve preservation : core.
    
    Lemma step_R : forall t g e e',
      e -->  e' -> R g e t -> R g e' t.
    Proof.
      intro t; induction t; intros;
        simpl in *; intuition; eauto.
    Qed.
    
    Local Hint Resolve unstep_SN : core.
    Local Hint Resolve R_types : core.
    Local Hint Resolve R_SN : core.
    Local Hint Constructors SN : core.
    Local Hint Constructors check : core.

    Lemma unstep_R : forall t g e e',
        e -->  e' -> g ⊢ e ∈ t -> R g e' t -> R g e t.
    Proof.
      intro t; induction t; intros;
        simpl in *; intuition; eauto 6.
    Qed.
    
    Local Hint Resolve step_R : core.
    Local Hint Resolve unstep_R : core.
    Local Hint Constructors stuck : core.
    Local Hint Resolve stuck_SN : core.

    Lemma multi_step_R : forall e e' g t,
        e -->* e' -> R g e t -> R g e' t.
    Proof.
      intros ? ? ? ? Hms;
        induction Hms; simpl; eauto.
    Qed.

    Lemma multi_unstep_R : forall e e' g t,
        e -->* e' -> g ⊢ e ∈ t -> R g e' t -> R g e t.
    Proof.
      intros ? ? ? ? Hms;
        induction Hms; eauto.
    Qed.

    Local Hint Resolve multi_step_R : core.
    Local Hint Resolve multi_unstep_R : core.
    Local Hint Resolve trans_closure_r : core.
    Local Hint Resolve multi_step_app_r : core.

    Lemma abs_R_sub : forall g e t t',
        g ⊢ λ t ⇒ e ∈ t → t' ->
        (forall G v, R (G ++ g) v t -> R (G ++ g) (sub (length G) v e) t') ->
        R g (λ t ⇒ e) (t → t').
    Proof.
      intros g e t t' Het HR; simpl; intuition.
      assert (Hsn : SN e2) by eauto.
      apply SN_exists_stuck in Hsn as [v [Hvstk Hvms]].
      apply multi_unstep_R with (e' := beta_reduce e v); eauto.
      unfold beta_reduce.
      replace 0 with (@length type []) by reflexivity.
      pose proof HR []; simpl in *; eauto.
    Qed.

    Lemma abs_R : forall g e t t',
        g ⊢ λ t ⇒ e ∈ t → t' ->
        (forall v, stuck v -> R g v t -> R g (beta_reduce e v) t') ->
        R g (λ t ⇒ e) (t → t').
    Proof.
      intros g e t t' Het HR; simpl; intuition.
      assert (Hsn : SN e2) by eauto.
      apply SN_exists_stuck in Hsn as [v [Hvstk Hvms]].
      apply multi_unstep_R with (e' := beta_reduce e v); eauto.
    Qed.

    Local Hint Resolve SN_lambda : core.
    Local Hint Resolve SN_var : core.
    Local Hint Resolve typ_msub_weak : core.
    Local Hint Resolve fold_typ_sub_weak_l : core.
    Local Hint Resolve AllCtx2_impl : core.

    (*Definition br_first*)

    Lemma R_fold_br : forall g ts e t vs,
        AllCtx2 R g vs ts ->
        (ts ++ g) ⊢ e ∈ t ->
        R g (fold_left beta_reduce vs e) t.
    Proof.
      intros g ts e t vs ? Het.
      remember (ts ++ g) as Γ eqn:Heqg.
      generalize dependent g; generalize dependent ts; generalize dependent vs.
      induction Het; intros vs ts g Hctx Heqg; subst.
      - generalize dependent n;
          generalize dependent τ.
        induction Hctx; intros t n Hnth; simpl in *.
        + generalize dependent n;
            generalize dependent t.
          induction g as [| tg g IHg];
            intros t n Hnth; simpl.
          * rewrite nth_error_nil in Hnth.
            discriminate.
          * destruct n as [| n]; simpl in *.
            ** inv Hnth. generalize dependent g.
               induction t as [| t1 IHt1 t2 IHt2];
                 intros g IH; simpl; intuition. admit.
            ** admit.
        + admit.
      - unfold beta_reduce.
        rewrite fold_sub_lambda_l. apply abs_R.
        + constructor.
          replace (τ :: g) with ([τ] ++ g) by reflexivity.
          replace 1 with (length [τ]) by reflexivity. eauto.
        + intros v Hstk HR. admit.
      - assert (doi: ts ++ g = ts ++ g) by reflexivity.
        pose proof IHHet1 _ _ _ Hctx doi as IH1.
        pose proof IHHet2 _ _ _ Hctx doi as IH2.
        unfold beta_reduce in *.
        rewrite fold_sub_app_l. simpl in IH1.
        intuition.
    Admitted.

    Lemma R_fold_sub : forall G ts g e t vs,
        AllCtx2 R g vs ts ->
        (G ++ ts ++ g) ⊢ e ∈ t ->
        R (G ++ g) (fold_left (fun e v => sub (length G) v e) vs e) t.
    Proof.
      intros G ts g e t vs ? Het. generalize dependent vs.
      remember (G ++ ts ++ g) as Γ eqn:HeqG.
      generalize dependent g; generalize dependent ts; generalize dependent G.
      induction Het; intros G ts g Heqg vs Hac; subst.
      - admit.
      - simpl; intuition.
        + rewrite fold_sub_lambda_l. eauto.
        + rewrite fold_sub_lambda_l.
          constructor.
          replace (S (length G))
            with (length (τ :: G)) by reflexivity.
          rewrite app_comm_cons. eauto.
        + assert (Hsn : SN e2) by eauto.
          apply SN_exists_stuck in Hsn as [v [Hv He2]].
          apply multi_unstep_R
            with (e' :=
                    beta_reduce
                      (fold_left
                         (fun e v => sub (S (length G)) v e) vs e) v).
          * rewrite fold_sub_lambda_l; eauto.
          * constructor 3 with τ; eauto.
          * assert (doi: τ :: G ++ ts ++ g = τ :: G ++ ts ++ g) by trivial.
            pose proof IHHet (τ :: G) ts g doi vs Hac as IH; clear IHHet.
            simpl in *.
            Check substitution_lemma.
            (** Maybe "substitution_lemma" for R? *) admit.
      - rewrite fold_sub_app_l.
        assert (doi: G ++ ts ++ g = G ++ ts ++ g) by trivial.
        pose proof IHHet1 G ts g doi vs Hac.
        pose proof IHHet2 G ts g doi vs Hac.
        simpl in *; intuition.
    Admitted.

    Local Hint Resolve Forall2_impl : core.
    
    Lemma R_msub : forall G ts g e t vs,
        Forall2 (R g) vs ts ->
        (G ++ rev ts ++ g) ⊢ e ∈ t ->
        R (G ++ g) (msub (length G) vs e) t.
    Proof.
      intros G ts g e t vs ? Het.
      generalize dependent vs.
      remember (G ++ rev ts ++ g) as ctx eqn:Hctxeq.
      generalize dependent g;
        generalize dependent ts;
        generalize dependent G.
      induction Het; intros G ts g Heqctx vs HF2; subst.
      - admit.
      - rewrite msub_lambda.
        replace (S (length G))
          with (length (τ :: G)) by reflexivity.
        unfold R; fold R; intuition.
        + constructor.
          rewrite app_comm_cons; eauto.
        + assert (Hsn: SN e2) by eauto.
          apply SN_exists_stuck in Hsn as [v [Hstk Hms]].
          apply multi_unstep_R with
              (e' := beta_reduce (msub (length (τ :: G)) vs e) v); eauto.
          * constructor 3 with τ; eauto.
            constructor.
            rewrite app_comm_cons; eauto.
          * unfold beta_reduce. admit.
      - rewrite msub_app.
        assert (Hdumb : G ++ rev ts ++ g = G ++ rev ts ++ g)
          by trivial.
        pose proof IHHet1 _ _ _ Hdumb _ HF2
          as [HSN [Hchk HR]]; clear IHHet1.
        pose proof IHHet2 _ _ _ Hdumb _ HF2 as IH2; clear IHHet2.
        eauto.
    Admitted.

    Lemma reduce_lemma : forall e t g ts vs,
        Forall2 (R g) vs ts ->
        (ts ++ g) ⊢ e ∈ t ->
        R g (fold_left beta_reduce vs e) t.
    Proof.
      intro e;
        induction e as [n | t e IHe | e1 IHe1 e2 IHe2];
        intros τ g ts vs HF2 Het; inv Het; simpl.
    Abort.
  End RProp.
End JapaneseNorm.
