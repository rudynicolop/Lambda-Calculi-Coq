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

Inductive value : expr -> Prop :=
| value_lam t e : value (λ t ⇒ e).

Reserved Notation "e1 '-->' e2" (at level 40).

Inductive step : expr -> expr -> Prop :=
| step_beta τ e1 e2 :
    value e2 ->
    (λ τ ⇒ e1) ⋅ e2 -->  beta_reduce e1 e2
| step_app_r e1 e2 e2' :
    value e1 ->
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
  Local Hint Constructors value : core.

  Ltac contra_step :=
    match goal with
    | H: ?e -->  _, IH : (forall _, ~ ?e -->  _)
      |- _ => apply IH in H; contradiction
    end.

  Local Hint Extern 0 => contra_step : core.
  
  Lemma value_step : forall e e',
      value e -> ~ e -->  e'.
  Proof. intros ? ? Hv He; inv Hv; inv He. Qed.
End NormalForm.

Ltac value_step_contra :=
  match goal with
  | Hnf: value ?e, He: ?e -->  _
    |- _ => pose proof value_step _ _ Hnf He;
          contradiction
  end.
(**[]*)

Section Determinism.
  Local Hint Constructors value : core.
  Local Hint Extern 0 => inv_step_bad : core.
  Local Hint Extern 0 => value_step_contra : core.

  Theorem step_deterministic : deterministic step.
  Proof. ind_det; f_equal; eauto 2. Qed.
End Determinism.

Section CanonicalForms.
  Lemma nth_error_nil : forall A n,
    @nth_error A [] n = None.
  Proof. intros ? []; reflexivity. Qed.

  Hint Rewrite nth_error_nil : core.
  Local Hint Constructors value : core.

  Lemma value_exm : forall e,
      value e \/ ~ value e.
  Proof.
    intros [];
      try (right; intros H; inv H; contradiction);
      intuition.
  Qed.
  
  Lemma canonical_forms_lambda : forall e τ τ',
    value e -> [] ⊢ e ∈ τ → τ' -> exists e', e = λ τ ⇒ e'.
  Proof.
    intros ? t t' Hnf;
      generalize dependent t';
      generalize dependent t;
      induction Hnf; intros ? ? Ht; inv Ht;
      autorewrite with core in *; try discriminate; eauto 2.
  Qed.
End CanonicalForms.

Section Progress.
  Local Hint Constructors value : core.
  Local Hint Constructors step : core.
  Hint Rewrite nth_error_nil : core.

  Lemma progress_thm : forall e t,
      [] ⊢ e ∈ t ->
      value e \/ exists e', e -->  e'.
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

  Lemma substition_lemma : forall Γ τ τ' e e',
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
    - inv H2. eapply substition_lemma; eauto.
  Qed.
End Preservation.

Notation "e1 '-->*' e2" := (refl_trans_closure step e1 e2) (at level 40).

(** Does a program halt? *)
Definition halts (e : expr) : Prop :=
  exists e', e -->* e' /\ forall e'', ~ e' -->  e''.
(**[]*)

Section NH.
  Local Hint Constructors refl_trans_closure : core.
  Local Hint Resolve value_step : core.
  
  Lemma value_halts : forall e, value e -> halts e.
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
  Local Hint Constructors value : core.

  Lemma value_sub : forall e,
      value e -> forall i esub, value (sub i esub e).
  Proof.
    intros ? Hv; inv Hv; intros; simpl; auto 1.
  Qed.
  
  Local Hint Constructors step : core.
  Local Hint Resolve value_sub : core.
  
  Lemma sub_step : forall e e' es i,
      e -->  e' ->
      sub i es e -->  sub i es e'.
  Proof.
    intros ? ? es i H.
      generalize dependent es;
      generalize dependent i.
      induction H; intros; simpl; eauto.
      rewrite distr_sub_beta; auto 3.
  Qed.
  
  Lemma beta_reduce_step : forall e1 e1' e2,
      e1 -->  e1' ->
      beta_reduce e1 e2 -->  beta_reduce e1' e2.
  Proof.
    unfold beta_reduce; intros.
    apply sub_step; assumption.
  Qed.

  Hint Constructors closed : core.
  
  Lemma closed_closed : forall e m n,
      m < n -> closed m e -> closed n e.
  Proof.
    induction e; intros ? ? ? Hm; inv Hm; eauto.
    - constructor. lia.
    - constructor.
      apply IHe with (S m); auto 1; lia.
  Qed.
End FrenchLemmas.

(** The Logical Relation. *)
Fail Inductive R (Γ : list type) : type -> expr -> Prop :=
| R_base e :
    halts e ->
    Γ ⊢ e ∈ ⊥ ->
    R Γ ⊥ e
| R_lambda τ τ' e :
    halts e ->
    (forall e2, R Γ τ e2 -> R Γ τ' (e ⋅ e2)) ->
    R Γ (τ → τ') e.
(**[]*)

(** Oh, wait, oops, my bad. Here it is: *)
Fixpoint R (Γ : list type) (e : expr) (τ : type) : Prop :=
  halts e /\ Γ ⊢ e ∈ τ /\
  match τ with
  | ⊥ => True
  | τ → τ' => forall e2, R Γ e2 τ -> R Γ (e ⋅ e2) τ'
  end.
(**[]*)

Lemma R_halts : forall Γ e τ, R Γ e τ -> halts e.
Proof. destruct τ; simpl; intros; intuition. Qed.

Lemma R_types : forall Γ e τ, R Γ e τ -> Γ ⊢ e ∈ τ.
Proof. destruct τ; simpl; intros; intuition. Qed.

Section Bot.
  Lemma nexists_base : ~ exists e, [] ⊢ e ∈ ⊥.
  Proof.
    intros [e H]. induction e; inv H.
    - rewrite nth_error_nil in H1; discriminate.
    - intuition.
  Abort.
End Bot.

Section PierceLemmas.
  Local Hint Extern 0 => value_step_contra : core.
  Local Hint Extern 0 =>
  match goal with
  | H: _, IH: forall _, _ -> False |- _ => apply IH in H; contradiction
  | H: _, IH: forall _, ~ _ |- _ => apply IH in H; contradiction
  end : core.

  Lemma step_preserves_halting : forall e e',
    e -->  e' -> halts e -> halts e'.
  Proof.
    intros e e' He [e'' [Hs Hnf]]; unfold halts.
    exists e''; inv Hs; intuition.
    pose proof step_deterministic _ _ _ He H; subst.
    assumption.
  Qed.

  Local Hint Constructors refl_trans_closure : core.

  Lemma unstep_preserves_halting : forall e e',
    e -->  e' -> halts e' -> halts e.
  Proof.
    intros ? ? ? [? [? ?]]; unfold halts; eauto 4.
  Qed.

  Local Hint Resolve R_halts : core.
  Local Hint Resolve R_types : core.
  Local Hint Resolve step_preserves_halting : core.
  Local Hint Resolve preservation : core.
  Local Hint Constructors step : core.
  Local Hint Resolve beta_reduce_step : core.

  Lemma step_preserves_R : forall τ Γ e e',
      e -->  e' -> R Γ e τ -> R Γ e' τ.
  Proof.
    induction τ; intros;
      simpl in *; intuition; eauto 4.
  Qed.

  Local Hint Resolve unstep_preserves_halting : core.
  Local Hint Constructors check : core.
  
  Lemma unstep_preserves_R : forall τ Γ e e',
      Γ ⊢ e ∈ τ -> e -->  e' -> R Γ e' τ -> R Γ e τ.
  Proof.
    induction τ; intros;
      simpl in *; intuition; eauto 6.
  Qed.

  Hint Resolve step_preserves_R : core.
  
  Lemma step_star_preserves_R : forall e e' τ Γ,
      e -->* e' -> R Γ e τ -> R Γ e' τ.
  Proof.
    intros ? ? t g Hms;
      generalize dependent t;
      generalize dependent g;
      induction Hms; intros; eauto 3.
  Qed.

  Hint Resolve unstep_preserves_R : core.

  Lemma unstep_star_preserves_R : forall e e' τ Γ,
      Γ ⊢ e ∈ τ -> e -->* e' -> R Γ e' τ -> R Γ e τ.
  Proof.
    intros ? ? t g ? Hms;
      generalize dependent t;
      generalize dependent g;
      induction Hms; intros; eauto 4.
  Qed.

  Local Hint Constructors value : core.
  Local Hint Unfold halts : core.
  Local Hint Extern 0 => inv_step_bad : core.

  Lemma check_R : forall τ Γ e,
      Γ ⊢ e ∈ τ -> R Γ e τ.
  Proof.
    intros ? ? ? H; induction H;
      simpl in *; intuition; eauto.
    - destruct τ; simpl; intuition; eauto.
      admit.
    (*- 
    - assert (Γ ⊢ e2 ∈ τ) by eauto.
      Fail apply progress_thm in H1 as [? | [e2' ?]].
      destruct (value_exm e2) as [? | ?].
      + apply unstep_preserves_R with (beta_reduce e e2); eauto.
        admit.
      + 
    - rewrite nth_error_nil in H; discriminate.
    - clear IHcheck.
      destruct (value_exm e2) as [? | ?].
      + apply unstep_preserves_R with (beta_reduce e e2); eauto. *)
  Abort.
  
  Theorem normalization : forall e τ,
      [] ⊢ e ∈ τ -> halts e.
  Proof.
    intros.
    apply (R_halts [] _ τ).
  Abort.
End PierceLemmas.

(*
Lemma app_end_cons : forall A l (a : A),
    exists h t, l ++ [a] = h :: t.
Proof. intros ? [] ?; simpl; eauto 3. Qed.

Fixpoint nat_list' (n : nat) : list nat :=
  match n with
  | O => []
  | S n => n :: nat_list' n
  end.
(**[]*)

Fixpoint nat_list'' (n : nat) : list nat :=
  match n with
  | O => []
  | S n => nat_list'' n ++ [n]
  end.
(**[]*)

Lemma nat_list''_length : forall n, length (nat_list'' n) = n.
Proof.
  induction n; simpl; auto.
  rewrite app_length.
  rewrite IHn. simpl. lia.
Qed.

Lemma nat_list''_app_end : forall n,
    nat_list'' n ++ [n] = 0 :: map S (nat_list'' n).
Proof.
  induction n as [| n IHn]; simpl; auto.
  rewrite map_last. rewrite IHn at 1.
  reflexivity.
Qed.

Lemma skipn_map_comm : forall A B (f : A -> B) n l,
    skipn n (map f l) = map f (skipn n l).
Proof.
  induction n; destruct l; simpl; auto 1.
Qed.

Lemma skipn_nat_list'' : forall n m,
    skipn n (nat_list'' (n + m)) = map (fun i => n + i) (nat_list'' m).
Proof.
  induction n as [| n IHn]; intros m; simpl.
  - rewrite map_id. reflexivity.
  - rewrite nat_list''_app_end.
    rewrite <- map_map
      with (f := fun i => n + i) (g := S).
    rewrite skipn_map_comm. f_equal. auto.
Qed.

Definition nat_list (n : nat) : list nat := rev (nat_list' n).

Lemma nat_list_nat_list'' : forall n,
    nat_list n = nat_list'' n.
Proof.
  intros n; unfold nat_list.
  induction n; simpl; auto 1.
  rewrite IHn. reflexivity.
Qed.

Section FoldLeftIter.
  Context {A B : Type}.
  Variable f : nat -> A -> B -> A.

  Fixpoint fold_left_iter' (i : nat) (a : A) (bs : list B) : A :=
    match bs with
    | [] => a
    | b :: bs => fold_left_iter' (S i) (f i a b) bs
    end.
  (**[]*)

  Definition fold_left_iter (init : A) (bs : list B) : A :=
    fold_left_iter' 0 init bs.
  (**[]*)

  Lemma fold_left_iter'_app : forall l1 l2 i a,
      fold_left_iter' i a (l1 ++ l2) =
      fold_left_iter' (i + length l1) (fold_left_iter' i a l1) l2.
  Proof.
    induction l1 as [| h1 t1 IHt1]; intros; simpl in *.
    - f_equal; auto 1; lia.
    - rewrite IHt1. f_equal; auto 1; lia.
  Qed.

  Lemma fold_left_iter_app : forall l1 l2 a,
      fold_left_iter a (l1 ++ l2) =
      fold_left_iter' (length l1) (fold_left_iter a l1) l2.
  Proof.
    intros. unfold fold_left_iter.
    rewrite fold_left_iter'_app. reflexivity.
  Qed.

  Lemma fold_left_iter'_fold_left_combine : forall l i a,
      fold_left_iter' i a l =
      fold_left
        (fun a '(i,b) => f i a b)
        (combine (map (fun m => i + m) (nat_list'' (length l))) l) a.
  Proof.
    induction l; intros; simpl; auto 1.
    rewrite nat_list''_app_end; simpl.
    rewrite IHl. f_equal.
    - rewrite map_map. repeat f_equal.
      extensionality x; lia.
    - f_equal; lia.
  Qed.

  Lemma fold_left_iter_fold_left_combine : forall a l,
      fold_left_iter a l =
      fold_left
        (fun a '(i,b) => f i a b)
        (combine (nat_list'' (length l)) l) a.
  Proof.
    intros; unfold fold_left_iter.
    rewrite fold_left_iter'_fold_left_combine; simpl.
    rewrite map_id. reflexivity.
  Qed.
End FoldLeftIter.

Lemma fold_left_iter'_fold_left : forall A B (f : A -> B -> A) l i a,
    fold_left_iter' (fun _ a b => f a b) i a l = fold_left f l a.
Proof.
  induction l as [| h t IHt]; intros; simpl; auto 1.
Qed.

Lemma fold_left_iter_fold_left : forall A B (f : A -> B -> A) l a,
    fold_left_iter (fun _ a b => f a b) a l = fold_left f l a.
Proof.
  intros; unfold fold_left_iter.
  apply fold_left_iter'_fold_left.
Qed.

(** Pierce's notion of multi-substituions. *)
Definition msubi (i : nat) (env : list expr) (e : expr) : expr :=
  fold_left_iter' (fun i e esub => sub i esub e) i e env.
(**[]*)

Definition msub := msubi 0.

Section PierceLemmas.
  Lemma sub_closed : forall k i e esub,
    k <= i ->
    closed k e ->
    sub i esub e = e.
  Proof.
    intros ? i ? esub ? Hc;
      generalize dependent esub;
      generalize dependent i;
      induction Hc; intros; simpl;
        try f_equal; auto 2.
    - destroy_arith.
    - apply IHHc; lia.
  Qed.

  (** 
      [5 6 7 (esub/6) = 4 (shift 0 6 esub) 7]
      [(5 6 7 (esub/6))(es'/6)
      = (4 (shift 0 6 esub) 7)(es'/6) = 3 ? 7]
   *)
  Lemma duplicate_sub : forall e es es' i,
      closed 0 es ->
      sub i es' (sub i es e) = sub i es e.
  Proof.
  Abort.

  Lemma swap_sub : forall e es es' i i',
      i <> i' ->
      (*k <= i ->
      k <= i' ->*)
      closed 0 es ->
      sub i' es' (sub i es e) = sub i es (sub i' es' e).
  Proof.
    induction e; intros; simpl.
    - destroy_arith; admit.
    - f_equal. apply IHe; try lia; auto.
    - f_equal;
      try rewrite IHe1; try rewrite IHe2; try lia; auto.
  Abort.
  
  Lemma msubi_closed : forall env k i e,
      k <= i -> closed k e -> msubi i env e = e.
  Proof.
    unfold msubi.
    induction env; intros; simpl; try reflexivity.
    rewrite sub_closed with (k := k) by auto 1.
    apply IHenv with (k := k); auto 1. lia.
  Qed.

  (*Lemma sub_msub : forall env i v e,*)

  Lemma msubi_var : forall env k i n,
      k <= i ->
      Forall (closed k) env ->
      msubi i env !n =
      match nth_error env n with
      | None => !n
      | Some es => shift 0 i es
      end.
  Proof.
    unfold msubi.
    induction env; intros ? ? ? ? HF;
      inv HF; simpl.
    - rewrite nth_error_nil. reflexivity.
    - destroy_arith; destruct n as [| n];
        simpl in *; subst; try lia.
  Abort.
End PierceLemmas.
*)
