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

Module SFPierce.
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
End PierceLemmas.

Section MorePierceLemmas.
  Inductive instantiation (g : list type)
    : list type -> list expr -> Prop :=
  | inst_nil :
      instantiation g [] []
  | inst_cons t ts v vs :
      instantiation g ts vs ->
      R (ts ++ g) v t ->
      instantiation g (t :: ts) (v :: vs).
  (**[]*)
      
  Lemma msub_preserves_typing : forall vs ts g' g e t,
      instantiation g' ts vs ->
      (g ++ ts ++ g') ⊢ e ∈ t ->
      (g ++ g') ⊢ (fold_left (fun e v => sub (length g) v e) vs e) ∈ t.
  Proof.
    intros vs ts g' g e t H.
    generalize dependent t;
      generalize dependent e;
      generalize dependent g.
    induction H; intros g e τ He; simpl in *; trivial.
    apply IHinstantiation; eauto.
    eapply typ_sub_weak; eauto.
    apply R_types. assumption.
  Qed.
  
  Lemma multi_beta_reduce_preserves_typing : forall g1 g2 vs e t,
    Forall2 (R []) vs g1 ->
    (g1 ++ g2) ⊢ e ∈ t ->
    g2 ⊢ (fold_left (fun e v => beta_reduce e v) vs e) ∈ t.
  Proof.
    intros g1; induction g1; intros g2 vs e t HF2 Het;
      inv HF2; simpl in *; trivial.
    apply IHg1; eauto.
    apply substitution_lemma with (τ' := a); auto.
    apply under_empty. apply R_types. assumption.
  Qed.

  Lemma subst_closed : forall v e n k,
      closed k e ->
      sub (k + n) v e = e.
  Proof.
    intros v e n k Hc.
    generalize dependent v;
      generalize dependent n.
    induction Hc; intros m v; simpl in *.
    - destroy_arith.
    - f_equal; auto.
    - f_equal; auto.
  Qed.

  Lemma msubst_closed : forall vs e n k,
      closed k e ->
      fold_left (fun e v => sub (k + n) v e) vs e = e.
  Proof.
    intro vs; induction vs as [| v vs IHvs];
      intros e n k Hc; simpl in *; trivial.
    rewrite subst_closed by assumption.
    apply IHvs; trivial.
  Qed.
    
  Lemma beta_reduce_closed : forall v e,
      closed 0 e -> beta_reduce e v = e.
  Proof.
    intros v e H; unfold beta_reduce.
    replace 0 with (0 + 0) by reflexivity.
    apply subst_closed. assumption.
  Qed.
  
  Lemma multi_beta_reduce_closed : forall vs e,
      closed 0 e ->
      fold_left beta_reduce vs e = e.
  Proof.
    intros vs e H. unfold beta_reduce.
    replace 0 with (0 + 0) by reflexivity.
    rewrite msubst_closed by auto. reflexivity.
  Qed.

  Lemma msub_R_var : forall ts g g' vs t n,
      instantiation g' ts vs ->
      nth_error ts n = Some t ->
      R (g ++ g') (fold_left (fun e v => sub (length g) v e) vs !n) t.
  Proof.
    intros ts g g' vs t n H.
    generalize dependent g;
      generalize dependent t;
      generalize dependent n.
    induction H; intros n τ g Hnth; simpl in *.
    - rewrite nth_error_nil in Hnth. discriminate.
    - destroy_arith.
      + apply IHinstantiation; auto.
        destruct n as [| n]; simpl in *; try lia; trivial.
      + subst n. admit.
      + apply IHinstantiation; auto. admit.
  Abort.
  
  Lemma multi_beta_reduce_R_var : forall Γ vs t n,
      Forall2 (R []) vs Γ ->
      nth_error Γ n = Some t ->
      R [] (fold_left beta_reduce vs !n) t.
  Proof.
    induction Γ as [| t g IHg];
      intros vs τ n Hvs Hnth; inv Hvs; simpl in *.
    - rewrite nth_error_nil in Hnth. discriminate.
    - cbn. destroy_arith.
      rewrite shift0. simpl in *. inv Hnth.
      rewrite multi_beta_reduce_closed; auto.
      apply R_types in H2.
      apply type_closed in H2. assumption.
  Qed.

  Lemma msubst_lam : forall vs τ e k,
      fold_left (fun e v => sub k v e) vs (λ τ ⇒ e) =
      λ τ ⇒ (fold_left (fun e v => sub (S k) v e) vs e).
  Proof.
    induction vs as [| v vs IHvs]; intros t e k; simpl in *; auto.
  Qed.

  Lemma R_prefix : forall t e g g',
      R g e t ->
      R (g ++ g') e t.
  Proof.
    induction t as [| t1 IHt1 t2 IHt2];
      intros e g g' H; simpl in *; intuition;
        auto using under_prefix.
    apply IHt2. apply H2.
  Admitted.

  Lemma forall2_instantiation : forall ts vs,
      Forall2 (R []) vs ts ->
      instantiation [] ts vs.
  Proof.
    induction ts as [| t ts IHts];
      intros [| v vs] H; inv H.
    - constructor.
    - constructor; auto.
      rewrite app_nil_r.
      replace ts with ([] ++ ts) by reflexivity.
      apply R_prefix. assumption.
  Qed.
    
  Lemma msubst_R : forall Γ vs e t,
      Forall2 (R []) vs Γ ->
      Γ ⊢ e ∈ t ->
      R [] (fold_left beta_reduce vs e) t.
  Proof.
    intros g vs e t HF2 Het.
    generalize dependent vs.
    induction Het; intros vs Hvs; simpl.
    - eapply multi_beta_reduce_R_var; eauto.
    - repeat split.
      + unfold beta_reduce.
        rewrite msubst_lam.
        apply value_halts. constructor.
      + unfold beta_reduce.
        rewrite msubst_lam.
        constructor.
        replace [τ] with ([τ] ++ []) by reflexivity.
        replace 1 with (length [τ]) by reflexivity.
        eapply msub_preserves_typing; eauto.
        apply forall2_instantiation; eauto.
        rewrite app_nil_r. assumption.
      + admit.
  Abort.

  Local Hint Constructors check : core.
  Local Hint Resolve R_types : core.
  Local Hint Resolve R_halts : core.
  Local Hint Unfold halts : core.
  Local Hint Constructors refl_trans_closure : core.
  Local Hint Resolve value_halts : core.
  Local Hint Constructors value : core.

  Lemma types_R : forall g e t,
      g ⊢ e ∈ t -> R g e t.
  Proof.
    intros g e t H.
    induction H; simpl in *;
      intuition; eauto.
    - Check multi_beta_reduce_R_var.
    (*- destruct τ as [| t1 t2]; simpl in *;
        intuition; eauto.
      + exists !n; intuition. inv H0.
      + exists !n; intuition. inv H0.
      + admit.
    - intuition; eauto.
      admit.
    - intuition.*)
  Abort.
End MorePierceLemmas.
End SFPierce.

Module FrenchApproach.
  Definition flip {A : Type} (R : A -> A -> Prop) (a2 a1 : A) := R a1 a2.
  
  Definition sn := Acc (flip step).

  Fixpoint R (g : list type) (e : expr) (t : type) : Prop :=
    g ⊢ e ∈ t /\ sn e /\
    match t with
    | ⊥ => True
    | t → t' => forall e2, R g e2 t -> R g (e ⋅ e2) t'
    end.

  Section SNHalts.
        Local Hint Constructors step : core.
        Local Hint Constructors value : core.
        
        Lemma step_exm : forall e,
            (exists e', e -->  e') \/ forall e', ~ e -->  e'.
        Proof.
          induction e as
              [
              | t e [[e' IHe] | IHe]
              | e1 [[e1' IHe1] | IHe1] e2 [[e2' IHe2] | IHe2]]; simpl in *;
            try (right; intros ? H; inv H; contradiction); eauto.
          - destruct (value_exm e1) as [He1 | He1]; eauto.
            right; intros e' He'; inv He'; eauto.
            apply IHe1 in H2. contradiction.
          - destruct (value_exm e1) as [He1 | He1];
              destruct (value_exm e2) as [He2 | He2];
              try inv He1; eauto;
                right; intros e' He'; inv He'; eauto.
            + apply IHe2 in H3; contradiction.
            + inv H2.
            + apply IHe1 in H2; contradiction.
            + apply IHe1 in H2; contradiction.
        Qed.

        Local Hint Constructors refl_trans_closure : core.

        Lemma sn_halts : forall e,
            sn e -> halts e.
        Proof.
          unfold sn, flip, halts.
          intros e Hsn.
          induction Hsn using Acc_inv_dep.
          destruct (step_exm x) as [[e' IHe'] | IHx]; eauto.
          apply H in IHe' as IH.
          destruct IH as [e'' [He' He'']]; eauto.
        Qed.

        Lemma value_sn : forall e, value e -> sn e.
        Proof.
          intros e Hv; inv Hv; unfold sn, flip.
          constructor. intros ? H; inv H.
        Qed.

        Lemma step_sn : forall e e',
            e -->  e' -> sn e -> sn e'.
        Proof.
          intros e e' Hs Hsn; unfold sn, flip in *.
          induction Hs; inv Hsn; eauto.
        Qed.

        Lemma sub_sn : forall e v i,
            sn (sub i v e) -> sn e.
        Proof.
          induction e as
              [ n
              | t e IHe
              | e1 IHe1 e2 IHe2 ];
            intros v i Hsn; simpl in *;
              unfold sn, flip in *; inv Hsn.
          - admit.
          - admit.
        Abort.

        Theorem types_sn : forall Γ e τ,
            Γ ⊢ e ∈ τ -> sn e.
        Proof.
          intros g e t Ht; unfold sn, flip.
          induction Ht.
          - constructor; intros ? Hn; inv Hn.
          - constructor; intros ? Hl; inv Hl.
          - constructor; intros e' He'; inv He'.
            + admit.
            + admit.
            + admit.
        Abort.
  End SNHalts.
End FrenchApproach.

Module Abella.
  (** Abella terms. *)
  Fail Inductive term : Set :=
  | term_app (tm1 tm2 : term)
  | term_lambda (A : type) (body : term -> term).

  (** Abella typing *)
  Fail Inductive term_of : term -> type -> Prop :=
  | of_app A B tm1 tm2 :
      term_of tm1 (A → B) ->
      term_of tm2 A ->
      term_of (term_app tm1 tm2) B
  | of_lambda A B body :
      (forall tm, term_of tm A -> term_of (body tm) B) ->
      term_of (term_lambda A body) (A → B).
  (**[]*)
  
  Inductive sn (e : expr) : Prop :=
  | sn_intro :
      (forall e', e -->  e' -> sn e') -> sn e.

  Remark sn_var : forall n, sn !n.
  Proof.
    intros n. constructor.
    intros ? H. inv H.
  Qed.

  Remark sn_lambda : forall t e, sn (λ t ⇒ e).
  Proof.
    intros t e. constructor.
    intros ? H. inv H.
  Qed.

  Section Sect.
    Local Hint Constructors step : core.
    Local Hint Constructors refl_trans_closure : core.
    Local Hint Resolve inject_trans_closure : core.
    
    Lemma sn_halts : forall e, sn e -> halts e.
    Proof.
      intros e H; unfold halts.
      induction H.
      pose proof FrenchApproach.step_exm e
        as [[e' He] | He]; eauto.
      apply H0 in He as Hee.
      destruct Hee as [e'' [He' He'']]; eauto.
    Qed.

    Definition neutral (e : expr) : Prop :=
      forall t bdy, e <> λ t ⇒ bdy.
    (**[]*)

    Fixpoint R (g : list type) (e : expr) (t : type) : Prop :=
      g ⊢ e ∈ t /\ sn e /\
      match t with
      | ⊥ => True
      | t1 → t2 => forall ee, R g ee t1 -> R g (e ⋅ ee) t2 
      end.
    (**[]*)

    Lemma R_check : forall g e t, R g e t -> g ⊢ e ∈ t.
    Proof.
      intros ? ? []; simpl; intuition.
    Qed.

    Lemma R_sn : forall g e t, R g e t -> sn e.
    Proof.
      intros ? ? []; simpl; intuition.
    Qed.

    Lemma step_sn : forall e e',
        e -->  e' -> sn e -> sn e'.
    Proof.
      intros e e' H Hsn; inv Hsn; eauto.
    Qed.

    Lemma unstep_sn : forall e e',
        e -->  e' -> sn e' -> sn e.
    Proof.
      intros e e' H Hsn.
      constructor. intros e'' He''.
      pose proof step_deterministic _ _ _ H He'';
        subst; assumption.
    Qed.

    Local Hint Resolve step_sn : core.
    Local Hint Resolve preservation : core.

    Lemma step_R : forall t e e' g,
        e -->  e' -> R g e t -> R g e' t.
    Proof.
      intro t; induction t;
        intros; simpl in *;
          intuition; eauto 4.
    Qed.

    Search refl_trans_closure.

    Local Hint Resolve unstep_sn : core.
    Local Hint Constructors check : core.
    Local Hint Resolve R_check : core.
    Local Hint Resolve R_sn : core.

    Lemma unstep_R : forall t g e e',
        g ⊢ e ∈ t -> e -->  e' -> R g e' t -> R g e t.
    Proof.
      intro t; induction t; intros;
        simpl in *; intuition; eauto 6.
    Qed.

    Local Hint Resolve step_R : core.
    Local Hint Resolve unstep_R : core.

    Lemma neutral_unstep : forall t g e e',
        neutral e -> g ⊢ e ∈ t ->
        e -->  e' -> R g e' t -> R g e t.
    Proof.
      induction t as [| t1 IHt1 t2 IHt2];
        unfold neutral in *; simpl in *; intuition; eauto.
      apply IHt2 with (e' := e' ⋅ ee); eauto.
      intros; discriminate.
    Qed.

    Local Hint Resolve sn_var : core.
    Local Hint Resolve sn_lambda : core.

    Lemma br_value_R : forall e1 t t',
        [t] ⊢ e1 ∈ t' ->
        (forall e2, value e2 -> R [] e2 t -> R [] (beta_reduce e1 e2) t') ->
        R [] (λ t ⇒ e1) (t → t').
    Proof.
      intros e1 t t' He1 Hbr; simpl.
      do 2 try split; eauto.
      (*intros e2 HR
      intuition.
      destruct (value_exm ee) as [Hv | Hv]; eauto 7.
      destruct (FrenchApproach.step_exm ee) as [Hs | Hs].
      apply unstep_R with (e' := beta_reduce e1 ee); eauto.*)
    Abort.
      

    Lemma sub_step_R : forall G g e1 t t',
        (G ++ t :: g) ⊢ e1 ∈ t' ->
        (forall e2, R g e2 t -> R (G ++ g) (sub (length G) e2 e1) t') ->
        R g (λ t ⇒ e1) (t → t').
    Proof.
      intros G g e1 t t' He1 Hsub.
      simpl in *.
    Abort.
  End Sect.
End Abella.
