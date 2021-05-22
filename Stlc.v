Require Import Lambda.Util Coq.Program.Equality.

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

(** Substitution [e{esub/i}]. *)
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

  Lemma trival_progress : forall e, normal e \/ exists e', e -->  e'.
  Proof.
    induction e; eauto 3.
    - destruct IHe as [? | [? ?]]; eauto 4.
    - destruct (is_lambda_exm e1) as [HL | ?];
        try inv HL; eauto 4.
      destruct IHe1 as [? | [? ?]];
        destruct IHe2 as [? | [? ?]]; eauto 4.
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

  Fixpoint insert_nth {A : Type} (n : nat) (a : A) (l : list A) : list A :=
    match n with
    | 0 => a :: l
    | S n =>
      match l with
      | [] => [] (* idk? *)
      | h :: l => h :: insert_nth n a l
      end
    end.
  (**[]*)

  Lemma insert_nth_length_app : forall (A : Type) l1 l2 (a : A),
      insert_nth (length l1) a (l1 ++ l2) = l1 ++ a :: l2.
  Proof. induction l1; intros; simpl; f_equal; auto. Qed.

  Search (skipn _ (?l ++ _)).
  Lemma skipn_length_app : forall (A : Type) (l1 l2 : list A),
      skipn (length l1) (l1 ++ l2) = l2.
  Proof. induction l1; intros; simpl; f_equal; auto. Qed.

  Fixpoint remove_nth {A : Type} (n : nat) (l : list A) : list A :=
    match n,l with
    | 0,[] => []
    | 0, _::t => t
    | S _, [] => []
    | S n, h::t => h :: remove_nth n t
    end.

  Lemma remove_nth_of_nil : forall A n, @remove_nth A n [] = [].
  Proof. destruct n; reflexivity. Qed.

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

  (** [skipn] as a relation, like [trunc]. *)
  Inductive skip {A : Type} : nat -> list A -> list A -> Prop :=
  | skip0 l :
      skip 0 l l
  | skipS n h t l :
      skip n t l ->
      skip (S n) (h :: t) l.
  (**[]*)

  Lemma skip_skipn : forall A n (l : list A),
      n <= length l ->
      skip n l (skipn n l).
  Proof.
    Local Hint Constructors skip : core.
    induction n; destruct l; intros;
      simpl in *; eauto; try lia.
    constructor. apply IHn. lia.
  Qed.

  (** [insert_nth] as a relation, like [sub_in_env]. *)
  Inductive ins_nth {A : Type} (a : A) : nat -> list A -> list A -> Prop :=
  | ins_nth0 l :
      ins_nth a 0 l (a :: l)
  | ins_nthS n h t l :
      ins_nth a n t l ->
      ins_nth a (S n) (h :: t) (h :: l).
  (**[]*)

  Lemma ins_nth_insert_nth : forall A n (a : A) l,
      n <= length l ->
      ins_nth a n l (insert_nth n a l).
  Proof.
    Local Hint Constructors ins_nth : core.
    induction n; intros ? []; intros;
      simpl in *; try lia; eauto.
    constructor. apply IHn. lia.
  Qed.

  Lemma typ_sub_weak : forall e e' g1 g2 g3 t t' n,
      ins_nth t' n g2 g1 ->
      skip n g2 g3 ->
      g1 ⊢ e ∈ t ->
      g2 ⊢ e' ∈ t' ->
      g3 ⊢ sub n e' e ∈ t.
  Proof.
    induction e; intros ? ? ? ? ? ? ? HI HS He He';
      inv He; simpl in *; eauto.
    - admit.
    - constructor.
      apply IHe with (g1 := t :: g1) (g2 := t :: g2) (t' := t').
      + constructor. assumption.
      + constructor. admit.
      + assumption.
      + admit.
  Abort.

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

  Lemma typ_sub_weak : forall e e' Γ Γ' τ τ',
      (Γ ++ τ' :: Γ') ⊢ e ∈ τ ->
      Γ' ⊢ e' ∈ τ' ->
      (Γ ++ Γ') ⊢ sub (length Γ) e' e ∈ τ.
  Proof.
    induction e; intros ? ? ? ? ? He He';
      inv He; simpl in *; eauto.
    - destroy_arith.
      + constructor.
        Search (nth_error (_ ++ _)).
        Search (?a < ?c -> exists b, ?a + b = ?c).
        pose proof doi _ _ l as [b Hb]; subst.
        Search (nth_error (_ ++ _) (_ + _)).
        rewrite nth_error_app_plus in H0.
        Search (pred (_ + _)).
        rewrite <- Nat.add_pred_r by lia.
        rewrite nth_error_app_plus.
        destruct b; try lia; auto.
      + (** Helper lemma. *) admit.
      + constructor.
        rewrite nth_error_app1 in * by lia; auto.
    - constructor.
      replace (t :: Γ ++ Γ')
        with ((t :: Γ) ++ Γ') by reflexivity.
      replace (S (length Γ))
        with (length (t :: Γ)) by reflexivity.
      apply IHe with τ'; simpl; auto.
  Admitted.

  (** Failed attempts. *)
  
  Lemma typ_sub_weak' : forall e e' Γ τ τ' n,
      Γ ⊢ e ∈ τ ->
      remove_nth n Γ ⊢ e' ∈ τ' ->
      skipn (n + 1) Γ ⊢ sub n e' e ∈ τ.
  Proof.
    (*induction e; intros ? ? ? ? ? He ?; inv He; simpl in *; eauto.
    - admit.
    - constructor. induction Γ; simpl in *.
      + Hint Rewrite skipn_nil : core.
        Hint Rewrite remove_nth_of_nil : core.
        autorewrite with core in *.
        assert (H' : remove_nth n [t] ⊢ e' ∈ τ') by auto using under_empty.
        pose proof IHe _ _ _ _ _ H3 H' as IH.
        
        
      replace (remove_nth n Γ)
        with (remove_nth (S n) (t :: Γ)) in H.
      + pose proof IHe _ _ _ _ _ H3 H as IH.
        simpl in IH. admit.
      + simpl.
      destruct Γ as [| t' g]; simpl in *; constructor; auto.*)
  Abort.      
  
  Lemma typ_sub_weak' : forall e e' Γ Γ' τ τ',
      (Γ' ++ τ' :: Γ) ⊢ e ∈ τ ->
      (Γ' ++ Γ) ⊢ e' ∈ τ' -> Γ ⊢ sub (length Γ') e' e ∈ τ.
  Proof. (*
    intros e e' Γ Γ' t t' He.
    generalize dependent e'.
    remember (Γ' ++ t' :: Γ) as g eqn:Heqg.
    generalize dependent Γ'.
    generalize dependent Γ.
    dependent induction He; intros; subst; simpl; eauto.
    - admit.
    - constructor.
      replace (S (length Γ')) with (length (τ :: Γ')) by reflexivity.
      apply IHHe.
      apply IHHe with (t'0 := t').
      + simpl. admit.
      +
    induction He; intros; subst; simpl in *.
    - admit.
    - constructor.
      replace (S (length Γ')) with (length (τ :: Γ')) by reflexivity.
      apply IHHe.
      + admit.
      + admit.
    - eauto.
    induction e; intros ? ? ? ? ? He He'; inv He; simpl; eauto.
    - destroy_arith.
      + (** Need Helper Lemma. *) admit.
      + (** Need Helper Lemma. *) admit.
      + (** Need Helper Lemma. *) admit.
    - constructor.
      replace (S (length Γ')) with (length (t :: Γ')) by reflexivity.
      apply IHe with (τ' := τ').
      pose proof IHe e' Γ (t :: Γ') τ'0 τ' H2 as IH.
      apply IH; simpl.
      + admit.
      +
      apply IHe with (τ' := τ').
      replace (t :: insert_nth i τ' Γ)
        with (insert_nth (S i) τ' (t :: Γ))
        in H2 by reflexivity.
      replace (t :: skipn i Γ)
        with (skipn (S i) (t :: Γ)).
      + admit.
      + simpl. *)
  Abort.
      
    
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
    - inv H1. eapply substition_lemma; eauto.
  Qed.
End Preservation.
