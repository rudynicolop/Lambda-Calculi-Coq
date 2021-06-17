Require Import Lambda.Util Coq.Program.Equality.
Require Import FunctionalExtensionality.

Section NthError.
  Context {A : Type}.
  
  Lemma nth_error_nil : forall n, nth_error (@nil A) n = None.
  Proof. intros []; reflexivity. Qed.

  Hint Rewrite nth_error_nil : core.

  Lemma nth_error_length : forall (l : list A) n a,
      nth_error l n = Some a -> n < length l.
  Proof.
    intro l; induction l as [| h t IHt];
      intros [| n]; simpl; intros a H;
        autorewrite with core in *; try discriminate; try lia.
    apply IHt in H. lia.
  Qed.

  Lemma nth_error_app_plus : forall (l l' : list A) n,
      nth_error (l ++ l') (length l + n) = nth_error l' n.
  Proof.
    intros l l' n.
    rewrite nth_error_app2 by lia.
    f_equal; lia.
  Qed.

  Lemma nth_map : forall B (f : A -> B) l n a b,
      n < length l ->
      nth n (map f l) b = f (nth n l a).
  Proof.
    induction l as [| h t IHt];
      intros [| n] a b; simpl; intros; try lia; auto.
    apply IHt; lia.
  Qed.

  Lemma length_nth_error : forall (l : list A) n,
      n < length l -> exists a, nth_error l n = Some a.
  Proof.
    intro l; induction l as [| h t IHt];
      intros [| n] H; simpl in *; try lia; eauto.
    apply IHt. lia.
  Qed.
End NthError.

Section Forall2.
  Variables A B : Type.
  Variable R : A -> B -> Prop.
  
  Lemma Forall2_length : forall a b,
    Forall2 R a b -> length a = length b.
  Proof.
    intros a b H; induction H; simpl; auto.
  Qed.
  
  Lemma Forall2_impl : forall (Q : A -> B -> Prop) a b,
      (forall a b, R a b -> Q a b) ->
      Forall2 R a b -> Forall2 Q a b.
  Proof.
    intros Q a b H HP;
      induction HP; auto.
  Qed.

  Lemma Forall2_nth_error : forall la lb,
      Forall2 R la lb ->
      forall n a b, nth_error la n = Some a ->
               nth_error lb n = Some b ->
               R a b.
  Proof.
    intros la lb HR; induction HR;
      intros [| n] a b Hntha Hnthb;
      simpl in *; try discriminate.
    - inv Hntha; inv Hnthb. assumption.
    - pose proof IHHR _ _ _ Hntha Hnthb.
      assumption.
  Qed.
End Forall2.

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
Notation "e1 ⋅ e2"
  := (App e1 e2) (at level 8, left associativity) : expr_scope.
Notation "! n" := (Var n) (at level 0) : expr_scope.
Open Scope expr_scope.

Example id : expr := λ ⊥ ⇒ !0.
Example f2' : expr := λ ⊥ → ⊥ ⇒ λ ⊥ ⇒ !1 ⋅ !0.
Example t1 : type := (⊥ → ⊥) → ⊥ → ⊥.

(** * Static Semantics *)

Reserved Notation "Γ '⊢' e '∈' τ" (at level 40).

Inductive typing (Γ : list type) : expr -> type -> Prop :=
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
where "Γ '⊢' e '∈' τ" := (typing Γ e τ).
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

Section TypingLemmas.
  Local Hint Constructors typing : core.
  Local Hint Resolve nth_error_app1 : core.
  Local Hint Resolve nth_error_length : core.

  Lemma typing_prefix G e t :
      G ⊢ e ∈ t -> forall g, (G ++ g) ⊢ e ∈ t.
  Proof.
    intros H; induction H;
      intros g; eauto.
    constructor. rewrite nth_error_app1; eauto.
  Qed.
End TypingLemmas.

(** * Dynamic Semantics *)

(** Shifts free variables above a cutoff [c] up by [i]. *)
Fixpoint shift (c i : nat) (e : expr) : expr :=
  match e with
  | !n => ! if le_lt_dec c n then n + i else n
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

  Lemma shift_add : forall e d d' c c',
    c <= c' <= c + d -> shift c' d' (shift c d e) = shift c (d' + d) e.
  Proof.
    induction e as [n | t e IHe | e1 IHe1 e2 IHe2];
      intros; simpl.
    - destroy_arith.
    - rewrite IHe by lia. reflexivity.
    - f_equal; auto.
  Qed.

  Lemma shift_shift_distr : forall e d c d' c',
      c' <= c -> shift c' d' (shift c d e) = shift (d' + c) d (shift c' d' e).
  Proof.
    induction e as [n | t e IHe | e1 IHe1 e2 IHe2];
      intros; simpl; f_equal; auto.
    - destroy_arith.
    - rewrite IHe by lia. f_equal; lia.
  Qed.

  Local Hint Constructors typing : core.
  
  Lemma typing_shift : forall e G g g' t,
      (G ++ g) ⊢ e ∈ t ->
      (G ++ g' ++ g) ⊢ (shift (length G) (length g') e) ∈ t.
  Proof.
    intro e;
      induction e as [n | t e IHe | e1 IHe1 e2 IHe2];
      intros G g g' τ Het; inv Het; simpl; eauto.
    - constructor. destroy_arith.
      + rewrite Nat.add_comm.
        rewrite nth_error_app2 in * by lia.
        replace (length g' + n - length G)
          with (length g' + (n - length G)) by lia.
        rewrite nth_error_app_plus. assumption.
      + rewrite nth_error_app1 in * by lia.
        assumption.
    - constructor.
      replace (S (length G))
        with (length (t :: G)) by reflexivity.
      rewrite app_comm_cons. eauto.
  Qed.

  Lemma typ_weak_weak : forall e A Γ' Γ T,
      (Γ' ++ Γ) ⊢ e ∈ T ->
      (Γ' ++ A :: Γ) ⊢ shift (length Γ') 1 e ∈ T.
  Proof.
    intros e A G g t Het.
    replace 1 with (length [A]) by reflexivity.
    replace (G ++ A :: g)
      with (G ++ [A] ++ g) by reflexivity.
    apply typing_shift. assumption.
  Qed.

  Lemma thinning : forall e Γ T A,
      Γ ⊢ e ∈ T ->
      (A :: Γ) ⊢ shift 0 1 e ∈ T.
  Proof.
    intros e g T A Het.
    replace (A :: g) with ([] ++ A :: g) by reflexivity.
    replace 0 with (@length type []) at 1 by reflexivity.
    apply typ_weak_weak. assumption.
  Qed.

  Lemma thinning_n : forall Γ' Γ e T,
      Γ ⊢ e ∈ T ->
      (Γ' ++ Γ) ⊢ shift 0 (length Γ') e ∈ T.
  Proof.
    intros g' g e t Het.
    replace (g' ++ g) with ([] ++ g' ++ g) by reflexivity.
    replace 0 with (@length type nil) by reflexivity.
    apply typing_shift. assumption.
  Qed.
End ShiftLemmas.

Fixpoint sub (n: nat) (es: list expr) (e: expr) : expr :=
  match e with
  | !m => if le_lt_dec n m then
           shift 0 n (nth (m - n) es !(m - n - length es))
         else !m
  | λ τ ⇒ e => λ τ ⇒ (sub (S n) es e)
  | e1 ⋅ e2 => (sub n es e1) ⋅ (sub n es e2)
  end.
(**[]*)

Section SubShiftLemmas.
  Lemma sub_nil : forall e n,
      sub n [] e = e.
  Proof.
    induction e as [m | t e IHe | e1 IHe1 e2 IHe2]; intros; simpl;
      try (f_equal; eauto; assumption).
    destroy_arith.
  Qed.
    
  Lemma sub_shift_cancel : forall e n d c ts,
    c <= n -> length ts + n <= d + c ->
    sub n ts (shift c d e) = shift c (d - length ts) e.
  Proof.
    induction e as [m | t e IHe | e1 IHe1 e2 IHe2]; intros; simpl.
    - destroy_arith. rewrite nth_overflow by lia.
      simpl. f_equal. lia.
    - rewrite IHe by lia. reflexivity.
    - f_equal; auto.
  Qed.

  Lemma shift_sub_distr : forall e n d c ts,
      c <= n -> shift c d (sub n ts e) = sub (d + n) ts (shift c d e).
  Proof.
    induction e as [j | t e IHe | e1 IHe1 e2 IHe2]; intros; simpl.
    - destroy_arith. rewrite shift_add by lia.
      repeat (f_equal; try lia).
    - rewrite IHe by lia.
      do 2 f_equal. lia.
    - f_equal; auto.
  Qed.

  Lemma sub_shift_distr :  forall e ts n c d,
      n <= c ->
      shift c d (sub n ts e) =
      sub n (map (shift (c - n) d) ts) (shift (length ts + c) d e).
  Proof.
    induction e as [m | t e IHe | e1 IHe1 e2 IHe2];
      intros; simpl.
    - destroy_arith; rewrite map_length.
      + rewrite nth_overflow by lia.
        replace !(m + d - n - length ts)
          with (shift (c - n) d !(m - n - length ts)).
        * rewrite map_nth; simpl. destroy_arith.
          rewrite nth_overflow by lia; simpl.
          destroy_arith.
        * simpl. destroy_arith.
      + destruct (le_lt_dec (length ts) (m - n)) as [Hmnts | Hmnts].
        * rewrite nth_overflow by lia.
          rewrite nth_overflow
            by (try rewrite map_length; lia).
          simpl. destroy_arith.
        * rewrite nth_map with (a := !(m - n - length ts)) by lia.
          rewrite shift_shift_distr with (c' := 0) by lia.
          f_equal; try lia.
    - f_equal. rewrite IHe by lia.
      f_equal; try lia.
      f_equal; try lia.
    - f_equal; auto.
  Qed.
  
  Lemma sub_sub_distr : forall e n m xs ys,
      m <= n ->
      sub n xs (sub m ys e) =
      sub m (map (sub (n - m) xs) ys) (sub (length ys + n) xs e).
  Proof.
    induction e as [j | t e IHe | e1 IHe1 e2 IHe2]; intros; simpl.
    - destroy_arith.
      + rewrite nth_overflow by lia; simpl. destroy_arith.
        rewrite sub_shift_cancel
          by (try rewrite map_length; lia).
        rewrite map_length. do 3 (f_equal; try lia).
      + rewrite map_length.
        destruct (le_lt_dec (length ys) (j - m)) as [Hjmys | Hjmys].
        * rewrite nth_overflow by lia.
          rewrite nth_overflow
            by (try rewrite map_length; lia).
          simpl. destroy_arith.
        * rewrite nth_map with (a := !(j - m - length ys)) by lia.
          rewrite shift_sub_distr by lia.
          f_equal; lia.
    - f_equal. rewrite IHe by lia.
      f_equal; try lia.
      f_equal; try lia.
    - f_equal; auto.
  Qed.

  Lemma sub_append : forall e xs ys n,
      sub n (xs ++ ys) e = sub n xs (sub (length xs + n) ys e).
  Proof.
    induction e as [m | t e IHe | e1 IHe1 e2 IHe2];
      intros; simpl.
    - destroy_arith.
      + rewrite app_nth2 by lia.
        rewrite sub_shift_cancel by lia.
        rewrite app_length.
        repeat (f_equal; try lia).
      + rewrite app_nth1 by lia.
        rewrite app_length.
        repeat (f_equal; try lia).
    - f_equal. rewrite IHe by lia.
      repeat (f_equal; try lia).
    - f_equal; auto.
  Qed.

  Local Hint Constructors typing : core.

  Lemma typing_sub : forall e G ts g T es,
      Forall2 (typing g) es ts ->
      (G ++ ts ++ g) ⊢ e ∈ T ->
      (G ++ g) ⊢ sub (length G) es e ∈ T.
  Proof.
    intro e;
      induction e as [n | t e IHe | e1 IHe1 e2 IHe2];
      intros G ts g T es HF2 Het; inv Het; simpl; eauto.
    - assert (Hlen : length es = length ts)
        by eauto using Forall2_length.
      destroy_arith.
      + apply thinning_n.
        destruct (le_lt_dec (length es) (n - length G))
          as [Hesng | Hesng].
        * rewrite nth_overflow by lia.
          constructor. rewrite Hlen.
          repeat rewrite nth_error_app2 in H0 by lia.
          assumption.
        * rewrite nth_error_app2 in H0 by lia.
          rewrite nth_error_app1 in H0 by lia.
          apply length_nth_error in Hesng as [e Hnth].
          erewrite nth_error_nth by eauto.
          eapply Forall2_nth_error; eauto.
      + rewrite nth_error_app1 in H0 by lia.
        constructor. rewrite nth_error_app1 by lia.
        assumption.
    - replace (S (length G))
        with (length (t :: G)) by reflexivity.
      constructor. rewrite app_comm_cons. eauto.
  Qed.
End SubShiftLemmas.

(** Beta-reduction [(λx.e1) e2 -> e1{e2/x}]. *)
Definition beta_reduce (e1 e2 : expr) : expr := sub 0 [e2] e1.
(**[]*)

Lemma typing_beta_reduce : forall g e E t T,
    g ⊢ e ∈ t ->
    (t :: g) ⊢ E ∈ T ->
    g ⊢ (beta_reduce E e) ∈ T.
Proof.
  intros g e E t T He HE. unfold beta_reduce.
  replace g with ([] ++ g) by reflexivity.
  replace 0 with (@length type []) by reflexivity.
  eapply typing_sub; eauto.
Qed.
  
Reserved Notation "e1 '-->' e2" (at level 40).

(** Beta-reduction. *)
Inductive bred : expr -> expr -> Prop :=
| bred_bred t e1 e2 :
    (λ t ⇒ e1) ⋅ e2 -->  beta_reduce e1 e2
| bred_abs t e e' :
    e -->  e' ->
    λ t ⇒ e -->  λ t ⇒ e'
| bred_app_l el el' er :
    el -->  el' ->
    el ⋅ er -->  el' ⋅ er
| bred_app_r el er er' :
    er -->  er' ->
    el ⋅ er -->  el ⋅ er'
where "e1 '-->' e2" := (bred e1 e2).
