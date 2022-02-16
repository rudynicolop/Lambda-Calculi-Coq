Require Import Lambda.Util Coq.Program.Equality.

(** Note: many of the helper lemmas
          and proof techniques
          are inspired by those of
          Kazuhiko Sakaguchi:
          [https://github.com/pi8027/lambda-calculus]
*)        

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

(** * Static Semantics *)

Reserved Notation "Γ '⊢' e '∈' τ" (at level 40).

Inductive typing (Γ : list type) : expr -> type -> Prop :=
| typ_var n τ :
    nth_error Γ n = Some τ ->
    Γ ⊢ !n ∈ τ
| typ_lam τ τ' e :
    (τ :: Γ) ⊢ e ∈ τ' ->
    Γ ⊢ λ τ ⇒ e ∈ τ → τ'
| typ_app τ τ' e1 e2 :
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

Section Bred_exm.
  Local Hint Constructors bred : core.

  Lemma bred_exm : forall e,
      (exists e', e -->  e') \/ forall e', ~ e -->  e'.
  Proof.
    intro e;
      induction e as
        [n
        | t e [[e' IHe]| IHe]
        | e1 [[e1' IHe1] | IHe1] e2 [[e2' IHe2] | IHe2]]; eauto;
        try (right; intros e' He'; inv He';
             intuition; eauto; contradiction).
    destruct e1 as [m | t1 e1 | e11 e12]; eauto;
      try (right; intros e' He'; inv He';
           intuition; eauto; contradiction).
  Qed.
End Bred_exm.

Section BredSub.
  Local Hint Constructors bred : core.
  Local Hint Unfold beta_reduce : core.

  Lemma sub_bred : forall e e',
      e -->  e' -> forall n es, sub n es e -->  sub n es e'.
  Proof.
    intros e e' Hred; induction Hred;
      intros n es; simpl; auto.
    unfold beta_reduce.
    rewrite sub_sub_distr by lia; simpl.
    replace (n - 0) with n by lia.
    replace (sub 0 [sub n es e2] (sub (S n) es e1))
      with (beta_reduce (sub (S n) es e1) (sub n es e2))
      by reflexivity; auto.
  Qed.

  Local Hint Resolve sub_bred : core.

  Lemma beta_reduce_bred : forall e1 e1' e2,
      e1 -->  e1' -> beta_reduce e1 e2 -->  beta_reduce e1' e2.
  Proof. autounfold with core; auto. Qed.
End BredSub.

Section Preservation.
  Local Hint Constructors typing : core.
  Local Hint Resolve typing_beta_reduce : core.

  Theorem preservation : forall e e',
      e -->  e' -> forall g t, g ⊢ e ∈ t -> g ⊢ e' ∈ t.
  Proof.
    intros e e' He; induction He;
      intros g T Ht; inv Ht; eauto.
    inv H1; eauto.
  Qed.
End Preservation.

Section CanonicalForms.
  Local Hint Constructors bred : core.
  
  Lemma canonical_forms_lambda : forall e T t,
    [] ⊢ e ∈ T → t ->
    (forall e', ~ e -->  e') ->
    exists body, e = λ T ⇒ body.
  Proof.
    intro e;
      induction e as [n | T' e IHe | e1 IHe1 e2 IHe2];
      intros T t HeTt He; inv HeTt; simpl in *; eauto.
    - rewrite nth_error_nil in H0; discriminate.
    - exfalso. apply IHe1 in H1; eauto.
      + destruct H1 as [e1' He1]; subst.
        specialize He with (e' := beta_reduce e1' e2); auto.
      + intros e1' He1.
        specialize He with (e' := e1' ⋅ e2); auto.
  Qed.
End CanonicalForms.

Section Progress.
  Local Hint Constructors bred : core.

  Theorem progress_thm : forall e t,
      [] ⊢ e ∈ t ->
      (exists e', e -->  e') \/ exists T v, e = λ T ⇒ v.
  Proof.
    intro e;
      induction e as
        [ n
        | T e IHe
        | e1 IHe1 e2 IHe2 ];
      intros t Het; inv Het; eauto.
    - rewrite nth_error_nil in H0; discriminate.
    - pose proof IHe1 _ H1 as IH1; clear IHe1.
      pose proof IHe2 _ H3 as IH2; clear IHe2.
      destruct IH1 as [[e1' IH1] | [T1 [v1 IH1]]];
        destruct IH2 as [[e2' IH2] | [T2 [v2 IH2]]];
        subst; eauto.
  Qed.
End Progress.

Notation "e '-->*' e'"
  := (refl_trans_closure bred e e')
       (at level 40, no associativity).

(** Termination predicate. *)
Definition halts (e : expr) : Prop :=
  exists e', e -->* e' /\ forall e'', ~ e' -->  e''.

Section AccLemmas.
  Local Hint Constructors Acc : core.
  
  Lemma acc_pres : forall A B (f : A -> B) (R : A -> A -> Prop) (Q : B -> B -> Prop),
    (forall a1 a2, R a1 a2 -> Q (f a1) (f a2)) ->
    forall a, Acc Q (f a) -> Acc R a.
  Proof.
    intros A B f R Q Hmap a HQ.
    remember (f a) as fa eqn:Heqfa.
    generalize dependent a.
    induction HQ; intros a Heqfa; subst; eauto.
  Qed.

  Lemma Acc_ind2 :
    forall A B (RA : A -> A -> Prop) (RB : B -> B -> Prop) (P : A -> B -> Prop),
      (forall a b, (forall a', RA a' a -> P a' b) ->
              (forall b', RB b' b -> P a b') -> P a b) ->
      forall a b, Acc RA a -> Acc RB b -> P a b.
  Proof.
    intros A B R Q P H a b HA.
    generalize dependent b.
    induction HA; intros b HB;
      induction HB; eauto.
  Qed.
End AccLemmas.

(** Strongly Normalizing. *)
Definition SN : expr -> Prop := Acc (fun e' e => e -->  e').

Section HaltsSN.
  Local Hint Constructors refl_trans_closure : core.
  
  Lemma SN_halts : forall e, SN e -> halts e.
  Proof.
    intros e Hsn; unfold halts; induction Hsn.
    destruct (bred_exm x) as [[e He] | He]; eauto.
    apply H0 in He as He_. destruct He_ as [e' [He' He'']]; eauto.
  Qed.
End HaltsSN.

Section SNProp.
  Local Hint Unfold SN : core.

  Lemma SN_var : forall n, SN !n.
  Proof.
    intros n. constructor.
    intros e' Hred. inv Hred.
  Qed.
  
  Lemma bred_SN : forall e e',
    e -->  e' -> SN e -> SN e'.
  Proof.
    intros e e' Hbred Hsn; inv Hsn; auto.
  Qed.

  Local Hint Resolve bred_SN : core.

  Lemma multi_bred_SN : forall e e',
      e -->* e' -> SN e -> SN e'.
  Proof.
    intros e e' Hms; induction Hms; eauto.
  Qed.

  Local Hint Constructors Acc : core.
  Local Hint Resolve multi_bred_SN : core.

  Lemma not_bred_SN : forall e,
      (forall e', ~ e -->  e') -> SN e.
  Proof.
    intros e H; constructor.
    intros e' H'. apply H in H'. contradiction.
  Qed.
End SNProp.

Module StrongNorm.  
  Fixpoint teqb (t1 t2 : type) : bool :=
    match t1, t2 with
    | ⊥, ⊥ => true
    | T1 → t1, T2 → t2 => teqb T1 T2 && teqb t1 t2
    | _, _ => false
    end.
  (**[]*)

  Section TypeEq.
    Local Hint Resolve andb_true_intro : core.
    
    Lemma teqb_refl : forall t, teqb t t = true.
    Proof.
      intro t; induction t; simpl; intuition.
    Qed.

    Hint Rewrite Bool.andb_true_iff : core.

    Lemma eq_teqb : forall t1 t2, teqb t1 t2 = true -> t1 = t2.
    Proof.
      intro t1; induction t1; intros []; simpl;
        autorewrite with core; intuition;
          f_equal; eauto.
    Qed.

    Local Hint Resolve eq_teqb : core.
    Local Hint Resolve teqb_refl : core.
    Hint Rewrite teqb_refl : core.

    Lemma teqb_eq : forall t1 t2, teqb t1 t2 = true <-> t1 = t2.
    Proof.
      intuition; subst; trivial.
    Qed.

    Local Hint Resolve teqb_eq : core.
    Hint Rewrite teqb_eq : core.
    Local Hint Constructors Bool.reflect : core.

    Lemma teqb_reflect : forall t1 t2,
        Bool.reflect (t1 = t2) (teqb t1 t2).
    Proof.
      intros t1 t2.
      destruct (teqb t1 t2) eqn:Hteqb; auto.
      constructor. intros H.
      apply teqb_eq in H.
      rewrite H in Hteqb. discriminate.
    Qed.
  End TypeEq.

  Fixpoint types (g : list type) (e : expr) : option type :=
    match e with
    | !n => nth_error g n
    | λ t ⇒ e =>
      match types (t :: g) e with
      | None => None
      | Some T => Some (t → T)
      end
    | e1 ⋅ e2 =>
      match types g e1, types g e2 with
      | Some (T → t), Some T'
        => if teqb T T' then Some t else None
      | _, _ => None
      end
    end.
  (**[]*)

  Section TypingIff.
    Hint Rewrite teqb_refl : core.
    
    Lemma typing_types : forall g e t,
      g ⊢ e ∈ t -> types g e = Some t.
    Proof.
      intros g e t H;
        induction H; simpl in *;
          repeat match goal with
                 | H: types ?g ?t = Some _
                   |- context [types ?g ?t] => rewrite H; simpl
                 end; autorewrite with core; auto.
    Qed.

    Local Hint Constructors typing : core.
    Hint Rewrite teqb_eq : core.

    Lemma types_typing : forall e g t,
        types g e = Some t -> g ⊢ e ∈ t.
    Proof.
      intro e;
        induction e as [n | T e IHe | e1 IHe1 e2 IHe2];
        intros g t H; simpl in *; eauto.
      - destruct (types (T :: g) e) as [t' |] eqn:Heq;
          simpl in *; inv H; auto.
      - destruct (types g e1) as [[| T T'] |] eqn:Heq1;
          try discriminate.
        destruct (types g e2) as [t' |] eqn:Heq2;
          try discriminate.
        destruct (teqb T t') eqn:Heqt; inv H.
        autorewrite with core in *; subst; eauto.
    Qed.

    Local Hint Resolve typing_types : core.
    Local Hint Resolve types_typing : core.

    Lemma types_iff : forall g e t,
        types g e = Some t <-> g ⊢ e ∈ t.
    Proof. intuition. Qed.

    Local Hint Resolve types_iff : core.
    Local Hint Resolve typing_prefix : core.

    Lemma types_prefix : forall G g e t,
        types G e = Some t -> types (G ++ g) e = Some t.
    Proof. auto. Qed.

    Local Hint Resolve types_prefix : core.
    Hint Rewrite types_iff : core.
    
    Lemma types_append : forall G g e t,
        G ⊢ e ∈ t -> types (G ++ g) e = types G e.
    Proof.
      intros G g e t HG.
      assert (Hg: (G ++ g) ⊢ e ∈ t) by auto.
      rewrite <- types_iff in *.
      rewrite HG; rewrite Hg; reflexivity.
    Qed.
  End TypingIff.

  Section ListHyp.
    Fixpoint list_type (t : type) : list type :=
      match t with
      | ⊥ => []
      | T → t => T :: list_type T ++ list_type t
      end.
    (**[]*)

    Fixpoint list_expr (g : list type) (e : expr) : list type :=
      match types g e with
      | None => []
      | Some t => list_type t
      end ++
          match e with
          | !_ => []
          | λ t ⇒ e => list_expr (t :: g) e
          | e1 ⋅ e2 => list_expr g e1 ++ list_expr g e2
          end.
    (**[]*)

    Lemma list_expr_eq : forall g e,
        list_expr g e =
        match types g e with
        | None => []
        | Some t => list_type t
        end ++
            match e with
            | !_ => []
            | λ t ⇒ e => list_expr (t :: g) e
            | e1 ⋅ e2 => list_expr g e1 ++ list_expr g e2
            end.
    Proof.
      intros g []; reflexivity.
    Qed.

    Local Hint Resolve nth_error_length : core.
    Local Hint Resolve types_append : core.

    Lemma list_expr_append : forall e G g t,
        G ⊢ e ∈ t -> list_expr (G ++ g) e = list_expr G e.
    Proof.
      intro e;
        induction e as [n | T e IHe | e1 IHe1 e2 IHe2];
        intros G g t Het; inv Het; simpl.
      - assert (n < length G) by eauto.
        rewrite nth_error_app1 by lia. reflexivity.
      - rewrite app_comm_cons. erewrite IHe by eauto.
        erewrite types_append by eauto. reflexivity.
      - erewrite IHe1 by eauto. erewrite IHe2 by eauto.
        repeat erewrite types_append by eauto. reflexivity.
    Qed.
  End ListHyp.
  
  Definition neutral (e : expr) : Prop :=
    match e with
    | ! _ | _ ⋅ _ => True
    | λ _ ⇒ _ => False
    end.
  (**[]*)

  Fixpoint R (g : list type) (e : expr) (t : type) : Prop :=
    match t with
    | ⊥ => SN e
    | T → t => forall E, g ⊢ E ∈ T -> R g E T -> R g (e ⋅ E) t
    end.
  (**[]*)

  Section RProp.
    Local Hint Constructors typing : core.
    Local Hint Constructors bred : core.
    Local Hint Resolve bred_SN : core.
    Local Hint Resolve multi_bred_SN : core.
    Local Hint Resolve preservation : core.

    Lemma CR2 : forall t g e e',
        e -->  e' -> R g e t -> R g e' t.
    Proof.
      intro t;
        induction t as [| t1 IHt1 t2 IHt2];
        intros g e e' Hred HR; simpl in *;
          intuition; eauto.
    Qed.

    Local Hint Resolve CR2 : core.
    Local Hint Constructors Acc : core.
    Local Hint Unfold SN : core.
    Local Hint Unfold neutral : core.

    Lemma CR1_CR3 : forall t,
        (forall e g,
            Forall (fun t => In t g) (list_type t) ->
            g ⊢ e ∈ t -> R g e t -> SN e) /\
        (forall e g,
            Forall (fun t => In t g) (list_type t) ->
            g ⊢ e ∈ t -> neutral e ->
            (forall e', e -->  e' -> R g e' t) -> R g e t).
    Proof.
      intro t;
        induction t as
          [| t1 [IHt1_CR1 IHt1_CR3] t2 [IHt2_CR1 IHt2_CR3]];
        split; simpl; try (intuition; eauto; assumption).
      - intros e g HF Het HR. inv HF.
        rewrite Forall_app in H2; intuition.
        apply In_nth_error in H1 as [n Hnth].
        assert (g ⊢ e ⋅ !n ∈ t2) by eauto.
        assert (SN ((fun e => e ⋅ !n) e)).
        { eapply IHt2_CR1; eauto.
          apply HR; eauto.
          apply IHt1_CR3; eauto.
          intros ? Hn. inv Hn. }
        eapply acc_pres with (f := fun e => e ⋅ !n); eauto; simpl.
        intuition.
      - intros e g HF Het Hneut HR. inv HF.
        rewrite Forall_app in H2; intuition.
        assert (g ⊢ e ⋅ E ∈ t2) by eauto.
        assert (Hsn: SN E) by eauto. induction Hsn.
        eapply IHt2_CR3; eauto.
        intros e' He'; inv He'; simpl in *;
          try contradiction; eauto 6.
    Qed.
    
    Lemma CR1 : forall g e t,
        Forall (fun t => In t g) (list_type t) ->
        g ⊢ e ∈ t -> R g e t -> SN e.
    Proof.
      intros ? ? t.
      pose proof CR1_CR3 t as [HCR1 _]. eauto 2.
    Qed.

    Lemma CR3 : forall g e t,
        Forall (fun t => In t g) (list_type t) ->
        g ⊢ e ∈ t -> neutral e ->
        (forall e', e -->  e' -> R g e' t) -> R g e t.
    Proof.
      intros ? ? t.
      pose proof CR1_CR3 t as [_ HCR3]. eauto 2.
    Qed.

    Local Hint Resolve CR1 : core.
    Local Hint Resolve CR3 : core.
    Local Hint Resolve Forall_impl : core.
    Local Hint Resolve in_cons : core.
    Local Hint Resolve beta_reduce_bred : core.
    Local Hint Resolve sub_bred : core.

    Lemma abs_red : forall g e T t,
        Forall (fun t => In t g) (list_type (T → t)) ->
        g ⊢ λ T ⇒ e ∈ T → t ->
        (forall E, g ⊢ E ∈ T -> R g E T -> R g (beta_reduce e E) t) ->
        R g (λ T ⇒ e) (T → t).
    Proof.
      intros g e T t HF Het HR;
        inv HF; inv Het; simpl in *.
      rewrite Forall_app in H2. intuition.
      assert (Hbr: g ⊢ beta_reduce e E ∈ t) by eauto.
      assert (Hsn: SN e).
      { pose proof CR1 _ _ _ H3 Hbr (HR _ H2 H4) as Hsnbr.
        unfold beta_reduce in *.
        eapply acc_pres with (f := sub 0 [E]); eauto.
        intuition. }
      assert (HSN: SN E) by eauto.
      revert e E Hsn HSN H2 H4 HR Hbr H0.
      refine (Acc_ind2 _ _ _ _ _ _); intros.
      eapply CR3; eauto.
      intros e' He'; inv He'; eauto 8.
      inv H10. eauto 8.
    Qed.

    Local Hint Resolve typing_sub : core.

    Lemma R_var : forall g n t,
        Forall (fun t => In t g) (list_type t) ->
        nth_error g n = Some t ->
        R g !n t.
    Proof.
      intros g n t HF Hnth.
      apply CR3; auto.
      intros ? H'. inv H'.
    Qed.

    Local Hint Resolve R_var : core.
    
    Lemma reduce_lemma : forall e t g ts es,
        Forall (fun t => In t g) (list_expr (ts ++ g) e) ->
        Forall2 (typing g) es ts ->
        Forall2 (R g) es ts ->
        (ts ++ g) ⊢ e ∈ t ->
        R g (sub 0 es e) t.
    Proof.
      intro e;
        induction e as [n | T e IHe | e1 IHe1 e2 IHe2];
        intros t g ts es Hl Htyps HRs Het; inv Het.
      - simpl in *.
        assert (length es = length ts)
          by eauto using Forall2_length.
        rewrite shift0. rewrite H0 in Hl. rewrite app_nil_r in Hl.
        replace (n - 0) with n by lia.
        destruct (le_lt_dec (length es) n) as [Hesn | Hesn].
        + rewrite nth_overflow by lia.
          rewrite nth_error_app2 in H0 by lia.
          rewrite H. auto.
        + rewrite nth_error_app1 in H0 by lia.
          apply length_nth_error in Hesn as [e He].
          erewrite nth_error_nth by eauto.
          eapply Forall2_nth_error; eauto.
      - simpl in Hl.
        erewrite typing_types in Hl by eauto.
        simpl in Hl. inv Hl.
        rewrite Forall_app in H3.
        unfold sub; fold sub.
        apply abs_red; simpl; intuition.
        + constructor.
          replace 1 with (length [T]) by reflexivity.
          replace (T :: g) with ([T] ++ g) by reflexivity. eauto.
        + unfold beta_reduce.
          rewrite <- sub_append.
          apply IHe with (ts := T :: ts); simpl; intuition.
      - simpl in *.
        repeat erewrite typing_types in Hl by eauto.
        rewrite teqb_refl in Hl.
        repeat rewrite Forall_app in Hl.
        destruct Hl as [Ht [He1 He2]].
        pose proof IHe1 _ _ _ _ He1 Htyps HRs H1 as IH1; clear IHe1.
        pose proof IHe2 _ _ _ _ He2 Htyps HRs H3 as IH2; clear IHe2.
        simpl in IH1. apply IH1; eauto.
        replace g with ([] ++ g) by reflexivity.
        replace 0 with (@length type []) by reflexivity. eauto.
    Qed.

    Local Hint Resolve reduce_lemma : core.
    Local Hint Resolve typing_prefix : core.

    Theorem typing_SN : forall g e t, g ⊢ e ∈ t -> SN e.
    Proof.
      intros g e t Hget.
      assert (Happget: (g ++ list_expr g e) ⊢ e ∈ t) by eauto.
      rewrite <- sub_nil with (n := 0).
      pose proof reduce_lemma
           e t (g ++ list_expr g e) [] [] as H.
      assert (HF:
                Forall (fun t : type => In t (g ++ list_expr g e))
                       (list_expr ([] ++ g ++ list_expr g e) e)).
      { apply Forall_forall; simpl.
        erewrite list_expr_append by eauto.
        intuition. }
      pose proof H HF (Forall2_nil _) (Forall2_nil _) Happget as HR; clear H HF.
      pose proof CR1 (g ++ list_expr g e) (sub 0 [] e) t as Hcr1.
      assert (HF':
                Forall
                  (fun t : type => In t (g ++ list_expr g e)) (list_type t)).
      { rewrite list_expr_eq.
        erewrite typing_types by eauto.
        apply Forall_forall. intuition. }
      replace e with (sub 0 [] e) in Happget at 2 by eauto using sub_nil. eauto.
    Qed.
  End RProp.

  Fixpoint normal_order (e : expr) : option expr :=
    match e with
    | (λ _ ⇒ e1) ⋅ e2 => Some (beta_reduce e1 e2)
    | λ t ⇒ e => match normal_order e with
                | None => None
                | Some e' => Some (λ t ⇒ e')
                end
    | e1 ⋅ e2 => match normal_order e1 with
                | None => match normal_order e2 with
                         | None => None
                         | Some e2' => Some (e1 ⋅ e2')
                         end
                | Some e1' => Some (e1' ⋅ e2)
                end
    | ! _ => None
    end.

  Definition typed_expr (g : list type) (t : type) : Type :=
    {e : expr | g ⊢ e ∈ t }.
  (**[]*)

  Section NormalOrder.
    Local Hint Constructors bred : core.
    
    Lemma normal_order_bred : forall e e',
      normal_order e = Some e' -> e -->  e'.
    Proof.
      intro e;
        induction e as [? | t e IHe | e1 IHe1 e2 IHe2];
        intros e' Hno; simpl in *; try discriminate.
      - destruct (normal_order e) as [? |] eqn:Heq;
          try discriminate. inv Hno. eauto.
      - destruct (normal_order e1) as [e1' |] eqn:Heq1.
        + destruct e1; inv Hno; eauto.
        + destruct (normal_order e2)
            as [e2' |] eqn:Heq2;
            destruct e1; inv Hno; eauto.
    Qed.

    Local Hint Resolve normal_order_bred : core.
    Local Hint Resolve preservation : core.

    Lemma normal_order_preservation : forall e e',
        normal_order e = Some e' ->
        forall g t, g ⊢ e ∈ t -> g ⊢ e' ∈ t.
    Proof.
      eauto.
    Qed.

    Local Hint Resolve normal_order_preservation : core.

    Definition normal_order_typed
               g t (et : typed_expr g t) :
      sumor {et' : typed_expr g t | proj1_sig et -->  proj1_sig et'}
            (normal_order (proj1_sig et) = None).
    Proof.
      destruct (normal_order (proj1_sig et)) as [e' |] eqn:Heq.
      - left. destruct et as [e He]; simpl in *.
        assert (e -->  e') by eauto.
        assert (He': g ⊢ e' ∈ t) by eauto.
        refine (exist _ (exist _ e' He') _); auto.
      - right; trivial.
    Defined.
  End NormalOrder.

  Section Lemmas.
    Lemma typed_expr_acc : forall g t (et : typed_expr g t),
      Acc (fun (e' e : typed_expr g t) => proj1_sig e -->  proj1_sig e') et.
    Proof.
      intros g t [e Hget].
      apply typing_SN in Hget as HSN.
      unfold SN in HSN.
      pose proof @acc_pres
           (typed_expr g t) expr
           (@proj1_sig expr (fun e => g ⊢ e ∈ t)) as H.
      eapply H; eauto. intuition.
    Qed.

    Local Hint Resolve typed_expr_acc : core.

    Lemma typed_expr_wf : forall g t,
        well_founded
          (fun (et' et : typed_expr g t) =>
             proj1_sig et -->   proj1_sig et').
    Proof.
      unfold well_founded; auto.
    Qed.

    Definition multi_normal_order_typed g t :
      typed_expr g t -> typed_expr g t.
    Proof.
      refine
        (Fix
           (typed_expr_wf g t) (fun _ => typed_expr g t)
           (fun (et: typed_expr g t)
              (f: forall et': typed_expr g t,
                  (proj1_sig et -->  proj1_sig et') -> typed_expr g t) =>
              match normal_order_typed _ _ et with
              | inleft obj => f (proj1_sig obj) _
              | inright _ => et
              end)).
      destruct obj as [et' Heq]; auto.
    Defined.
  End Lemmas.

  Definition multi_normal_order g e t :
    g ⊢ e ∈ t -> expr :=
    fun H => proj1_sig (multi_normal_order_typed _ _ (exist _ e H)).
  (**[]*)

  Module Examples.
    Section Examples.
      Local Hint Constructors typing : core.
      
      Let basic := λ ⊥ ⇒ !0.
      
      Example basic_typing : [] ⊢ basic ∈ ⊥ → ⊥.
      Proof.
        subst basic; auto.
      Qed.

      (** WTF? *)
      (*Compute multi_normal_order _ _ _ basic_typing.*)
      (** If I replace all [Qed]s with [Defined],
          this command does not terminate. *)
    End Examples.
  End Examples.
End StrongNorm.

(* From Coq Require Extraction. *)
(* Recursive Extraction StrongNorm.multi_normal_order. *)
