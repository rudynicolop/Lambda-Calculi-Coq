Require Export Lambda.Util.Basic Init.Nat.
From Equations Require Export Equations.

(** De Bruijn syntax of terms. *)

Inductive term (S : Set) : Set :=
| sort (s : S)
| ident (x : nat)
| app (A B : term S)
| abs (A B : term S)
| pi (A B : term S).

Arguments sort {_}.
Arguments ident {_}.
Arguments app {_}.
Arguments abs {_}.
Arguments pi {_}.

Declare Scope term_scope.
Delimit Scope term_scope with term.

Notation "x '⋅' y"
  := (app x y)
       (at level 39, left associativity) : term_scope.
Notation "'λ' τ '⇒' t"
  := (abs τ t)
       (at level 42, right associativity) : term_scope.
Notation "'∏' x '`,' y"
  := (pi x y)
       (at level 42, right associativity) : term_scope.

Open Scope term_scope.

Section Sub.
  Context {sorts : Set}.
  
  Fixpoint Rename (ρ : nat -> nat) (t : term sorts) : term sorts :=
    match t with
    | sort _  => t
    | ident x => ident $ ρ x
    | A ⋅ B   => Rename ρ A ⋅ Rename ρ B
    | λ A ⇒ B => λ Rename ρ A ⇒ Rename (ext ρ) B
    | ∏ A `, B => ∏ Rename ρ A `, Rename (ext ρ) B
    end.

  Lemma Rename_mapply_id : forall A m,
      Rename (mapply m ext (fun n => n)) A = A.
  Proof.
    intro A;
      induction A as
      [ s | x | A ihA B ihb
      | A ihA B ihB | A ihA B ihB ];
      intros m;
      try specialize ihB with (m := S m);
      cbn in *; unfold "$"; f_equal; auto using mapply_id.
    generalize dependent x.
    induction m as [| m ih]; intro x; cbn; try reflexivity.
    destruct x as [| x]; cbn; f_equal; auto.
  Qed.
  
  Lemma Rename_id : forall A, Rename (fun n => n) A = A.
  Proof.
    intro A.
    pose proof Rename_mapply_id A 0 as h;
      cbn in h; assumption.
  Qed.

  Lemma map_Rename_id : forall As, map (Rename (fun n => n)) As = As.
  Proof.
    intro As; induction As as [| A As ih];
      cbn; f_equal; auto using Rename_id.
  Qed.
  
  Lemma Rename_mapply_ext : forall A ρ n,
      Rename (mapply (S n) ext ρ) (Rename (mapply n ext S) A)
      = Rename (mapply n ext S) (Rename (mapply n ext ρ) A).
  Proof.
    intro A;
      induction A as
      [ s | x | A ihA B ihB
      | A ihA B ihB | A ihA B ihB];
      intros ρ n; cbn; unfold "$"; f_equal;
      try pose proof ihB ρ (S n) as IHB;
      cbn in *; auto using mapply_ext.
  Qed.
  
  Lemma Rename_ext : forall A ρ,
      Rename (ext ρ) (Rename S A) = Rename S (Rename ρ A).
  Proof.
    intros A ρ.
    pose proof Rename_mapply_ext A ρ 0 as h;
      cbn in h; assumption.
  Qed.

  Lemma mapply_ext_add : forall m n k x,
      mapply m ext (add n) (mapply m ext (add k) x) = mapply m ext (add (n + k)) x.
  Proof.
    intro m; induction m as [| m ih];
      intros n k x; cbn; try lia.
    destruct x as [| x]; cbn; f_equal; auto.
  Qed.
  
  Lemma Rename_ext_add : forall A m n k,
      Rename (mapply m ext (add n)) (Rename (mapply m ext (add k)) A)
      = Rename (mapply m ext (add (n + k))) A.
  Proof.
    intro A; induction A as
      [ s | x | A ihA B ihb
      | A ihA B ihB | A ihA B ihB ];
      intros m n k; cbn; unfold "$";
      try specialize ihB with (S m) n k; try cbn in ihB;
      f_equal; auto using mapply_ext_add; try lia.
  Qed.
  
  Lemma Rename_add : forall A m n,
      Rename (add m) (Rename (add n) A) = Rename (add (m + n)) A.
  Proof.
    intros A m n.
    pose proof Rename_ext_add A 0 m n as h;
      cbn in h; assumption.
  Qed.

  Lemma map_Rename_add : forall As m n,
      map (Rename (add m)) (map (Rename (add n)) As)
      = map (Rename (add (m + n))) As.
  Proof.
    intro As; induction As as [| A As ih];
      intros m n; cbn; f_equal; auto using Rename_add.
  Qed.

  Lemma map_Rename_ext_add : forall As m n k,
      map (Rename (mapply m ext (add n))) (map (Rename (mapply m ext (add k))) As)
      = map (Rename (mapply m ext (add (n + k)))) As.
  Proof.
    intro As; induction As as [| A As ih];
      intros m n k; cbn; f_equal; auto using Rename_ext_add.
  Qed.
  
  Definition exts (σ : nat -> term sorts) (x : nat) : term sorts :=
    match x with
    | O   => ident O
    | S n => Rename S $ σ n
    end.
  
  Fixpoint subs (σ : nat -> term sorts) (t : term sorts) : term sorts :=
    match t with
    | sort _ => t
    | ident x   => σ x
    | A ⋅ B => subs σ A ⋅ subs σ B
    | λ A ⇒ B => λ subs σ A ⇒ subs (exts σ) B
    | ∏ A `, B => ∏ subs σ A `, subs (exts σ) B
    end.
  
  Definition sub_helper (t : term sorts) (x : nat) : term sorts :=
    match x with
    | O => t
    | S n => ident n
    end.

  Lemma mapply_exts_ident : forall n x a,
      mapply n exts (sub_helper a) (mapply n ext S x) = ident x.
  Proof.
    intros n x a; depind n; cbn; auto.
    destruct x as [| x]; cbn; auto.
    unfold "$"; rewrite IHn; reflexivity.
  Qed.

  Local Hint Resolve mapply_exts_ident : core.
  
  Lemma subs_rename_S : forall (B : term sorts) a n,
      subs
        (mapply n exts (sub_helper a))
        (Rename (mapply n ext S) B) = B.
  Proof.
    intros B a n; depind B; cbn; f_equal; auto;
      specialize IHB2 with a (S n);
      cbn in *; assumption.
  Qed.

  Lemma Rename_ident_distr : forall x n ρ C,
      Rename (mapply n ext ρ) (mapply n exts (sub_helper C) x)
      = mapply n exts (sub_helper (Rename ρ C)) (ext (mapply n ext ρ) x).
  Proof.
    intro x; induction x as [| x ihx];
      intros [| n] ρ C; cbn; unfold "$"; try reflexivity.
    rewrite Rename_ext; f_equal; auto.
  Qed.
  
  Lemma Rename_subs_distr : forall (A B : term sorts) ρ n,
      Rename
        (mapply n ext ρ)
        (subs (mapply n exts (sub_helper B)) A)
      = subs
          (mapply n exts (sub_helper (Rename ρ B)))
          (Rename (mapply (S n) ext ρ) A).
  Proof.
    intro A;
      induction A as
      [ s | x | A ihA B ihB
      | A ihA B ihB | A ihA B ihB];
      intros C ρ n; cbn; unfold "$";
      try (f_equal; eauto using Rename_ident_distr;
           try pose proof ihB C ρ (S n) as ihB; cbn in *; assumption).
  Qed.
      
  Definition sub (body arg : term sorts) : term sorts :=
    subs (sub_helper arg) body.
End Sub.

Notation "x '[[' y ']]'"
  := (sub x y) (at level 12, left associativity) : term_scope.

Lemma sub_rename_S : forall {sorts : Set} (B a : term sorts),
    (Rename S B) [[ a ]] = B.
Proof.
  intros sorts B a; unfold "_ [[ _ ]]".
  pose proof subs_rename_S B a 0 as h; cbn in h; assumption.
Qed.

Lemma Rename_sub_distr : forall {sorts : Set} (A B : term sorts) ρ,
    Rename ρ (A [[ B ]]) = Rename (ext ρ) A [[ Rename ρ B ]].
Proof.
  intros sorts A B ρ; unfold "_ [[ _ ]]".
  pose proof Rename_subs_distr A B ρ 0 as h;
    cbn in h; assumption.
Qed.

Notation "x '→' y"
  := (pi x (Rename S y))
       (at level 41, right associativity).

Lemma Rename_arrow : forall {sorts : Set} (A B : term sorts) ρ,
    Rename ρ (A → B) = Rename ρ A → Rename ρ B.
Proof.
  intros sorts A B ρ; cbn; f_equal;
    auto using Rename_ext.
Qed.

Reserved Notation "x '-->' y" (no associativity, at level 80).

Inductive br {S : Set} : term S -> term S -> Prop :=
| br_sub A B C :
  (λ A ⇒ B) ⋅ C --> B [[ C ]]
| br_app_l A A' B :
  A --> A' ->
  A ⋅ B --> A' ⋅ B
| br_app_r A B B' :
  B --> B' ->
  A ⋅ B --> A ⋅ B'
| br_abs_l A A' B :
  A --> A' ->
  λ A ⇒ B --> λ A' ⇒ B
| br_abs_r A B B' :
  B --> B' ->
  λ A ⇒ B --> λ A ⇒ B'
| br_pi_l A A' B :
  A --> A' ->
  ∏ A `, B --> ∏ A' `, B
| br_pi_r A B B' :
  B --> B' ->
  ∏ A `, B --> ∏ A `, B'
where "x '-->' y" := (br x y) : type_scope.

(** Reflexive-transitive closure. *)
Reserved Notation "A '=β' B" (at level 80, no associativity).

Inductive br_clos {S : Set} : term S -> term S -> Prop :=
  br_refl A :
    A =β A
| br_trans A B C :
  A --> B -> B =β C -> A =β C
where "A '=β' B" := (br_clos A B) : type_scope.

Reserved Notation "A '⇝' B" (no associativity, at level 80).

(** Weak-head reduction. *)
Inductive wh {S : Set} : term S -> term S -> Prop :=
| wh_sub A B C :
  (λ A ⇒ B) ⋅ C ⇝ B [[ C ]]
| wh_app A A' B :
  A ⇝ A' ->
  A ⋅ B ⇝ A' ⋅ B
| wh_abs A A' B :
  A ⇝ A' ->
  λ A ⇒ B ⇝ λ A' ⇒ B
| wh_pi_l A A' B :
  A ⇝ A' ->
  ∏ A `, B ⇝ ∏ A' `, B
| wh_pi_r A B B' :
  B ⇝ B' ->
  ∏ A `, B ⇝ ∏ A `, B'
where "A '⇝' B" := (wh A B) : type_scope.

Reserved Notation "A '⇓' B" (at level 80, no associativity).

Inductive wh_norm {S : Set} : term S -> term S -> Prop :=
| wh_normal A :
  (forall B, ~ (A ⇝ B)) -> A ⇓ A
| wh_reduce A B C :
  A ⇝ B -> B ⇓ C -> A ⇓ C
where "A '⇓' B" := (wh_norm A B) : type_scope.

Definition obind {A B : Set} (o : option A) (ƒ : A -> option B) : option B :=
  match o with
  | None => None
  | Some a => ƒ a
  end.

Notation "o '>>=' f" := (obind o f) (at level 50, left associativity).
Notation "o '>>|' f" := (option_map f o) (at level 50, left associativity).
Notation "'let*' x ':=' c1 'in' c2"
  := (obind c1 (fun x => c2))
       (at level 61, x pattern, 
         format "'let*'  x  ':='  c1  'in' '//' c2", c1 at next level, 
         right associativity).
Notation "'let*' ' x ':=' c1 'in' c2"
  := (obind c1 (fun x => c2))
       (at level 61, x pattern, 
         format "'let*'  ' x  ':='  c1  'in' '//' c2", c1 at next level, 
         right associativity).

Reserved Notation "Γ '⊨' A ⇔ B ∈ C" (at level 80, no associativity).
Reserved Notation "Γ ⊩ A ↔ B ∈ C" (at level 80, no associativity).
Reserved Notation "A '≡' B" (at level 80, no associativity).

Variant not_lambda {S : Set} : term S -> Prop :=
  | not_lambda_sort s :
    not_lambda (sort s)
  | not_lambda_ident x :
    not_lambda (ident x)
  | not_lambda_app A B :
    not_lambda (A ⋅ B)
  | not_lambda_pi A B :
    not_lambda (∏ A `, B).

Inductive equiv {sorts : Set} : term sorts -> term sorts -> Prop :=
| equiv_sort s :
  sort s ≡ sort s
| equiv_ident x :
  ident x ≡ ident x
| equiv_app A A' B B' C C' D D' :
  A ⇓ A' -> B ⇓ B' ->
  C ⇓ C' -> D ⇓ D' ->
  A' ≡ C' -> B' ≡ D' ->
  A ⋅ B ≡ C ⋅ D
| equiv_pi A A' B B' C C' D D' :
  A ⇓ A' -> B ⇓ B' ->
  C ⇓ C' -> D ⇓ D' ->
  A' ≡ C' -> B' ≡ D' ->
  ∏ A `, B ≡ ∏ C `, D
| equiv_abs A A' B B' C C' D D' :
  A ⇓ A' -> B ⇓ B' ->
  C ⇓ C' -> D ⇓ D' ->
  A' ≡ C' -> B' ≡ D' ->
  λ A ⇒ B ≡ λ C ⇒ D
| equiv_abs_l A B B' C C' :
  not_lambda C -> B ⇓ B' ->
  Rename S C ⋅ ident 0 ⇓ C' ->
  B' ≡ C' ->
  λ A ⇒ B ≡ C
| equiv_abs_r A B B' C C' :
  not_lambda C -> B ⇓ B' ->
  Rename S C ⋅ ident 0 ⇓ C' ->
  C' ≡ B' ->
  C ≡ λ A ⇒ B
where "A '≡' B" := (equiv A B) : type_scope.

Section Lemmas.
  Context {sorts : Set}.

  Fixpoint whr (t : term sorts) : option (term sorts) :=
    match t with
    | sort _ | ident _ => None
    | (λ _ ⇒ B) ⋅ C => Some $ B [[ C ]]
    | A ⋅ B   => whr A >>| fun A' => A' ⋅ B
    | λ A ⇒ B => whr A >>| fun A' => λ A' ⇒ B
    | ∏ A `, B => match whr A with
                 | Some A' => Some $ ∏ A' `, B
                 | None => whr B >>| pi A
                 end
    end.
  
  Local Hint Constructors wh : core.

  Ltac match_some :=
    match goal with
    | h: match ?t with
         | Some _ => _
         | None => None
         end = Some _
      |- _ => destruct t eqn:?; try discriminate
    end.

  Ltac some_inv :=
    match goal with
    | h: Some _ = Some _ |- _ => inv h
    end.

  Lemma whr_wh : forall A B, whr A = Some B -> A ⇝ B.
  Proof.
    intros A; induction A; intros t h;
      cbn in *; try discriminate; eauto.
    - destruct A1; try discriminate;
        unfold "_ >>| _","$" in h;
        try match_some; some_inv; eauto.
    - unfold "_ >>| _","$" in h;
        try match_some; some_inv; eauto.
    - destruct (whr A1) as [A1' |] eqn:eqA1';
        unfold "_ >>| _","$" in h;
        try match_some; some_inv; eauto.
  Qed.
  
  Local Hint Constructors br : core.
  
  Lemma wh_br : forall A B : term sorts, A ⇝ B -> A --> B.
  Proof.
    intros A B h; induction h; eauto.
  Qed.

  Local Hint Constructors br_clos : core.
  Local Hint Constructors wh_norm : core.
  Local Hint Resolve wh_br : core.

  Lemma wh_norm_br_clos : forall A B : term sorts, A ⇓ B -> A =β B.
  Proof.
    intros A B h; induction h; eauto.
  Qed.

  Local Hint Constructors wh_norm : core.

  (** Uh, proving
      termination for [wh_norm] is
      difficult...*)
  Lemma wh_norm_ex : forall A : term sorts, exists A', A ⇓ A'.
  Proof.
    intro A;
      induction A as
      [s | x
      | A ihA B ihB
      | A ihA B ihB
      | A ihA B ihB];
      try match goal with
          | |- exists A', ?A ⇓ A'
            => exists A; apply wh_normal;
              intros ? h; inv h; contradiction
          end.
    - destruct ihA as [A' ihA].
      destruct ihB as [B' ihB].
      admit.
  Admitted.

  Local Hint Constructors equiv : core.
  
  Lemma equiv_refl : forall A : term sorts, A ≡ A.
  Proof.
    intro A;
      induction A as
      [s | x
      | A ihA B ihB
      | A ihA B ihB
      | A ihA B ihB]; eauto.
    - pose proof wh_norm_ex A as [A' hA].
      pose proof wh_norm_ex B as [B' hB].
      eapply equiv_app; eauto.
      + (* bruh *) admit.
      + (* bruh *) admit.
  Admitted.
End Lemmas.

Module Type Triple.
  Parameter sorts : Set.
  Parameter axiom : sorts -> sorts -> Prop.
  Parameter rule : sorts -> sorts -> sorts -> Prop.
End Triple.

Reserved Notation "Γ '⊢' A '∈' B" (no associativity, at level 80).

Module Judge (T : Triple).
  Import T.

  Inductive judge (Γ : list (term sorts)) : term sorts -> term sorts -> Prop :=
  | judge_sort s₁ s₂ :
    axiom s₁ s₂ ->
    Γ ⊢ sort s₁ ∈ sort s₂
  | judge_ident x A :
    nth_error Γ x = Some A ->
    Γ ⊢ ident x ∈ A
  | judge_app A B C a :
    Γ ⊢ C ∈ ∏ A `, B ->
    Γ ⊢ a ∈ A ->
    Γ ⊢ C ⋅ a ∈ B [[ a ]]
  | judge_pi A B s₁ s₂ s₃ :
    rule s₁ s₂ s₃ ->
    Γ ⊢ A ∈ sort s₁ ->
    map (Rename S) (A :: Γ) ⊢ B ∈ sort s₂ ->
    Γ ⊢ ∏ A `, B ∈ sort s₃
  | judge_abs A B b s₁ s₂ s₃ :
    rule s₁ s₂ s₃ ->
    Γ ⊢ A ∈ sort s₁ ->
    map (Rename S) (A :: Γ) ⊢ b ∈ B ->
    map (Rename S) (A :: Γ) ⊢ B ∈ sort s₂ ->
    Γ ⊢ λ A ⇒ b ∈ ∏ A `, B
  | judge_conv A B B' s :
    B =β B' ->
    Γ ⊢ B ∈ sort s ->
    Γ ⊢ A ∈ B ->
    Γ ⊢ A ∈ B'
  where "Γ '⊢' A '∈' B" := (judge Γ A B) : type_scope.
  
  Equations Derive Signature for judge.

  Local Hint Constructors judge : core.


  Lemma preservation : forall A A',
      A --> A' -> forall Γ B, Γ ⊢ A ∈ B -> Γ ⊢ A' ∈ B.
  Proof.
    intros A A' h Γ B ht.
    generalize dependent A'.
    induction ht; intros A' hA'; inv hA'; eauto.
    - inv ht1.
      + (* lemmas :
           1. [map (Rename S) (A :: Γ) ⊢ B ∈ C -> Γ ⊢ a ∈ A -> Γ ⊢ B [[a]] ∈ C [[a]]] *) admit.
      + (* lemma. *) admit.
    - apply IHht2 in H2 as h.
      (* lemmas:
         1. [a --> a' -> B [[ a ]] --> B [[ a' ]]].
         2. [Γ ⊢ A ∈ ∏ B `, C -> exists s, map (Rename S) A :: Γ ⊢ C ∈ sort s] *)
      assert (hs: exists s, map (Rename S) (A :: Γ) ⊢ B ∈ sort s) by admit.
      destruct hs as [s hs].
      apply judge_conv with (B := B [[ B' ]]) (s := s); eauto.
      + (* maybe [A =β B] needs to be symmetric? *) admit.
      + (* by substitution lemma. *) admit.
    - econstructor; eauto; cbn in *.
      (* lemmas:
         1. [ Γ =β Γ' -> Γ ⊢ A ∈ B -> Γ' ⊢ A ∈ B ] *) admit.
    - (* needs similar lemmas to above. *)
      apply IHht1 in H3 as h.
      apply judge_conv with (B := ∏ A'0 `, B) (s := s₃); eauto.
      + (* Congruence lemmas for [A =β B]. *) admit.
      + econstructor; eauto; cbn in *.
        (* needs conv context lemma. *) admit.
      + econstructor; eauto; cbn in *;
          (* needs conv context lemma. *) admit.
    - apply judge_conv with (B := B) (s := s); auto.
      apply IHht2. constructor.
    - apply judge_conv with (B:=B) (s:=s); auto.
      apply IHht2. constructor. assumption.
    - apply judge_conv with (B:=B) (s:=s); auto.
      apply IHht2. constructor. assumption.
    - apply judge_conv with (B:=B) (s:=s); auto.
      apply IHht2. constructor. assumption.
    - apply judge_conv with (B:=B) (s:=s); auto.
      apply IHht2. constructor. assumption.
    - apply judge_conv with (B:=B) (s:=s); auto.
      apply IHht2. constructor. assumption.
    - apply judge_conv with (B:=B) (s:=s); auto.
      apply IHht2. constructor. assumption.
  Admitted. 
  
  Lemma judge_abs_pi : forall Γ A B b s,
      map (Rename S) (A :: Γ) ⊢ b ∈ B ->
      Γ ⊢ ∏ A `, B ∈ s ->
      Γ ⊢ λ A ⇒ b ∈ ∏ A `, B.
  Proof.
    intros g A B b s hb hpi; depind hpi;
      try match goal with
          | h : ∏ _ `, _ = _ |- _ => inv h
          end; eauto.
  Qed.

  Lemma judge_app_arrow : forall Γ A B C a,
      Γ ⊢ C ∈ A → B ->
      Γ ⊢ a ∈ A ->
      Γ ⊢ C ⋅ a ∈ B.
  Proof.
    intros G A B C a hC ha.
    rewrite <- sub_rename_S with (B := B) (a := a); eauto.
  Qed.

  Lemma judge_Rename_ext_S : forall Γ B C,
      Γ ⊢ B ∈ C -> forall Es D,
        Es ++ Rename (add (length Es)) D
           :: map (Rename (add (length Es + 1))) Γ
           ⊢ Rename (mapply (length Es) ext S) B
           ∈ Rename (mapply (length Es) ext S) C.
  Proof.
    intros Γ B C h; induction h;
      intros Es D; cbn; unfold "$"; auto.
    - constructor. (*Search (mapply _ ext S).
      generalize dependent Γ;
        generalize dependent A;
        generalize dependent D;
        generalize dependent x.
      induction Es as [| E Es ih]; intros.
      + unfold length.
        rewrite <- map_Rename_add; cbn.
        rewrite <- eta_expansion with (f := S),
            map_Rename_id,nth_error_map, H; reflexivity.
      + replace (length (E :: Es)) with (1 + (length Es)) by reflexivity.
        rewrite <- Rename_add.
        do 2 rewrite <- map_Rename_add; cbn.
        rewrite <- eta_expansion with (f := S).
        destruct x as [| x]; cbn.
        specialize ih with 0 E A Γ.
        apply ih in H. cbn in H.*)
      admit.
    - rewrite Rename_sub_distr.
      econstructor; eauto.
    - econstructor; eauto; cbn.
      rewrite map_app.
      specialize IHh2 with
        (Es := Rename S (Rename (mapply (length Es) ext S) A)
                      :: map (Rename S) Es).
  Abort.
  
  Lemma judge_Rename_app : forall Γ B C,
      Γ ⊢ B ∈ C -> forall As Es,
        Es ++ As ++
           map (Rename (plus (length Es))) (map (Rename (plus (length As))) Γ)
           ⊢ Rename (mapply (length Es) ext (plus (length As))) B
           ∈ Rename (mapply (length Es) ext (plus (length As))) C.
  Proof.
    intros Γ B C h; induction h;
      intros As Es; cbn in *; unfold "$"; auto.
    - constructor.
      rewrite map_Rename_add. (*Print ext.*)
      (*Search (mapply _ ext).*)
      generalize dependent As.
      generalize dependent Γ.
      generalize dependent x.
      generalize dependent A.
      induction Es as [| E Es ih]; intros.
      + cbn; rewrite nth_error_app_plus,
          nth_error_map, H; reflexivity.
      + replace (length (E :: Es)) with
          (1 + length Es) by reflexivity.
        do 2 rewrite <- map_Rename_add; cbn.
        rewrite <- eta_expansion with (f := S).
        apply ih with (As:=As) in H as h.
        destruct x as [| x]; cbn.
        
  Abort.
  
  Lemma judge_Rename_app : forall Γ B C,
      Γ ⊢ B ∈ C -> forall As,
        As ++ map (Rename (plus (length As))) Γ
           ⊢ Rename (plus (length As)) B ∈ Rename (plus (length As)) C.
  Proof.
    intros Γ B C h; induction h; intro As; cbn in *; unfold "$"; auto.
    - constructor.
      rewrite nth_error_app_plus,
        nth_error_map, H; reflexivity.
    - rewrite Rename_sub_distr; econstructor; eauto.
    - econstructor; eauto; cbn.
      rewrite map_app. admit.
    - econstructor; eauto; cbn.
      rewrite map_app.
  Abort.
  
  Lemma judge_Rename_S : forall Γ E B C,
      Γ ⊢ B ∈ C ->
      E :: map (Rename S) Γ ⊢ Rename S B ∈ Rename S C.
  Proof.
    intros G E B C h; generalize dependent E;
      induction h; intro E; cbn in *; unfold "$"; auto.
    - constructor; cbn.
      rewrite nth_error_map, H; reflexivity.
    - rewrite Rename_sub_distr; cbn in IHh1.
      econstructor; eauto.
    - econstructor; eauto; cbn. admit.
    - econstructor; eauto; cbn. (*Check Rename_ext.*)
  Abort.
  
  Lemma judge_arrow : forall Γ A B s₁ s₂ s₃,
      rule s₁ s₂ s₃ ->
      Γ ⊢ A ∈ sort s₁ ->
      Γ ⊢ B ∈ sort s₂ ->
      Γ ⊢ A → B ∈ sort s₃.
  Proof.
    intros Γ A B s1 s2 s3 hr hA hB.
    econstructor; eauto; cbn.
  Abort.
End Judge.

(** System U definitions from
    [https://www.cs.cmu.edu/~kw/scans/hurkens95tlca.pdf]. *)

Module SystemU_Spec.
  Inductive U_sorts : Set := prop | type | triangle.

  Declare Scope U_sort_scope.
  Delimit Scope U_sort_scope with sort.
  Notation "'*'" := prop (at level 0, no associativity).
  Notation "'◻'" := type (at level 0, no associativity).
  Notation "'△'" := triangle (at level 0, no associativity).
  Open Scope U_sort_scope.
  
  Variant U_axiom : U_sorts -> U_sorts -> Prop :=
    | axiom_prop : U_axiom * ◻
    | axiom_type : U_axiom ◻ △.

  Variant U_rule : U_sorts -> U_sorts -> U_sorts -> Prop :=
    | prop_prop : U_rule * * *
    | type_prop : U_rule ◻ * *
    | type_type : U_rule ◻ ◻ ◻
    | triangle_prop : U_rule △ * *
    | triangle_type : U_rule △ ◻ ◻.

  Local Hint Constructors U_rule : core.
  
  Lemma U_rule_star : forall s, U_rule s * *.
  Proof.
    intros []; auto.
  Qed.
End SystemU_Spec.

Module SystemU_Triple <: Triple.
  Include SystemU_Spec.
  Definition sorts := U_sorts.
  Definition axiom := U_axiom.
  Definition rule := U_rule.
End SystemU_Triple.

Module SystemU.
  Export SystemU_Triple.
  Include Judge SystemU_Triple.

  Definition pow (A : term sorts) := A → sort *.

  Lemma Rename_pow : forall A ρ,
      Rename ρ (pow A) = pow (Rename ρ A).
  Proof.
    intros A ρ; reflexivity.
  Qed.
  
  Notation "'⊥'" := (∏ sort * `, ident 0) (at level 0, no associativity) : term_scope.
  Notation "'¬' A" := (A → ⊥) (at level 41) : term_scope.
  
  Lemma Rename_false : forall ρ, Rename ρ ⊥ = ⊥.
  Proof.
    intro ρ; reflexivity.
  Qed.

  Lemma Rename_neg : forall ρ A, Rename ρ (¬ A) = ¬ Rename ρ A.
  Proof.
    intros ρ A; reflexivity.
  Qed.
  
  Definition U :=
    ∏ sort ◻ `, (pow (pow (ident 0)) → ident 0) → (pow (pow (ident 0))).

  Lemma Rename_U : forall ρ,
      Rename ρ U = U.
  Proof.
    intro ρ; reflexivity.
  Qed.
  
  Local Hint Constructors U_axiom : core.
  Local Hint Constructors U_rule : core.
  Local Hint Constructors judge : core.
  Local Hint Resolve judge_abs_pi : core.
  Local Hint Resolve judge_app_arrow : core.
  Local Hint Unfold axiom : core.
  Local Hint Unfold rule : core.
  Local Hint Unfold pow : core.
  Local Hint Rewrite map_cons : core.
  Local Hint Rewrite (@Rename_arrow sorts) : core.
  Local Hint Resolve U_rule_star : core.

  Lemma pow_judge : forall Γ A,
      Γ ⊢ A ∈ sort ◻ -> Γ ⊢ pow A ∈ sort ◻.
  Proof.
    intros Γ A h;
      econstructor; try eassumption; eauto;
      autorewrite with core; cbn; auto.
  Qed.

  Lemma false_judge : forall Γ, Γ ⊢ ⊥ ∈ sort *.
  Proof.
    intro Γ; eapply judge_pi with (s₁ := ◻); eauto.
  Qed.
  
  Local Hint Resolve false_judge : core.

  Lemma neg_judge : forall Γ A s, Γ ⊢ A ∈ sort s -> Γ ⊢ ¬ A ∈ sort *.
  Proof.
    intros Γ A s h;
      eapply judge_pi with (s₁ := s); eauto.
  Qed.

  Local Hint Resolve neg_judge : core.
  Local Hint Resolve pow_judge : core.
  Arguments pow : simpl never.
  
  Lemma U_judge : forall Γ, Γ ⊢ U ∈ sort ◻.
  Proof.
    intros Γ; unfold U; simpl; unfold "$".
    eapply judge_pi with (s₁ := △) (s₂ := ◻);
      eauto; autorewrite with core.
    eapply judge_pi with (s₁ := ◻) (s₂ := ◻); eauto; simpl; unfold "$".
    - eapply judge_pi with (s₁ := ◻) (s₂ := ◻); cbn; unfold "$"; eauto.
    - do 2 (eapply judge_pi with (s₁ := ◻) (s₂ := ◻); cbv; eauto).
  Qed.

  Local Hint Resolve U_judge : core.
  
  Definition τ :=
    λ pow (pow U) ⇒
      λ sort ◻ ⇒
      λ (pow (pow (ident 0)) → ident 0) ⇒
      λ pow (ident 1) ⇒
      ident 3 ⋅ λ U ⇒ (ident 1 ⋅ (ident 2 ⋅ (ident 0 ⋅ ident 3 ⋅ ident 2))).
   
  Lemma Rename_τ : forall ρ, Rename ρ τ = τ.
  Proof.
    intros ρ; reflexivity.
  Qed.
  
  Arguments U : simpl never.
  Local Hint Rewrite Rename_pow : core.
  Local Hint Rewrite Rename_U : core.
  
  Lemma τ_judge : forall Γ, Γ ⊢ τ ∈ pow (pow U) → U.
  Proof.
    intro Γ; unfold τ.
    apply judge_abs_pi with (s := sort ◻); autorewrite with core.
    - apply judge_abs_pi with (s := sort ◻); auto.
      autorewrite with core. unfold Rename at 1.
      apply judge_abs_pi with (s := sort ◻); autorewrite with core; eauto.
      + unfold Rename at 1; unfold Rename at 2; unfold "$".
        apply judge_abs_pi with (s := sort ◻);
          autorewrite with core.
        * do 2 unfold Rename at 2; unfold "$".
          unfold Rename at 1; unfold "$".
          unfold Rename at 2; unfold "$".
          unfold Rename at 3; unfold "$".
          unfold Rename at 2; unfold "$".
          unfold Rename at 6; unfold "$".
          eapply judge_app_arrow.
          -- constructor; reflexivity.
          -- apply judge_abs_pi with (s := sort ◻);
               autorewrite with core.
             ++ do 2 unfold Rename at 1; unfold "$".
                do 2 unfold Rename at 2; unfold "$".
                unfold Rename at 7; unfold "$".
                do 3 (eapply judge_app_arrow;
                      try (econstructor; reflexivity)).
                replace ((pow (pow (ident 3)) → ident 3) → (pow (pow (ident 3))))
                  with (((pow (pow (ident 0)) → ident 0) → (pow (pow (ident 0)))) [[ ident 3 ]])
                  by reflexivity.
                eapply judge_app; econstructor; reflexivity.
             ++ eapply judge_pi with (s₁ := ◻); eauto;
                  autorewrite with core; cbn; auto.
        * unfold Rename at 2 6. unfold "$".
          do 2 (eapply judge_pi with (s₁ := ◻); eauto;
                autorewrite with core; cbn; auto; unfold "$").
      + unfold Rename at 4; unfold "$".
        repeat (eapply judge_pi with (s₁ := ◻); eauto;
                autorewrite with core; try (cbn; auto; assumption)).
        cbn; constructor; reflexivity.
    - apply judge_pi with (s₁ := ◻) (s₂ := ◻); auto.
  Qed.

  Definition σ := λ U ⇒ ident 0 ⋅ U ⋅ τ.

  Lemma Rename_σ : forall ρ, Rename ρ σ = σ.
  Proof.
    intro ρ; reflexivity.
  Qed.
  
  Arguments τ : simpl never.
  Local Hint Resolve τ_judge : core.

  Lemma σ_judge : forall Γ, Γ ⊢ σ ∈ U → pow (pow U).
  Proof.
    intro Γ; unfold σ.
    apply judge_abs_pi with (s := sort ◻); auto;
      autorewrite with core.
    eapply judge_app_arrow; eauto.
    - replace ((pow (pow U) → U) → pow (pow U)) with
        (((pow (pow (ident 0)) → ident 0) → pow (pow (ident 0))) [[ U ]])
        by reflexivity.
      econstructor; eauto.
      constructor; reflexivity.
    - eapply judge_pi with (s₁ := ◻); eauto;
        autorewrite with core; try (cbn; auto; assumption).
  Qed.

  Definition Δ :=
    λ U ⇒ ¬ (∏ pow U `, σ ⋅ ident 1 ⋅ ident 0 → ident 0 ⋅ (τ ⋅ (σ ⋅ ident 1))).

  Lemma Rename_Δ : forall ρ, Rename ρ Δ = Δ.
  Proof.
    intro ρ; reflexivity.
  Qed.

  Arguments σ : simpl never.
  Local Hint Resolve σ_judge : core.

  Lemma Δ_judge : forall Γ, Γ ⊢ Δ ∈ pow U.
  Proof.
    intro Γ; unfold Δ.
    apply judge_abs_pi with (s := sort ◻);
      autorewrite with core.
    - unfold Rename at 4.
      eapply neg_judge.
      do 2 (econstructor; eauto; autorewrite with core).
      + eapply judge_app_arrow.
        * eapply judge_app_arrow; eauto.
          -- apply σ_judge.
          -- constructor; reflexivity.
        * constructor; reflexivity.
      + cbn; unfold "$".
        eapply judge_app_arrow; eauto.
        constructor; reflexivity.
    - eapply judge_pi with (s₁ := ◻); eauto;
        autorewrite with core; cbn; auto.
  Qed.

  Definition Ω :=
    τ ⋅ λ pow U ⇒ ∏ U `, σ ⋅ ident 0 ⋅ ident 1 → ident 1 ⋅ ident 0.

  Lemma Rename_Ω : forall ρ, Rename ρ Ω = Ω.
  Proof.
    intro ρ; reflexivity.
  Qed.

  Lemma Ω_judge : forall Γ, Γ ⊢ Ω ∈ U.
  Proof.
    intro Γ; unfold Ω.
    eapply judge_app_arrow; eauto.
    eapply judge_abs_pi; eauto; autorewrite with core.
    - cbn; econstructor; eauto; unfold "$";
        autorewrite with core.
      econstructor; eauto; autorewrite with core.
      + eapply judge_app_arrow.
        * eapply judge_app_arrow.
          -- apply σ_judge.
          -- constructor; reflexivity.
        * constructor; reflexivity.
      + eapply judge_app_arrow; autorewrite with core;
          constructor; reflexivity.
    - eapply judge_pi with (s₁ := ◻) (s₃ := ◻); eauto;
        autorewrite with core; cbn; auto.
  Qed.
  
  Arguments Δ : simpl never.
  Arguments Ω : simpl never.

  Definition bad :=
    λ (∏ pow U `, ∏ U `, (σ ⋅ ident 1 ⋅ ident 0 → ident 1 ⋅ ident 0) → ident 1 ⋅ Ω) ⇒
      ((ident 0 ⋅ Δ ⋅
              λ U ⇒ λ σ ⋅ ident 0 ⋅ Δ ⇒
              λ (∏ pow U `, σ ⋅ ident 2 ⋅ ident 0 → ident 0 ⋅ (τ ⋅ (σ ⋅ ident 2))) ⇒
              ident 0 ⋅ Δ ⋅ ident 1 ⋅ λ pow U ⇒ ident 0 ⋅ λ U ⇒ ident 1 ⋅ (τ ⋅ (σ ⋅ ident 0)))
         ⋅ λ pow U ⇒ ident 1 ⋅ λ U ⇒ ident 1 ⋅ (τ ⋅ (σ ⋅ ident 0)))
      ⋅ λ pow U ⇒ λ (∏ U `, σ ⋅ ident 0 ⋅ ident 1 → ident 1 ⋅ ident 0) ⇒
      ident 0 ⋅ Ω ⋅ λ U ⇒ ident 1 ⋅ (τ ⋅ (σ ⋅ ident 0)).

  Lemma bad_judge : forall Γ, Γ ⊢ bad ∈ ⊥.
  Proof.
    intro Γ; unfold bad.
    Fail apply judge_abs_pi.
    (* How does [bad] have type [⊥]?
       Makes no sense... *)
  Abort.
End SystemU.

Definition leibniz {A : Set} (x y : A) : Prop := forall P : A -> Prop, P x <-> P y.

Lemma eq_leibniz : forall {A : Set} (a : A), leibniz a a.
Proof.
  firstorder.
Qed.

Lemma leibniz_eq : forall {A : Set} (x y : A), leibniz x y -> x = y.
Proof.
  unfold leibniz.
  intros A x y h.
  specialize h with (eq x).
  destruct h as [h _]; auto.
Qed.
