Require Export Lambda.PTS.Syntax Coq.Classes.RelationClasses Setoid.

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

Reserved Notation "x '⟶' y" (no associativity, at level 80).

Inductive br {S : Set} : term S -> term S -> Prop :=
| br_sub A B C :
  (λ A ⇒ B) ⋅ C ⟶ B [[ C ]]
| br_app_l A A' B :
  A ⟶ A' ->
  A ⋅ B ⟶ A' ⋅ B
| br_app_r A B B' :
  B ⟶ B' ->
  A ⋅ B ⟶ A ⋅ B'
| br_abs_l A A' B :
  A ⟶ A' ->
  λ A ⇒ B ⟶ λ A' ⇒ B
| br_abs_r A B B' :
  B ⟶ B' ->
  λ A ⇒ B ⟶ λ A ⇒ B'
| br_pi_l A A' B :
  A ⟶ A' ->
  ∏ A `, B ⟶ ∏ A' `, B
| br_pi_r A B B' :
  B ⟶ B' ->
  ∏ A `, B ⟶ ∏ A `, B'
where "x '⟶' y" := (br x y) : type_scope.

(** Reflexive-transitive closure. *)
Reserved Notation "A '⟶*' B" (at level 80, no associativity).

Inductive br_rt {sorts : Set} : term sorts -> term sorts -> Prop :=
| br_rt_refl A :
  A ⟶* A
| br_rt_trans A B C :
  A ⟶ B -> B ⟶* C -> A ⟶* C
where "A '⟶*' B" := (br_rt A B) : type_scope.

(** Reflexive-symmetric-transitive closure. *)
Reserved Notation "A '=β' B" (at level 80, no associativity).

Inductive br_rst {sorts : Set} : term sorts -> term sorts -> Prop :=
| br_br A B :
  A ⟶ B -> A =β B
| br_refl A :
  A =β A
| br_sym A B :
  A =β B -> B =β A
| br_trans A B C :
  A =β B -> B =β C -> A =β C
where "A '=β' B" := (br_rst A B) : type_scope.

Section Congruence.
  Local Hint Constructors br : core.
  Local Hint Constructors br_rt : core.
  Local Hint Constructors br_rst : core.

  Context {sorts : Set}.
  
  Lemma br_br_rt : forall A B : term sorts, A ⟶ B -> A ⟶* B.
  Proof.
    intros A B h; eauto.
  Qed.

  Lemma br_rt_transitve : forall A B C : term sorts,
      A ⟶* B -> B ⟶* C -> A ⟶* C.
  Proof.
    intros A B C hab; generalize dependent C;
      induction hab; intros C' hbc; auto.
    eapply br_rt_trans; eauto.
  Qed.

  Lemma br_rt_app_cong_l : forall A B C : term sorts,
      A ⟶* B -> A ⋅ C ⟶* B ⋅ C.
  Proof.
    intros A B C h; generalize dependent C;
      induction h; eauto.
  Qed.

  Lemma br_rt_app_cong_r : forall A B C : term sorts,
      B ⟶* C -> A ⋅ B ⟶* A ⋅ C.
  Proof.
    intros A B C h; generalize dependent A;
      induction h; eauto.
  Qed.

  Local Hint Resolve br_rt_transitve : core.
  Local Hint Resolve br_rt_app_cong_l : core.
  Local Hint Resolve br_rt_app_cong_r : core.
  
  Lemma br_rt_app_cong : forall A B C D : term sorts,
      A ⟶* B -> C ⟶* D -> A ⋅ C ⟶* B ⋅ D.
  Proof. eauto. Qed.

  Lemma br_rt_abs_cong_l : forall A B C : term sorts,
      A ⟶* B -> λ A ⇒ C ⟶* λ B ⇒ C.
  Proof.
    intros A B C h; generalize dependent C; induction h; eauto.
  Qed.

  Lemma br_rt_abs_cong_r : forall A B C : term sorts,
      B ⟶* C -> λ A ⇒ B ⟶* λ A ⇒ C.
  Proof.
    intros A B C h; generalize dependent A; induction h; eauto.
  Qed.

  Local Hint Resolve br_rt_abs_cong_l : core.
  Local Hint Resolve br_rt_abs_cong_r : core.
  
  Lemma br_rt_abs_cong : forall A B C D : term sorts,
      A ⟶* B -> C ⟶* D -> λ A ⇒ C ⟶* λ B ⇒ D.
  Proof. eauto. Qed.

  Lemma br_rt_pi_cong_l : forall A B C : term sorts,
      A ⟶* B -> ∏ A `, C ⟶* ∏ B `, C.
  Proof.
    intros A B C h; generalize dependent C; induction h; eauto.
  Qed.

  Lemma br_rt_pi_cong_r : forall A B C : term sorts,
      B ⟶* C -> ∏ A `, B ⟶* ∏ A `, C.
  Proof.
    intros A B C h; generalize dependent A; induction h; eauto.
  Qed.

  Local Hint Resolve br_rt_pi_cong_l : core.
  Local Hint Resolve br_rt_pi_cong_r : core.
  
  Lemma br_rt_pi_cong : forall A B C D : term sorts,
      A ⟶* B -> C ⟶* D -> ∏ A `, C ⟶* ∏ B `, D.
  Proof. eauto. Qed.

  Lemma br_rt_rst : forall A B : term sorts,
      A ⟶* B -> A =β B.
  Proof.
    intros A B h; induction h; eauto.
  Qed.
  
  Lemma br_rst_app_cong_l : forall A₁ A₂ B : term sorts,
      A₁ =β A₂ -> A₁ ⋅ B =β A₂ ⋅ B.
  Proof.
    intros A₁ A₂ B h; generalize dependent B;
      induction h; eauto.
  Qed.

  Lemma br_rst_app_cong_r : forall A B₁ B₂ : term sorts,
      B₁ =β B₂ -> A ⋅ B₁ =β A ⋅ B₂.
  Proof.
    intros A B₁ B₂ h; generalize dependent A;
      induction h; eauto.
  Qed.

  Local Hint Resolve br_rst_app_cong_l : core.
  Local Hint Resolve br_rst_app_cong_r : core.
  
  Lemma br_rst_app_cong : forall A₁ A₂ B₁ B₂ : term sorts,
      A₁ =β A₂ -> B₁ =β B₂ -> A₁ ⋅ B₁ =β A₂ ⋅ B₂.
  Proof. eauto. Qed.

  Lemma br_rst_abs_cong_l : forall A B C : term sorts,
      A =β B -> λ A ⇒ C =β λ B ⇒ C.
  Proof.
    intros A B C h; generalize dependent C; induction h; eauto.
  Qed.

  Lemma br_rst_abs_cong_r : forall A B C : term sorts,
      B =β C -> λ A ⇒ B =β λ A ⇒ C.
  Proof.
    intros A B C h; generalize dependent A; induction h; eauto.
  Qed.

  Local Hint Resolve br_rst_abs_cong_l : core.
  Local Hint Resolve br_rst_abs_cong_r : core.
  
  Lemma br_rst_abs_cong : forall A B C D : term sorts,
      A =β B -> C =β D -> λ A ⇒ C =β λ B ⇒ D.
  Proof. eauto. Qed.

  Lemma br_rst_pi_cong_l : forall A B C : term sorts,
      A =β B -> ∏ A `, C =β ∏ B `, C.
  Proof.
    intros A B C h; generalize dependent C; induction h; eauto.
  Qed.

  Lemma br_rst_pi_cong_r : forall A B C : term sorts,
      B =β C -> ∏ A `, B =β ∏ A `, C.
  Proof.
    intros A B C h; generalize dependent A; induction h; eauto.
  Qed.

  Local Hint Resolve br_rst_pi_cong_l : core.
  Local Hint Resolve br_rst_pi_cong_r : core.
  
  Lemma br_rst_pi_cong : forall A B C D : term sorts,
      A =β B -> C =β D -> ∏ A `, C =β ∏ B `, D.
  Proof. eauto. Qed.

  Lemma br_rst_reflexive : Reflexive (@br_rst sorts).
  Proof. auto. Qed.

  Lemma br_rst_symmetric : Symmetric (@br_rst sorts).
  Proof. auto. Qed.

  Lemma br_rst_transitive : Transitive (@br_rst sorts).
  Proof. eauto. Qed.
End Congruence.

Add Parametric Relation sorts
  : (term sorts)
      (@br_rst sorts)
    reflexivity proved by br_rst_reflexive
    symmetry proved by br_rst_symmetric
    transitivity proved by br_rst_transitive as br_rst_eq.

Add Parametric Morphism sorts : (@app sorts)
    with signature @br_rst sorts ==>  @br_rst sorts ==>  @br_rst sorts as app_mor.
Proof. auto using br_rst_app_cong. Qed.

Add Parametric Morphism sorts : (@abs sorts)
    with signature @br_rst sorts ==>  @br_rst sorts ==>  @br_rst sorts as abs_mor.
Proof. auto using br_rst_abs_cong. Qed.

Add Parametric Morphism sorts : (@pi sorts)
    with signature @br_rst sorts ==>  @br_rst sorts ==>  @br_rst sorts as pi_mor.
Proof. auto using br_rst_pi_cong. Qed.
