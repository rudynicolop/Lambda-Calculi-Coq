Require Export Lambda.PTS.Red.

Open Scope term_scope.

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

Reserved Notation "A '≡' B" (at level 80, no associativity).

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
  
  Lemma wh_br : forall A B : term sorts, A ⇝ B -> A ⟶ B.
  Proof.
    intros A B h; induction h; eauto.
  Qed.

  Local Hint Constructors br_rst : core.
  Local Hint Constructors wh_norm : core.
  Local Hint Resolve wh_br : core.

  Lemma wh_norm_br_rst : forall A B : term sorts, A ⇓ B -> A =β B.
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
