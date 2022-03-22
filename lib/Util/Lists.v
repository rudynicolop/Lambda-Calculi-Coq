Require Export Lambda.Util.Basic.
From Equations Require Export Equations.

(** * List helpers. *)

Section List.
  Context {A : Set}.

  Inductive Has : A -> list A -> Set :=
  | HasO : forall a t, Has a (a :: t)
  | HasS : forall a h t, Has a t -> Has a (h :: t).

  Global Arguments HasO {_} {_}.
  Global Arguments HasS {_} {_} {_}.

  Equations Derive NoConfusion NoConfusionHom Subterm for list.
  Equations Derive Signature NoConfusion for Has.
  (*Equations Derive NoConfusionHom for Has.*)
  (*Next Obligation.
  Proof.
    unfold NoConfusionHom_Has in H.
    unfold apply_noConfusion in H. cbn in H.
    unfold DepElim.solution_left,DepElim.solution_right in H.
    unfold DepElim.eq_simplification_sigma1,Logic.transport in H.
    repeat unfold noConfusionHom_list_obligation_2,
      noConfusionHom_list_obligation_4,
      noConfusionHom_list_obligation_1,
      NoConfusionHom_list,eq_sym in H. cbn in H.
    depind a0; cbn in *; depelim b; cbn in *.
    - unfold DepElim.pack_sigma_eq_nondep in *.
      Search (eq_rect (_ :: _) _ _ (_ :: _) _).
      rewrite f_equal_dep in H.
      Print Assumptions Eqdep.EqdepTheory.eq_rect_eq.
      depelim e'; cbn in *. inv H.
      depelim e'0; cbn in *.
    - admit.
    - admit.
    - f_equal.*)

  Equations ext_has : forall {Γ Δ},
      (forall a : A, Has a Γ -> Has a Δ) ->
      forall b a : A, Has a (b :: Γ) -> Has a (b :: Δ) :=
    ext_has ρ _ _ HasO := HasO;
    ext_has ρ _ _ (HasS h) := HasS (ρ _ h).

  Equations ext_has_app_l : forall {Γ Δ},
      (forall a : A, Has a Γ -> Has a Δ) ->
      forall (l : list A) (a : A), Has a (l ++ Γ) -> Has a (l ++ Δ) :=
    ext_has_app_l ρ []:= ρ;
    ext_has_app_l ρ (h :: t) := ext_has (ext_has_app_l ρ t) h.
  
  Definition Has_nth_error : forall {Γ a},
      Has a Γ -> { n | nth_error Γ n = Some a}.
  Proof.
    intros l a h; induction h.
    - refine (exist _ 0 _); reflexivity.
    - destruct IHh as [k Hk].
      refine (exist _ (S k) _); assumption.
  Defined.
  
  Variant zilch : list A -> Prop := zilch_nil : zilch [].
  
  Definition lookup :
    forall {Γ : list A} {n : nat},
      n < length Γ -> A.
  Proof.
    refine
      (fix F Γ n HnΓ :=
         match Γ as Γ' return Γ = Γ' -> A with
         | []
           => fun HΓΓ' => _
         | a :: Δ
         => fun HΓΓ' =>
             match n as n' return n = n' -> A with
             | O   => fun _ => a
             | S k => fun Hnn' => F Δ k _
             end eq_refl
         end eq_refl).
    - inv HΓΓ'; cbn in *; lia.
    - subst; cbn in *; lia.
  Defined.
  
  (* Require Import Extraction.
     Recursive Extraction lookup. *)

  Definition length_nth_error' :
    forall {l : list A} {n : nat},
      n < length l -> { a | nth_error l n = Some a }.
  Proof.
    refine
    (fix F l n Hnl :=
       match
         l as l'
         return
         l = l' -> { a | nth_error l n = Some a } with
       | [] => fun H => _
       | h :: t
         => fun H =>
             match
               n as n'
               return
               n = n' -> { a | nth_error l n = Some a } with
             | O
               => fun _ => @exist _ _ h _
             | S k
               => fun Hnn' =>
                   match F t k _ with
                   | exist _ a' Hk => @exist _ _ a' _
                   end
             end eq_refl
       end eq_refl); subst; cbn in *;
      lia || reflexivity || assumption.
  Defined.

  Definition nth_error_lookup :
    forall {Γ : list A} {n : nat} (H : n < length Γ),
      nth_error Γ n = Some (lookup H).
  Proof.
    intro l; induction l as [| a l IHl];
      intros [| n] H; cbn in *;
        try lia; eauto using Lt.lt_S_n.
  Defined.

  Local Hint Constructors Has : core.
  
  Definition nth_error_Has : forall {Γ a n},
      nth_error Γ n = Some a -> Has a Γ.
  Proof.
    intro l; induction l as [| h t IHt];
      intros a [| n] Hnth; cbn in *; try discriminate; eauto.
    inv Hnth; auto.
  Defined.

  Definition nth_error_Has' : forall {Γ a},
      {n | nth_error Γ n = Some a} -> Has a Γ.
  Proof.
    intros l a [n H]; exact (nth_error_Has H).
  Defined.
  
  Definition ext_nth_error : forall {Γ Δ : list A},
      (forall a, {n | nth_error Γ n = Some a} ->
              {k | nth_error Δ k = Some a}) ->
      forall b a, {n | nth_error (b :: Γ) n = Some a} ->
               {k | nth_error (b :: Δ) k = Some a}.
  Proof.
    intros l d f b a Hab.
    apply Has_nth_error.
    apply nth_error_Has' in Hab.
    pose proof (fun a H => nth_error_Has' (f a (Has_nth_error H))) as H.
    eauto using ext_has.
  Defined.
End List.

Equations has_map :
  forall {A B : Set} (f : A -> B) {l : list A} {e : A},
    Has e l -> Has (f e) (map f l) :=
  has_map f  HasO     := HasO;
  has_map f (HasS hs) := HasS (has_map f hs).

Definition map_has : forall (A B : Set) (f : A -> B) (l : list A) b,
    Has b (map f l) -> {a : A & f a = b & Has a l}.
Proof.
  intros A B f l.
  induction l as [| a l ih]; intros b h; cbn in *; depelim h.
  - exact (existT2 _ _ a eq_refl HasO).
  - apply ih in h0 as [a' fab hasa].
    exact (existT2 _ _ a' fab (HasS hasa)).
Defined.
