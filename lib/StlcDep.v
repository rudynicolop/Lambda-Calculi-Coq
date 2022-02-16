From Lambda Require Export Util Stlc.

(** * Dependently Typed Lambda Calculus. *)

(** Inspired by
    Programming Language Foundations in Agda. *)

(** List helpers. *)

Section List.
  Context {A : Set}.

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
End List.

(** De Bruijn syntax. *)

Reserved Notation "Γ '⊩' τ" (at level 80, no associativity).

Inductive term (Γ : list type) : type -> Set :=
| Id (n : nat) (τ : type) :
    nth_error Γ n = Some τ ->
    Γ ⊩ τ
| Abs (τ τ' : type) :
    τ :: Γ ⊩ τ' ->
    Γ ⊩ τ → τ'
| App (τ τ' : type) :
    Γ ⊩ τ → τ' ->
    Γ ⊩ τ ->
    Γ ⊩ τ'
where "Γ '⊩' τ" := (term Γ τ).

Local Hint Constructors term : core.

Definition term_of_id :
  forall {Γ : list type} (n : nat) {H : n < length Γ},
    Γ ⊩ lookup H := ltac:(eauto using nth_error_lookup).

Notation "'#' n"
  := (ltac:(refine (term_of_id n); cbn; lia))
       (at level 10, no associativity).

Example identity_func : [] ⊩ (⊥ → ⊥) := Abs _ _ _ (# 0).
