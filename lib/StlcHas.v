Require Export Lambda.SimpleTypes.
From Equations Require Import Equations.

(** Inspired by
    Programming Language Foundations in Agda. *)

(** De Bruijn syntax. *)

Reserved Notation "Γ '⊢' τ" (at level 80, no associativity).

Inductive term (Γ : list type) : type -> Set :=
| Id (τ : type) :
  Has τ Γ ->
  Γ ⊢ τ
| Abs (τ τ' : type) :
  τ :: Γ ⊢ τ' ->
  Γ ⊢ τ → τ'
| App (τ τ' : type) :
  Γ ⊢ τ → τ' ->
  Γ ⊢ τ ->
  Γ ⊢ τ'
where "Γ '⊢' τ" := (term Γ τ) : type_scope.

Derive Signature for term.
Equations Derive NoConfusion NoConfusionHom Subterm for term.
