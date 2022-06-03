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

Variant not_lambda {S : Set} : term S -> Prop :=
  | not_lambda_sort s :
    not_lambda (sort s)
  | not_lambda_ident x :
    not_lambda (ident x)
  | not_lambda_app A B :
    not_lambda (A ⋅ B)
  | not_lambda_pi A B :
    not_lambda (∏ A `, B).
