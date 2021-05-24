Require Import Psatz.
Require Import Setoid.
Require Import Arith.
Require Import Bool.
Require Import Program.
Require Import ZSum.
Require Export Coq.ZArith.ZArith.
Require Import Matrix.

Open Scope matrix_scope.

Search (Z -> nat). (* Z.to_nat *)
Search (nat -> Z). (* Z.of_nat *)

Inductive StrassenMult: 
  forall n : nat, Square n -> Square n -> Square n -> Prop :=
  | SM_1 : forall (n : nat) (A B C : Square n), 
      n = Z.to_nat 1 -> C = A × B ->
      StrassenMult n A B C
  | SM_n : forall (n: nat)
                  (A B C : Square (2 * n))
                  (A11 A12 A21 A22 B11 B12 B21 B22 C11 C12 C21 C22
                  S1 S2 S3 S4 S5 S6 S7 S8 S9 S10
                  P1 P2 P3 P4 P5 P6 P7 : Square n),
      n <> Z.to_nat 0 ->
      Split A A11 A12 A21 A22 ->
      Split B B11 B12 B21 B22 ->
      Split C C11 C12 C21 C22 ->
      S1 = B12 - B22 ->
      S2 = A11 + A12 ->
      S3 = A21 + A22 -> 
      S4 = B21 - B11 ->
      S5 = A11 + A22 ->
      S6 = B11 + B22 ->
      S7 = A12 - A22 ->
      S8 = B21 + B22 ->
      S9 = A11 - A21 -> 
      S10 = B11 + B12 ->
      StrassenMult n A11 S1 P1 ->
      StrassenMult n S2 B22 P2 ->
      StrassenMult n S3 B11 P3 ->
      StrassenMult n A22 S4 P4 ->
      StrassenMult n S5 S6  P5 ->
      StrassenMult n S7 S8  P6 ->
      StrassenMult n S9 S10 P7 ->
      C11 = P5 + P4 - P2 + P6 ->
      C12 = P1 + P2 ->
      C21 = P3 + P4 ->
      C22 = P5 + P1 - P3 - P7 ->
      StrassenMult (2 * n) A B C.

Lemma MatMultBlockRes:
  forall (n : nat) (A B C : Square (2 * n)) (A11 A12 A21 A22 B11 B12 B21 B22 C11 C12 C21 C22: Square n),
    n <> Z.to_nat 0 ->
    Split A A11 A12 A21 A22 ->
    Split B B11 B12 B21 B22 ->
    Split C C11 C12 C21 C22 ->
    C = A × B ->
    (C11 = A11 × B11 + A12 × B21) /\ 
    (C12 = A11 × B12 + A12 × B22) /\ 
    (C21 = A21 × B11 + A22 × B21) /\
    (C22 = A21 × B12 + A22 × B22).
Proof.
  Admitted.

Lemma BlockEquivCompat:
  forall (n : nat) (A B : Square (2 * n)) (A11 A12 A21 A22 B11 B12 B21 B22 : Square n),
    n <> Z.to_nat 0 ->
    Split A A11 A12 A21 A22 ->
    Split B B11 B12 B21 B22 ->
    A11 = B11 -> A12 = B12 -> A21 = B21 -> A22 = B22 -> 
    A = B.
Proof.
  Admitted.

Theorem StrassenCorrectness:
  forall (n : nat) (A B C D : Square n), StrassenMult n A B C -> D = A × B -> C = D.
Proof.
  Admitted.

(* Haoxuan Xu, Yichen Tao *)
(* 2021-05-24 15:01 *)