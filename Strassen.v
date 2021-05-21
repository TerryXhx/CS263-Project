Require Import Psatz.
Require Import Setoid.
Require Import Arith.
Require Import Bool.
Require Import Program.
Require Import ZSum.
Require Export Coq.ZArith.ZArith.
Require Import Matrix.

Inductive StrassenMult {n : nat} : Square n -> Square n -> Square n -> Prop :=
  | SM_1 : forall (A B C : Square n), 
      n = 1 -> (A 0 0) * (B 0 0) = (C 0 0) ->
      StrassenMult A B C.
  | SM_n : forall (A B C : Square 2 * n), 
                  (A11 A12 A21 A22 B11 B12 B21 B22 C11 C12 C21 C22
                  S1 S2 S3 S4 S5 S6 S7 S8 S9 S10
                  P1 P2 P3 P4 P5 P6 P7 : Square n),
      A11 = subMat A 0 0 ->
      A12 = subMat A 0 n/2 ->
      A21 = subMat A n/2 0 -> 
      A22 = subMat A n/2 n/2 ->
      B11 = subMat B 0 0 ->
      B12 = subMat B 0 n/2 ->
      B21 = subMat B n/2 0 -> 
      B22 = subMat B n/2 n/2 ->
      C11 = subMat C 0 0 ->
      C12 = subMat C 0 n/2 ->
      C21 = subMat C n/2 0 -> 
      C22 = subMat C n/2 n/2 ->
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
      StrassenMult A11 S1 P1 ->
      StrassenMult S2 B22 P2 ->
      StrassenMult S3 B11 P3 ->
      StrassenMult A22 S4 P4 ->
      StrassenMult S5 S6  P5 ->
      StrassenMult S7 S8  P6 ->
      StrassenMult S9 S10 P7 ->
      C11 = P5 + P4 - P2 + P6 ->
      C12 = P1 + P2 ->
      C21 = P3 + P4 ->
      C22 = P5 + P1 - P3 - P7 ->
      StrassenMult A B C.


Theorem StrassenCorrectness {n : nat} : 
  forall (A B C : Square n), StrassenMult A B C -> C = A * B.