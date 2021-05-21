Require Import Psatz.
Require Import Setoid.
Require Import Arith.
Require Import Bool.
Require Import Program.
Require Import ZSum.
Require Export Coq.ZArith.ZArith.
Require Import Matrix.

Inductive StrassenMult (Matrix )

Fact Strassen_correctness: forall {n: nat} (st: state) (X Y: Square),
  (StrassenMult X Y) = (X * Y).