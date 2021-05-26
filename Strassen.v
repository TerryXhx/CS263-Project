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
      Split n A A11 A12 A21 A22 ->
      Split n B B11 B12 B21 B22 ->
      Split n C C11 C12 C21 C22 ->
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
    Split n A A11 A12 A21 A22 ->
    Split n B B11 B12 B21 B22 ->
    Split n C C11 C12 C21 C22 ->
    C = A × B ->
    (C11 == A11 × B11 + A12 × B21) /\ 
    (C12 == A11 × B12 + A12 × B22) /\ 
    (C21 == A21 × B11 + A22 × B21) /\
    (C22 == A21 × B12 + A22 × B22).
Proof.
  intros n A B C A11 A12 A21 A22 B11 B12 B21 B22 C11 C12 C21 C22 H0 HA HB HC HMult.
  unfold Split in HA; destruct HA as [HA11 [HA12 [HA21 HA22]]].
  unfold Split in HB; destruct HB as [HB11 [HB12 [HB21 HB22]]].
  unfold Split in HC; destruct HC as [HC11 [HC12 [HC21 HC22]]].
  unfold SubMat in *.
  repeat try split; unfold Mmult, Mplus in *; intros i j Hi Hj.
  + rewrite HA11, HB11, HA12, HB21, HC11.
    rewrite HMult.     
    assert (
      forall y : nat,
        (y < n)%nat ->
        ((fun y : nat => (A (i + 0)%nat y * B y (j + 0)%nat)%Z) (y + n)%nat) = 
        ((fun y : nat => (A (i + 0)%nat (y + n)%nat * B (y + n)%nat (j + 0)%nat)%Z) y)). 
    {
      intros.
      lia.
    }
    pose proof (
      Zsum_eq_seg 
        (fun y : nat => (A (i + 0)%nat y * B y (j + 0)%nat)%Z) 
        n
        (fun y : nat => (A (i + 0)%nat (y + n)%nat * B (y + n)%nat (j + 0)%nat)%Z)
        H
    ).
    rewrite H1.
    simpl.
    assert ((i + 0)%nat = i). { lia. }
    assert ((j + 0)%nat = j). { lia. } 
    rewrite H2, H3. clear H2 H3.
    assert (
      Zsum (fun y : nat => A i y * B y j)%Z n = 
      Zsum (fun y : nat => A i (y + 0)%nat * B (y + 0)%nat j)%Z n
    ).
    {
      apply Zsum_eq.
      intros y ?.
      assert ((y + 0)%nat = y). { lia. }
      rewrite H3.
      reflexivity.
    }
    rewrite H2.
    reflexivity.
  + rewrite HA11, HA12, HB12, HB22, HC12.
    rewrite HMult.
    assert (
      forall y : nat,
        (y < n)%nat ->
        ((fun y : nat => (A (i + 0)%nat y * B y (j + n)%nat)%Z) (y + n)%nat) = 
        ((fun y : nat => (A (i + 0)%nat (y + n)%nat * B (y + n)%nat (j + n)%nat)%Z) y)). 
    {
      intros.
      lia.
    }
    pose proof (
      Zsum_eq_seg 
        (fun y : nat => (A (i + 0)%nat y * B y (j + n)%nat)%Z) 
        n
        (fun y : nat => (A (i + 0)%nat (y + n)%nat * B (y + n)%nat (j + n)%nat)%Z)
        H
    ).
    rewrite H1.
    simpl.
    assert ((i + 0)%nat = i). { lia. }
    rewrite H2. clear H2.
    assert (
      Zsum (fun y : nat => A i y * B y (j + n)%nat)%Z n = 
      Zsum (fun y : nat => A i (y + 0)%nat * B (y + 0)%nat (j + n)%nat)%Z n
    ).
    {
      apply Zsum_eq.
      intros y ?.
      assert ((y + 0)%nat = y). { lia. }
      rewrite H3.
      reflexivity.
    }
    rewrite H2.
    reflexivity.
  + rewrite HA21, HA22, HB11, HB21, HC21.
    rewrite HMult. 
    assert (
      forall y : nat,
        (y < n)%nat ->
        ((fun y : nat => (A (i + n)%nat y * B y (j + 0)%nat)%Z) (y + n)%nat) = 
        ((fun y : nat => (A (i + n)%nat (y + n)%nat * B (y + n)%nat (j + 0)%nat)%Z) y)). 
    {
      intros.
      lia.
    }
    pose proof (
      Zsum_eq_seg 
        (fun y : nat => (A (i + n)%nat y * B y (j + 0)%nat)%Z) 
        n
        (fun y : nat => (A (i + n)%nat (y + n)%nat * B (y + n)%nat (j + 0)%nat)%Z)
        H
    ).
    rewrite H1.
    simpl.
    assert ((j + 0)%nat = j). { lia. }
    rewrite H2. clear H2.
    assert (
      Zsum (fun y : nat => A (i + n)%nat y * B y j)%Z n = 
      Zsum (fun y : nat => A (i + n)%nat (y + 0)%nat * B (y + 0)%nat j)%Z n
    ).
    {
      apply Zsum_eq.
      intros y ?.
      assert ((y + 0)%nat = y). { lia. }
      rewrite H3.
      reflexivity.
    }
    rewrite H2.
    reflexivity.
  + rewrite HA21, HA22, HB12, HB22, HC22.
    rewrite HMult.
    assert (
      forall y : nat,
        (y < n)%nat ->
        ((fun y : nat => (A (i + n)%nat y * B y (j + n)%nat)%Z) (y + n)%nat) = 
        ((fun y : nat => (A (i + n)%nat (y + n)%nat * B (y + n)%nat (j + n)%nat)%Z) y)). 
    {
      intros.
      lia.
    }
    pose proof (
      Zsum_eq_seg 
        (fun y : nat => (A (i + n)%nat y * B y (j + n)%nat)%Z) 
        n
        (fun y : nat => (A (i + n)%nat (y + n)%nat * B (y + n)%nat (j + n)%nat)%Z)
        H
    ).
    rewrite H1.
    simpl.
    assert (
      Zsum (fun y : nat => A (i + n)%nat y * B y (j + n)%nat)%Z n = 
      Zsum (fun y : nat => A (i + n)%nat (y + 0)%nat * B (y + 0)%nat (j + n)%nat)%Z n
    ).
    {
      apply Zsum_eq.
      intros y ?.
      assert ((y + 0)%nat = y). { lia. }
      rewrite H3.
      reflexivity.
    }
    rewrite H2.
    reflexivity.
Qed.

Lemma BlockEquivCompat:
  forall (n : nat) (A B : Square (2 * n)) (A11 A12 A21 A22 B11 B12 B21 B22 : Square n),
    n <> Z.to_nat 0 ->
    Split n A A11 A12 A21 A22 ->
    Split n B B11 B12 B21 B22 ->
    A11 == B11 -> A12 == B12 -> A21 == B21 -> A22 == B22 -> 
    A == B.
Proof.
  intros n A B A11 A12 A21 A22 B11 B12 B21 B22 H0 HA HB Heq11 Heq12 Heq21 Heq22.
  intros i j Hi Hj.
  unfold Split in HA; destruct HA as [HA11 [HA12 [HA21 HA22]]].
  unfold Split in HB; destruct HB as [HB11 [HB12 [HB21 HB22]]].
  unfold SubMat in *.
  unfold mat_equiv in Heq11, Heq12, Heq21, Heq22.
  rewrite HA11, HB11 in Heq11.
  rewrite HA12, HB12 in Heq12.
  rewrite HA21, HB21 in Heq21.
  rewrite HA22, HB22 in Heq22.
  assert ((i < n)%nat \/ (n <= i < 2 * n)%nat). { lia. }
  assert ((j < n)%nat \/ (n <= j < 2 * n)%nat). { lia. }
  clear Hi Hj.
  destruct H; destruct H1. 
  + specialize (Heq11 i j H H1).
    assert ((i + 0)%nat = i). { lia. }
    assert ((j + 0)%nat = j). { lia. }
    rewrite H2, H3 in Heq11.
    exact Heq11.
  + assert (((j - n) < n)%nat). { lia. }
    specialize (Heq12 i (j - n)%nat H H2). 
    assert ((i + 0)%nat = i). { lia. }
    assert ((j - n + n)%nat = j). { lia. }
    rewrite H3, H4 in Heq12.
    exact Heq12.
  + assert ((i - n < n)%nat). { lia. }
    specialize (Heq21 (i - n)%nat j H2 H1).
    assert ((i - n + n)%nat = i). { lia. }
    assert ((j + 0)%nat = j). { lia. }
    rewrite H3, H4 in Heq21.
    exact Heq21.
  + assert ((i - n < n)%nat). { lia. }
    assert (((j - n) < n)%nat). { lia. }
    specialize (Heq22 (i - n)%nat (j - n)%nat H2 H3).
    assert ((i - n + n)%nat = i). { lia. }
    assert ((j - n + n)%nat = j). { lia. }
    rewrite H4, H5 in Heq22.
    exact Heq22.
Qed.

Theorem StrassenCorrectness:
  forall (n : nat) (A B C D : Square n), StrassenMult n A B C -> D = A × B -> C == D.
Proof.
Admitted.

(* Haoxuan Xu, Yichen Tao *)
(* 2021-05-26 09:41 *)