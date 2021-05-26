(* Reference: https://www.cs.umd.edu/~rrand/vqc/Matrix.html#Matrix *)

Require Import Psatz.
Require Import Setoid.
Require Import Arith.
Require Import Bool.
Require Import Program.
Require Import ZSum.
Require Export Coq.ZArith.ZArith.

Delimit Scope matrix_scope with M.
Open Scope matrix_scope.
Open Scope nat_scope.

(* We define a _matrix_ as a simple function from two nats
(corresponding to a row and a column) to a integer. *)
Definition Matrix (m n : nat) := nat -> nat -> Z.

Bind Scope matrix_scope with Matrix.
Notation Vector n := (Matrix n 1).
Notation Square n := (Matrix n n).

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop :=
  forall i j, i < m -> j < n -> A i j = B i j.

Infix "==" := mat_equiv (at level 80).

(* Some important notions about matrix equality. *)
Lemma mat_equiv_refl : forall {m n} (A : Matrix m n), A == A.
Proof.
  intros.
  unfold mat_equiv. 
  intros. 
  reflexivity.
Qed.

Lemma mat_equiv_sym : forall {m n} (A B : Matrix m n), A == B -> B == A.
Proof.
  unfold mat_equiv.
  intros.
  specialize (H i j H0 H1).
  rewrite H. 
  reflexivity.
Qed.

Lemma mat_equiv_trans : forall {m n} (A B C : Matrix m n),
    A == B -> B == C -> A == C.
Proof.
  unfold mat_equiv.
  intros.
  specialize (H i j H1 H2).
  specialize (H0 i j H1 H2).
  rewrite H, H0. 
  reflexivity.
Qed.

Add Parametric Relation m n : (Matrix m n) (@mat_equiv m n)
  reflexivity proved by mat_equiv_refl
  symmetry proved by mat_equiv_sym
  transitivity proved by mat_equiv_trans
    as mat_equiv_rel.

(* ################################################################# *)
(** * Basic Matrices and Operations *)

Close Scope nat_scope.
Open Scope Z_scope.

(** Because we will use these so often, it is good to have them in matrix scope. *)
Notation "m =? n" := (Nat.eqb m n) (at level 70) : matrix_scope.
Notation "m <? n" := (Nat.ltb m n) (at level 70) : matrix_scope.
Notation "m <=? n" := (Nat.leb m n) (at level 70) : matrix_scope.

Open Scope matrix_scope.

Definition I (n : nat) : Matrix n n := fun i j => if (i =? j)%nat then 1 else 0.

Definition Zero (m n : nat) : Matrix m n := fun _ _ => 0.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun i j => A i j + B i j.

Definition Mminus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun i j => A i j - B i j.

Infix "+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix "-" := Mminus (at level 50, left associativity) : matrix_scope.

Lemma Mplus_assoc : forall {m n} (A B C : Matrix m n), (A + B) + C == A + (B + C).
Proof.
  intros m n A B C i j Hi Hj.
  unfold Mplus.
  lia.
Qed.

Lemma Mplus_comm : forall {m n} (A B : Matrix m n), A + B == B + A.
Proof.
  intros m n A B i j Hi Hj.
  unfold Mplus.
  lia.
Qed.

Lemma Mplus_0_l : forall {m n} (A : Matrix m n), Zero m n + A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Zero, Mplus.
  lia.
Qed.

Lemma Mplus_0_r : forall {m n} (A : Matrix m n), A + Zero m n == A.
Proof.
  intros m n A.
  rewrite Mplus_comm.
  apply Mplus_0_l.
Qed.

Lemma Mplus_compat : forall {m n} (A B A' B' : Matrix m n),
  A == A' -> B == B' -> A + B == A' + B'.
Proof.
  intros m n A B A' B' HA HB.
  intros i j Hi Hj.
  unfold Mplus.
  rewrite HA, HB; tauto.
Qed.

Add Parametric Morphism m n : (@Mplus m n)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mplus_mor.
Proof.
  intros A A' HA B B' HB.
  apply Mplus_compat; tauto.
Qed.

Lemma Mminus_compat : forall {m n} (A B A' B' : Matrix m n),
  A == A' -> B == B' -> A - B == A' - B'.
Proof.
  intros m n A B A' B' HA HB.
  intros i j Hi Hj.
  unfold Mminus.
  rewrite HA, HB; tauto.
Qed.

Add Parametric Morphism m n : (@Mminus m n)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mminus_mor.
Proof.
  intros A A' HA B B' HB.
  apply Mminus_compat; tauto.
Qed.

Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o :=
  fun x z => Zsum (fun y => A x y * B y z)%Z n.

Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.

Lemma Mmult_compat : forall {m n o} (A A' : Matrix m n) (B B' : Matrix n o),
    A == A' -> B == B' -> A × B == A' × B'.
Proof.
  intros m n o A A' B B' HA HB i j Hi Hj.
  unfold Mmult.
  apply Zsum_eq; intros x Hx.
  rewrite HA, HB; tauto.
Qed.

Add Parametric Morphism m n o : (@Mmult m n o)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mmult_mor.
Proof. intros. apply Mmult_compat; easy. Qed.

Definition SubMat {m n} (A : Matrix m n) (rowl rowh coll colh : nat) : Matrix (rowh - rowl)%nat (colh - coll)%nat :=
  fun i j => A (i + rowl)%nat (j + coll)%nat.

Definition Split(n : nat) (A : Square (2 * n)) (A11 A12 A21 A22 : Square n): Prop :=
  A11 = SubMat A 0 n 0 n  /\
  A12 = SubMat A 0 n n (2 * n) /\
  A21 = SubMat A n (2 * n) 0 n /\ 
  A22 = SubMat A n (2 * n) n (2 * n)
.

Lemma Splitable(n : nat) (A : Square (2 * n)): 
  n <> Z.to_nat 0 ->
  exists (A11 A12 A21 A22 : Square n), Split n A A11 A12 A21 A22.
Proof.
  intros.
  exists 
    (SubMat A 0 n 0 n),
    (SubMat A 0 n n (2 * n)), 
    (SubMat A n (2 * n) 0 n), 
    (SubMat A n (2 * n) n (2 * n))
  .
  unfold Split.
  tauto.
Qed.

(* ################################################################# *)
(** * Matrix Properties *)

Theorem Mmult_assoc : forall {m n o p : nat} (A : Matrix m n) (B : Matrix n o) 
  (C: Matrix o p), A × B × C == A × (B × C).
Proof.
  intros m n o p A B C i j Hi Hj.
  unfold Mmult.
  induction n.
  + simpl.
    clear B.
    induction o. reflexivity.
    simpl. rewrite IHo.
    - lia.
    - tauto. 
  + simpl. 
    rewrite <- IHn.
    simpl.
    rewrite Zsum_mult_l.
    rewrite <- Zsum_plus.
    apply Zsum_eq; intros.
    rewrite Zmult_plus_dist_r.
    rewrite Zmult_assoc.
    reflexivity.
Qed.

                                                   
(* ################################################################# *)
(** * Matrix Library *)

Lemma Mmult_plus_dist_l : forall {m n o : nat} (A : Matrix m n) (B C : Matrix n o), 
                           A × (B + C) == A × B + A × C.
Proof. 
  intros. intros i j _ _.
  unfold Mplus, Mmult.
  rewrite <- Zsum_plus.
  apply Zsum_eq_bounded; intros.
  rewrite Zmult_plus_dist_l. 
  reflexivity.
Qed.

Lemma Mmult_plus_dist_r : forall {m n o : nat} (A B : Matrix m n) (C : Matrix n o), 
                           (A + B) × C == A × C + B × C.
Proof. 
  intros. intros i j _ _.
  unfold Mplus, Mmult.
  rewrite <- Zsum_plus.
  apply Zsum_eq_bounded; intros.
  rewrite Zmult_plus_dist_r. 
  reflexivity.
Qed.

Lemma Mmult_plus_dist : forall {m n o : nat} (A B : Matrix m n) (C D : Matrix n o), 
                           (A + B) × (C + D) == A × C + A × D + B × C + B × D.
Proof. 
  intros.
  pose proof (Mmult_plus_dist_l (A + B) C D).
  rewrite H.
  pose proof (Mmult_plus_dist_r A B C).
  pose proof (Mmult_plus_dist_r A B D).
  rewrite H0, H1.
  intros i j _ _.
  unfold Mplus.
  lia.
Qed.

Lemma Mmult_minus_dist_l : forall {m n o : nat} (A : Matrix m n) (B C : Matrix n o), 
                           A × (B - C) == A × B - A × C.
Proof. 
  intros. intros i j _ _.
  unfold Mminus, Mmult.
  rewrite <- Zsum_minus.
  apply Zsum_eq_bounded; intros.
  rewrite Zmult_minus_dist_l. 
  reflexivity.
Qed.

Lemma Mmult_minus_dist_r : forall {m n o : nat} (A B : Matrix m n) (C : Matrix n o), 
                           (A - B) × C == A × C - B × C.
Proof. 
  intros. intros i j _ _.
  unfold Mminus, Mmult.
  rewrite <- Zsum_minus.
  apply Zsum_eq_bounded; intros.
  rewrite Zmult_minus_dist_r. 
  reflexivity.
Qed.

Lemma Mmult_minus_dist : forall {m n o : nat} (A B : Matrix m n) (C D : Matrix n o), 
                           (A - B) × (C - D) == A × C - A × D - B × C + B × D.
Proof. 
  intros.
  pose proof (Mmult_minus_dist_l (A - B) C D).
  rewrite H.
  pose proof (Mmult_minus_dist_r A B C).
  pose proof (Mmult_minus_dist_r A B D).
  rewrite H0, H1.
  intros i j _ _.
  unfold Mplus, Mminus.
  lia.
Qed.

Lemma Mmult_minus_plus_dist : forall {m n o : nat} (A B : Matrix m n) (C D : Matrix n o), 
                           (A - B) × (C + D) == A × C + A × D - B × C - B × D.
Proof. 
  intros.
  pose proof (Mmult_plus_dist_l (A - B) C D).
  rewrite H.
  pose proof (Mmult_minus_dist_r A B C).
  pose proof (Mmult_minus_dist_r A B D).
  rewrite H0, H1.
  intros i j _ _.
  unfold Mplus, Mminus.
  lia.
Qed.

Lemma Mmult_plus_minus_dist : forall {m n o : nat} (A B : Matrix m n) (C D : Matrix n o), 
                           (A + B) × (C - D) == A × C - A × D + B × C - B × D.
Proof. 
  intros.
  pose proof (Mmult_minus_dist_l (A + B) C D).
  rewrite H.
  pose proof (Mmult_plus_dist_r A B C).
  pose proof (Mmult_plus_dist_r A B D).
  rewrite H0, H1.
  intros i j _ _.
  unfold Mplus, Mminus.
  lia.
Qed.

(* Haoxuan Xu, Yichen Tao *)
(* 2021-05-26 14:34 *)