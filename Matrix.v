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

Definition Mscale {m n : nat} (c : Z) (A : Matrix m n) : Matrix m n :=
  fun i j => c * A i j.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun i j => A i j + B i j.

Definition Mminus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun i j => A i j - B i j.

Infix "+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix "-" := Mminus (at level 50, left associativity) : matrix_scope.
Infix "*" := Mscale (at level 40, left associativity) : matrix_scope.

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

Lemma Mscale_compat : forall {m n} (c c' : Z) (A A' : Matrix m n),
  c = c' -> A == A' -> c * A == c' * A'.
Proof.
  intros m n c c' A A' Hc HA.
  intros i j Hi Hj.
  unfold Mscale.
  rewrite Hc, HA; tauto.
Qed.

Add Parametric Morphism m n : (@Mscale m n)
  with signature eq ==> mat_equiv ==> mat_equiv as Mscale_mor.
Proof.
  intros; apply Mscale_compat; tauto.
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

Inductive Split {n : nat} : Square (2 * n) -> Square n -> Square n -> Square n -> Square n -> Prop :=
  | SplitIntoFour : forall (A : Square (2 * n)) (A11 A12 A21 A22 : Square n),
      A11 = SubMat A 0 n 0 n  ->
      A12 = SubMat A 0 n n (2 * n) ->
      A21 = SubMat A n (2 * n) 0 n -> 
      A22 = SubMat A n (2 * n) n (2 * n) ->
      Split A A11 A12 A21 A22.
      
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
(** * Matrix Automation *)

(** A useful tactic for solving A == B for concrete A, B *)
Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.
                
Ltac by_cell := 
  intros;
  let i := fresh "i" in 
  let j := fresh "j" in 
  let Hi := fresh "Hi" in 
  let Hj := fresh "Hj" in 
  intros i j Hi Hj; try solve_end;
  repeat (destruct i as [|i]; simpl; [|apply lt_S_n in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; [|apply lt_S_n in Hj]; try solve_end); clear Hj.

Ltac lma := by_cell; lia.
                                                   
(* ################################################################# *)
(** * Matrix Library *)

(* Lemma scale0_concrete : 0 * I 10 == Zero _ _.
Proof. lma. Qed.

Lemma Mscale_0_l : forall {m n : nat} (A : Matrix m n), 0 * A == Zero m n.
Proof. intros. lma. Qed.

Lemma Mscale_0_r : forall {m n : nat} (c : C), c * Zero m n == Zero m n.
Proof. intros. lma. Qed.

Lemma Mscale_1_l : forall {m n : nat} (A : Matrix m n), 1 * A == A.
Proof. intros. lma. Qed.

Lemma Mscale_1_r : forall {n : nat} (c : C),
    c * I n == fun x y => if (x =? y) then c else 0.
Proof.
  intros n c i j _ _.
  unfold I, Mscale; simpl. 
  destruct (i =? j); lca.
Qed.

Lemma Mscale_assoc : forall {m n : nat} (x y : C) (A : Matrix m n),
  x * (y * A) == (x * y)%C * A.
Proof. lma. Qed.

Lemma Mscale_plus_dist_l : forall {m n : nat} (x y : C) (A : Matrix m n),
  (x + y)%C * A == x * A + y * A.
Proof. lma. Qed.

Lemma Mscale_plus_dist_r : forall {m n : nat} (x : C) (A B : Matrix m n),
  x * (A + B) == x * A + x * B.
Proof. lma. Qed. *)

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

Lemma Mscale_mult_dist_l : forall {m n o : nat} (x : Z) (A : Matrix m n) (B : Matrix n o), 
    ((x * A) × B) == x * (A × B).
Proof. 
  intros. intros i j _ _.
  unfold Mscale, Mmult.
  rewrite Zsum_mult_l.
  apply Zsum_eq_bounded; intros.
  lia.
Qed.

Lemma Mscale_mult_dist_r : forall {m n o : nat} (x : Z) (A : Matrix m n) (B : Matrix n o),
    (A × (x * B)) == x * (A × B).
Proof.
  intros. intros i j _ _.
  unfold Mscale, Mmult.
  rewrite Zsum_mult_l.
  apply Zsum_eq_bounded; intros.
  lia.
Qed.

(*******************************)
(* Automation *)
(*******************************)

Lemma double_mult : forall (n : nat), (n + n = 2 * n)%nat. Proof. intros. lia. Qed.
Lemma pow_two_succ_l : forall x, (2^x * 2 = 2 ^ (x + 1))%nat.
Proof. intros. rewrite mult_comm. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma pow_two_succ_r : forall x, (2 * 2^x = 2 ^ (x + 1))%nat.
Proof. intros. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma double_pow : forall (n : nat), (2^n + 2^n = 2^(n+1))%nat. 
Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.
Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof. intuition. Qed.

Ltac unify_pows_two :=
  repeat match goal with
  (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
  | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat by reflexivity
  | [ |- context[ (0 + ?a)%nat]]            => rewrite plus_0_l 
  | [ |- context[ (?a + 0)%nat]]            => rewrite plus_0_r 
  | [ |- context[ (1 * ?a)%nat]]            => rewrite Nat.mul_1_l 
  | [ |- context[ (?a * 1)%nat]]            => rewrite Nat.mul_1_r 
  | [ |- context[ (2 * 2^?x)%nat]]          => rewrite <- Nat.pow_succ_r'
  | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
  | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
  | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite <- Nat.pow_add_r 
  | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite plus_assoc 
  | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; try lia 
  end.

(** Restoring Matrix dimensions *)
Ltac is_nat_equality :=
  match goal with 
  | |- ?A = ?B => match type of A with
                | nat => idtac
                end
  end.

Lemma f_equal_gen : forall {A B} (f g : A -> B) a b, f = g -> a = b -> f a = g b.
Proof. intros. subst. reflexivity. Qed.

Ltac unify_matrix_dims tac := 
  try reflexivity; 
  repeat (apply f_equal_gen; try reflexivity; 
          try (is_nat_equality; tac)).

Ltac restore_dims_rec A :=
   match A with
(* special cases *)
  | ?A × I _          => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (I n'))
                        end
  | I _ × ?B          => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (I n')  B')
                        end
  | ?A × @Zero ?n ?n  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (@Zero n' n'))
                        end
  | @Zero ?n ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero n' n') B')
                        end
  | ?A × @Zero ?n ?o  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' o A' (@Zero n' o))
                        end
  | @Zero ?m ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero m n') B')
                        end
  | ?A + @Zero ?m ?n => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mplus m' n' A' (@Zero m' n'))
                        end
  | @Zero ?m ?n + ?B => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?m' ?n' => constr:(@Mplus m' n' (@Zero m' n') B')
                        end
(* general cases *)
  | ?A == ?B  => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' => constr:(@mat_equiv m' n' A' B')
                  end
  | ?A × ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?n'' ?o' => constr:(@Mmult m' n' o' A' B')
                  end
                end 
  | ?A + ?B => let A' := restore_dims_rec A in 
               let B' := restore_dims_rec B in 
               match type of A' with 
               | Matrix ?m' ?n' =>
                 match type of B' with 
                 | Matrix ?m'' ?n'' => constr:(@Mplus m' n' A' B')
                 end
               end
  | ?c * ?A => let A' := restore_dims_rec A in 
               match type of A' with
               | Matrix ?m' ?n' => constr:(@Mscale m' n' c A')
               end
  (* Handle functions applied to matrices *)
  | ?f ?A    => let f' := restore_dims_rec f in 
               let A' := restore_dims_rec A in 
               constr:(f' A')
  (* default *)
  | ?A       => A
   end.

Ltac restore_dims tac := 
  match goal with
  | |- ?A      => let A' := restore_dims_rec A in 
                replace A with A' by unify_matrix_dims tac
  end.

Tactic Notation "restore_dims" tactic(tac) := restore_dims tac.

Tactic Notation "restore_dims" := restore_dims (try ring; unify_pows_two; simpl; lia).

(* Haoxuan Xu, Yichen Tao *)
(* 2021-05-20 23:37 *)