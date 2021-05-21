Require Import Psatz.
Require Import Setoid.
Require Import Arith.
Require Import Bool.
Require Import Program.
Require Export Coq.ZArith.ZArith.

(* ZSum and its properties *)
Open Scope Z_scope.
Fixpoint Zsum (f : nat -> Z) (n : nat) : Z := 
  match n with
  | O => 0
  | S n' => Zsum f n' +  f n'
  end.
  
Lemma Zsum_eq : forall (f g : nat -> Z) (n : nat),
  (forall x, (x < n)%nat -> f x = g x) ->
  Zsum f n = Zsum g n.
Proof.
  intros f g n H. 
  induction n.
  + simpl. reflexivity.
  + simpl. 
    rewrite H by lia.
    rewrite IHn by (intros; apply H; lia).
    reflexivity.
Qed.

Lemma Zsum_plus : forall (f g : nat -> Z) (n : nat),
    Zsum (fun x => f x + g x) n = Zsum f n + Zsum g n.  
Proof. 
  intros f g n.  
  induction n.  
  - simpl. lia.  
  - simpl. rewrite IHn. lia.  
Qed.

Lemma Zmult_plus_distr_l : forall c1 c2 c3:Z, c1 * (c2 + c3) = c1 * c2 + c1 * c3.
Proof. intros. lia. Qed.

Lemma Zmult_plus_distr_r : forall c1 c2 c3:Z, (c1 + c2) * c3 = c1 * c3 + c2 * c3.
Proof. intros. lia. Qed.

Lemma Zsum_mult_l : forall (c : Z) (f : nat -> Z) (n : nat),
    c * Zsum f n = Zsum (fun x => c * f x) n.  
Proof.  
  intros c f n.  
  induction n.  
  - simpl; lia.  
  - simpl.  
    rewrite Zmult_plus_distr_l.  
    rewrite IHn.  
    reflexivity.  
Qed.

Lemma Zsum_eq_bounded : forall f g n, (forall x, (x < n)%nat -> f x = g x) -> Zsum f n = Zsum g n.
Proof. 
  intros f g n H. 
  induction n.
  + simpl. reflexivity.
  + simpl. 
    rewrite H by lia.
    rewrite IHn by (intros; apply H; lia).
    reflexivity.
Qed.

Lemma Zmult_plus_dist_l (x y z : Z) : x * (y + z) = x * y + x * z.
Proof.
  lia.
Qed.

Lemma Zmult_plus_dist_r (x y z : Z) : (x + y) * z = x * z + y * z.
Proof.
  lia.
Qed.

Close Scope Z_scope.
(* End of ZSum *)

(* Haoxuan Xu, Yichen Tao *)
(* 2021-05-20 23:37 *)