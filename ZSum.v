Require Import Psatz.
Require Import Arith.
Require Import Setoid.
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

Lemma func_shift: forall (f: nat -> Z)(n: nat),
  exists g, (forall x, (x < n)%nat -> f (x + n)%nat = g x).
Proof.
  intros.
  exists (fun x => f (x + n)%nat).
  tauto.
Qed.  

Lemma Zsum_g_g': forall (n : nat) (g g' : nat -> Z),
  (forall x : nat, (x < n)%nat -> g (S x) = g' x) ->
  Zsum g (S n) = g 0%nat + Zsum g' n.
Proof.
  intros.
  induction n.
  + simpl. 
    lia.
  + assert (forall x : nat, (x < n)%nat -> g (S x) = g' x). {
      intros.
      assert ((x < S n)%nat). { lia. }
      pose proof (H x H1). clear H1.
      tauto.
    }
    pose proof (IHn H0).
    replace (Zsum g (S (S n))) with (Zsum g (S n) + g (S n)) by reflexivity.
    rewrite H1.
    simpl.
    assert ((n < S n)%nat). { lia. }
    pose proof (H n H2).
    rewrite H3.
    lia.
Qed.

Lemma Zsum_f_g: forall (n : nat) (f g g' : nat -> Z),
  (forall x : nat, (x < S n)%nat -> f (x + S n)%nat = g' x) -> 
  (forall x : nat, (x < n)%nat -> f (x + n)%nat = g x) ->
  Zsum g n + f (2 * n)%nat = f n + Zsum g' n.
Proof.
  intros.
  destruct n.
  + simpl.
    lia.
  + replace (Zsum g' (S n)) with (Zsum g' n + g' n) by reflexivity.
    assert ((n < S (S n))%nat). { lia. }
    pose proof (H n H1). clear H1.
    rewrite <- H2.
    assert ((2 * S n = n + S (S n))%nat). { lia. }
    rewrite <- H1.
    assert (forall x : nat, (x < n)%nat -> g (S x) = g' x). {
      intros.
      assert ((S x < S n)%nat). { lia. }
      assert ((x < S (S n))%nat). { lia. }
      specialize (H x H5).
      specialize (H0 (S x) H4).
      rewrite <- H.
      rewrite <- H0.
      assert ((S x + S n = x + S (S n))%nat). { lia. }
      rewrite H6.
      reflexivity.
    }
  pose proof (Zsum_g_g' n g g' H3).
  rewrite H4.
  assert ((0 < S n)%nat). { lia. }
  pose proof (H0 0%nat H5).
  rewrite <- H6.
  simpl.
  lia.
Qed.

Lemma Zsum_eq_seg: forall (f: nat -> Z)(n : nat),
  forall (g: nat -> Z), (forall x, (x < n)%nat -> f (x + n)%nat = g x) ->
  Zsum f (2 * n) = Zsum f n + Zsum g n.
Proof.
  intros f n.
  induction n.
  + tauto.
  + intros g' ?. 
    (* Zsum f  (2n + 2) -> Zsum f (2n + 1) + f (2n + 1) *)
    (* Zsum f  (n + 1)  -> Zsum f n + f n *)
    (* Zsum g' (n + 1)  -> Zsum g' n + g' n *)
    simpl.
    pose proof func_shift f n.
    destruct H0 as [g ?].
    specialize (IHn g H0).
    assert ((n + S (n + 0))%nat = S (2 * n)). {
      simpl. lia.
    }
    rewrite H1. clear H1.

    (* Zsum f (2n + 1) -> Zsum f (2n) + f (2n) *)
    simpl.
    assert ((n + (n + 0))%nat = (2 * n)%nat). { lia. }
    rewrite H1. clear H1.

    (* use IHn: Zsum f (2n) = Zsum f n + Zsum g n *)
    rewrite IHn.
    assert ((n < S n)%nat). { lia. }
    pose proof H n H1.
    assert ((n + S n)%nat = S (2 * n)). {
      lia.
    }

    (* f (2n + 1) = g' n *)
    assert (f (S (2 * n)) = g' n). {
      rewrite <- H3.
      rewrite H2.
      reflexivity.
    }
    rewrite H4. clear H2 H3 H4.

    (* Zsum g n + f (2 * n)%nat = f n + Zsum g' n *)
    pose proof (Zsum_f_g n f g g' H H0).
    replace (Zsum f n + Zsum g n + f (2 * n)%nat + g' n) with (Zsum f n + (Zsum g n + f (2 * n)%nat) + g' n).
    2: { lia. }
    rewrite H2.
    lia.
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
(* 2021-05-26 01:12 *)