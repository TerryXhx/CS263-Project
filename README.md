# Correctness of Strassen’s Algorithm
The project for [CS 263 Programming languages, Spring 2021 ](https://jhc.sjtu.edu.cn/public/courses/CS263/). The main objective of the project is to prove the correctness of Strassen's algorithm for matrix multiplication.

## Project Overview

### Main files:

- ```Zsum.v```: Definition of Zsum, its properties essential to the definition of matrix multiplication and the proof of the properties.
- ```Matrix.v```: Definition of matrix, its operations and properties.
- `Strassen.v`: Definition of Strassen's algorithm, the proof of relevant lemmas and algorithm correctness.

### Important Definitions

#### Zsum

Zsum f n = f(0) + ... + f(n - 1)

```Coq
Fixpoint Zsum (f : nat -> Z) (n : nat) : Z := 
  match n with
  | O => 0
  | S n' => Zsum f n' +  f n'
  end.
```

#### Matrix

We define a _matrix_ as a simple function from two nats (corresponding to a row and a column) to an integer.

```Coq
Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop :=
  forall i j, i < m -> j < n -> A i j = B i j.
```

#### Matrix Multiplication

```Coq
Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o :=
  fun x z => Zsum (fun y => A x y * B y z)%Z n.
```

#### Split of Matrix

```Coq
Definition SubMat {m n} (A : Matrix m n) (rowl rowh coll colh : nat) : Matrix (rowh - rowl)%nat (colh - coll)%nat :=
  fun i j => A (i + rowl)%nat (j + coll)%nat.

Definition Split(n : nat) (A : Square (2 * n)) (A11 A12 A21 A22 : Square n): Prop :=
  A11 = SubMat A 0 n 0 n  /\
  A12 = SubMat A 0 n n (2 * n) /\
  A21 = SubMat A n (2 * n) 0 n /\ 
  A22 = SubMat A n (2 * n) n (2 * n)
.
```

#### Strassen's Algorithm

We define the algorithm as a quadratic relation recursively.

```Coq
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
```

#### Correctness of Strassen's Algorithms 

```Coq
Theorem StrassenCorrectness:
  forall (n : nat) (A B C D : Square n), StrassenMult n A B C -> D = A × B -> C == D
```

## Compilation Order

Please compile the files in the following order:

1. `Zsum.v`
2. `Matrix.v`
3. `Strassen.v`

## Proof Sketch

### Two Important Lemmas

#### MatMultBlockRes

This lemma states how to calculate the product of  block partitioned matrices only involving multiplication of submatrices of the factors.

```Coq
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
```

#### BlockEquivCompat

This lemma states how to judge the equivalence to matrices only involving the comparison of their submatrices.

```Coq
Lemma BlockEquivCompat:
  forall (n : nat) (A B : Square (2 * n)) (A11 A12 A21 A22 B11 B12 B21 B22 : Square n),
    n <> Z.to_nat 0 ->
    Split n A A11 A12 A21 A22 ->
    Split n B B11 B12 B21 B22 ->
    A11 == B11 -> A12 == B12 -> A21 == B21 -> A22 == B22 -> 
    A == B.
```

### Schema of Proof

By executing induction over `StrassenMult n A B C`, two cases need to be discussed.

1. SM_1 

   When the matrix is of order 1, the algorithm is defined by the initial definition of matrix multiplication, so the equivalence can be proved just by `reflexivity`.

2. SM_n

   (1) Apply `MatMultBlockRes` to get the expression of D11, D12, D21, D22 denoted by A11, A12, A21, A22, B11, B12, B21, B22.

   (2) Rewrite P1 - P7 in C11, C12, C21, C22, and then rewrite S1 - S10. Finally, we get C11, C12, C21, C22 denoted by A11, A12, A21, A22, B11, B12, B21, B22.

   (3) Use the distribution law of multiplication of matrices(defined and proved in `Matrix.v`) to simplify the expression of C11, C12, C21, C22.

   (4) The equivalence of Cij and Dij can be found directly.

   (5) Use `BlockEquivCompat` to prove C == D.

## Contributors

[Haoxuan Xu](https://github.com/TerryXhx), [Yichen Tao](https://github.com/TaoYC0904)

## References

1.  [Matrix: Lightweight Complex Matrices (umd.edu)](https://www.cs.umd.edu/~rrand/vqc/Matrix.html#Matrix).

2. [Complex: Complex Numbers in Coq (umd.edu)](https://www.cs.umd.edu/~rrand/vqc/Complex.html)

