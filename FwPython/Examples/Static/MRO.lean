import FwPython.Static

/-! # C3 linearization regression examples

These examples are adapted from Samuele Pedroni's classic C3 test suite,
used in the original Python 2.3 MRO paper.

Each example defines a class hierarchy by its parent relationships and
checks the C3 merge result against the expected linearization.
Use `decide` so Lean's proof checker verifies each calculation.
The tests do not need axioms that trust compiled results. -/

/-! ## ex_2: Serious order disagreement (from Guido van Rossum)

    O
   / \
  X   Y
  |\ /|
  | X  |
  |/ \ |
  A    B
   \  /
    Z

  A(X,Y), B(Y,X) — the parent orders disagree on X vs Y.
  Z(A,B) has no valid C3 linearization.

  L[X] = [X, O]
  L[Y] = [Y, O]
  L[A] = [A, X, Y, O]
  L[B] = [B, Y, X, O]
  Z: merge([A,X,Y,O], [B,Y,X,O], [A,B]) — fails because
     X is in the tail of B's MRO, and Y is in the tail of A's MRO. -/

/-- ex_2: C3 merge for Z(A,B) fails. -/
example : c3Merge [["A","X","Y","O"], ["B","Y","X","O"], ["A","B"]] = none := by decide

/-! ## ex_5: Diamond with shared grandparent

       O
      /|\
     D E F
     |\ |
     C  B
      \/
       A

  D(O), E(O), F(O), C(D,F), B(D,E), A(B,C)

  L[D] = [D, O]
  L[E] = [E, O]
  L[F] = [F, O]
  L[B] = [B, D, E, O]
  L[C] = [C, D, F, O]
  L[A] = [A, B, C, D, E, F, O] -/

/-- ex_5: merge for B(D,E). -/
example : c3Merge [["D","O"], ["E","O"], ["D","E"]] = some ["D","E","O"] := by decide

/-- ex_5: merge for C(D,F). -/
example : c3Merge [["D","O"], ["F","O"], ["D","F"]] = some ["D","F","O"] := by decide

/-- ex_5: merge for A(B,C). -/
example : c3Merge [["B","D","E","O"], ["C","D","F","O"], ["B","C"]]
    = some ["B","C","D","E","F","O"] := by decide

/-! ## ex_6: Variant with different parent order in B

       O
      /|\
     D E F
     |  \|
     C   B
      \ /
       A

  D(O), E(O), F(O), C(D,F), B(E,D), A(B,C)

  L[B] = [B, E, D, O]
  L[C] = [C, D, F, O]
  L[A] = [A, B, E, C, D, F, O]

  Note: changing B's parent order from (D,E) to (E,D) changes A's MRO. -/

/-- ex_6: merge for B(E,D). -/
example : c3Merge [["E","O"], ["D","O"], ["E","D"]] = some ["E","D","O"] := by decide

/-- ex_6: merge for A(B,C). -/
example : c3Merge [["B","E","D","O"], ["C","D","F","O"], ["B","C"]]
    = some ["B","E","C","D","F","O"] := by decide

/-! ## ex_9: Complex hierarchy (from Samuele Pedroni)

  Difference between Python 2.2 MRO and C3.

  O, A(O), B(O), C(O), D(O), E(O)
  K1(A,B,C), K2(D,B,E), K3(D,A)
  Z(K1,K2,K3)

  L[K1] = [K1, A, B, C, O]
  L[K2] = [K2, D, B, E, O]
  L[K3] = [K3, D, A, O]
  L[Z]  = [Z, K1, K2, K3, D, A, B, C, E, O] -/

/-- ex_9: merge for K1(A,B,C). -/
example : c3Merge [["A","O"], ["B","O"], ["C","O"], ["A","B","C"]]
    = some ["A","B","C","O"] := by decide

/-- ex_9: merge for K2(D,B,E). -/
example : c3Merge [["D","O"], ["B","O"], ["E","O"], ["D","B","E"]]
    = some ["D","B","E","O"] := by decide

/-- ex_9: merge for K3(D,A). -/
example : c3Merge [["D","O"], ["A","O"], ["D","A"]]
    = some ["D","A","O"] := by decide

/-- ex_9: merge for Z(K1,K2,K3). -/
example : c3Merge [["K1","A","B","C","O"], ["K2","D","B","E","O"], ["K3","D","A","O"], ["K1","K2","K3"]]
    = some ["K1","K2","K3","D","A","B","C","E","O"] := by decide

/-! ## Edge cases -/

/-- Empty input: no lists to merge. -/
example : c3Merge [] = some [] := by decide

/-- Single empty list. -/
example : c3Merge [[]] = some [] := by decide

/-- Single class (Object). -/
example : c3Merge [["O"]] = some ["O"] := by decide

/-- Simple single inheritance: B(A), A(O). -/
example : c3Merge [["A","O"], ["A"]] = some ["A","O"] := by decide
