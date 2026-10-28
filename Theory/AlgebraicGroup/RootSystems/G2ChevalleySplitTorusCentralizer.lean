module

public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyBruhatCover
public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
import all Theory.AlgebraicGroup.RootSystems.G2ChevalleyBruhatCover

/-!
# Split-torus centralizer in the G2 Chevalley carrier

This module proves that the centralizer of the explicit rank-two split torus in
the closed integral `G2` Chevalley carrier is exactly that torus over every
algebraically closed field, including characteristics two and three.

The explicit Bruhat cover writes a carrier point as six negative root curves,
a canonical Weyl lift, a torus point, and six positive root curves.  A point
centralizing the torus has zero ambient matrix entries between distinct basis
weights, because the Laurent characters of the two-dimensional torus separate
those weights.  To read this condition in every characteristic, the proof
computes the Bruhat matrix as a sparse multivariate polynomial matrix over
`Int`.  A checked finite certificate treats all twelve Weyl cells: in the
identity cell it successively isolates all twelve root coordinates, while in
each other cell it isolates a nonzero torus monomial.  Evaluation of the
integral certificate in the coefficient field therefore forces the Weyl word
to be trivial and all root coordinates to vanish.  The Bruhat point is then
its torus factor.

Only the integral root-curve matrices, split-torus action, and explicit Bruhat
cover are used.  In particular, the argument is independent of G2 root
exhaustiveness, semisimplicity and center results, and general maximal-torus
centralizer theorems.
-/

open Matrix

namespace Theory.AlgebraicGroup.G2Chevalley

private abbrev Symbol := Fin 16
private abbrev RootSymbol := Fin 12
private abbrev Exponent := Symbol → Nat

private structure MultiTerm where
  exponent : Exponent
  coefficient : Int
  deriving DecidableEq

private abbrev MultiPoly := List MultiTerm

-- These finite tables are local copies of the integral G2 data. Keeping the
-- checker input local makes the closed certificate kernel-reducible without
-- requiring executable code for exposed definitions in imported modules.
private def centralizerAllBasis : List Basis :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

private def centralizerBasisWeight : Basis → Fin 2 → ℤ
  | 0, _ => 0 | 1, _ => 0
  | 2, 0 => 2 | 2, 1 => -1
  | 3, 0 => -3 | 3, 1 => 2
  | 4, 0 => -1 | 4, 1 => 1
  | 5, 0 => 1 | 5, 1 => 0
  | 6, 0 => 3 | 6, 1 => -1
  | 7, 0 => 0 | 7, 1 => 1
  | 8, 0 => -2 | 8, 1 => 1
  | 9, 0 => 3 | 9, 1 => -2
  | 10, 0 => 1 | 10, 1 => -1
  | 11, 0 => -1 | 11, 1 => 0
  | 12, 0 => -3 | 12, 1 => 1
  | 13, 0 => 0 | 13, 1 => -1

private lemma centralizerBasisWeight_eq (b : Basis) :
    centralizerBasisWeight b = basisWeight b := by
  funext i
  fin_cases b <;> fin_cases i <;>
    simp [centralizerBasisWeight, basisWeight, basisRoot,
      Root.pairingSimple, Root.coord]

private def centralizerCanonicalWeylWord : Fin 12 → List (Fin 2)
  | 0 => [] | 1 => [0] | 2 => [1] | 3 => [0, 1] | 4 => [1, 0]
  | 5 => [0, 1, 0] | 6 => [1, 0, 1] | 7 => [0, 1, 0, 1]
  | 8 => [1, 0, 1, 0] | 9 => [0, 1, 0, 1, 0]
  | 10 => [1, 0, 1, 0, 1] | 11 => [0, 1, 0, 1, 0, 1]

private lemma centralizerCanonicalWeylWord_eq (j : Fin 12) :
    centralizerCanonicalWeylWord j = canonicalWeylWord j := by
  fin_cases j <;> rfl

private def centralizerWeylEntries : Fin 2 → List (ℕ × ℕ × ℤ)
  | 0 => [(0, 0, -1), (0, 1, -1), (1, 1, 1),
      (8, 2, 1), (6, 3, 1), (5, 4, -1), (4, 5, 1), (3, 6, -1), (7, 7, 1),
      (2, 8, 1), (12, 9, -1), (11, 10, 1), (10, 11, -1), (9, 12, 1), (13, 13, 1)]
  | 1 => [(0, 0, 1), (1, 0, -3), (1, 1, -1),
      (4, 2, 1), (9, 3, 1), (2, 4, -1), (5, 5, 1), (7, 6, 1), (6, 7, -1),
      (10, 8, -1), (3, 9, 1), (8, 10, 1), (11, 11, 1), (13, 12, -1), (12, 13, 1)]

private def centralizerRootOperatorEntries : Root → List (ℕ × ℕ × ℤ)
  | 0 => [(0, 8, 1), (2, 0, 2), (2, 1, 1), (4, 3, 1), (5, 4, 2),
      (6, 5, 3), (9, 10, 3), (10, 11, 2), (11, 12, 1)]
  | 1 => [(1, 9, 1), (3, 0, 3), (3, 1, 2), (4, 2, 1), (7, 6, 1),
      (8, 10, 1), (12, 13, 1)]
  | 2 => [(0, 10, 1), (1, 10, -3), (2, 9, 1), (3, 8, -3), (4, 0, 1),
      (4, 1, 1), (5, 2, 2), (7, 5, -3), (8, 11, -2), (11, 13, 1)]
  | 3 => [(0, 11, -2), (1, 11, 3), (2, 10, -2), (4, 8, -2), (5, 0, -1),
      (6, 2, 3), (7, 4, 3), (8, 12, 1), (10, 13, 1)]
  | 4 => [(0, 12, -1), (1, 12, 1), (2, 11, -1), (5, 8, 1), (6, 0, 3),
      (6, 1, 1), (7, 3, 1), (9, 13, -1)]
  | 5 => [(0, 13, -1), (1, 13, 2), (3, 12, 1), (4, 11, 1), (5, 10, 1),
      (6, 9, 1), (7, 1, 1)]
  | 6 => [(0, 2, -1), (3, 4, -3), (4, 5, -2), (5, 6, -1), (8, 0, -2),
      (8, 1, -1), (10, 9, -1), (11, 10, -2), (12, 11, -3)]
  | 7 => [(1, 3, -1), (2, 4, -1), (6, 7, -1), (9, 0, -3), (9, 1, -2),
      (10, 8, -1), (13, 12, -1)]
  | 8 => [(0, 4, 1), (1, 4, -3), (2, 5, -2), (5, 7, 1), (8, 3, 1),
      (9, 2, -3), (10, 0, 1), (10, 1, 1), (11, 8, 2), (13, 11, -3)]
  | 9 => [(0, 5, 2), (1, 5, -3), (2, 6, -1), (4, 7, -1), (8, 4, 2),
      (10, 2, 2), (11, 0, 1), (12, 8, -3), (13, 10, -3)]
  | 10 => [(0, 6, -1), (1, 6, 1), (3, 7, -1), (8, 5, -1), (11, 2, 1),
      (12, 0, 3), (12, 1, 1), (13, 9, 1)]
  | 11 => [(0, 7, 1), (1, 7, -2), (9, 6, -1), (10, 5, -1), (11, 4, -1),
      (12, 3, -1), (13, 1, -1)]

private def centralizerRootDividedPowerTwoEntries : Root → List (ℕ × ℕ × ℤ)
  | 0 => [(2, 8, 1), (5, 3, 1), (6, 4, 3), (9, 11, 3), (10, 12, 1)]
  | 1 => [(3, 9, 1)]
  | 2 => [(3, 11, 3), (4, 10, -1), (5, 9, 1), (7, 2, -3), (8, 13, -1)]
  | 3 => [(2, 13, -1), (4, 12, -1), (5, 11, 1), (6, 10, -3), (7, 8, -3)]
  | 4 => [(6, 12, -1)] | 5 => [(7, 13, 1)]
  | 6 => [(3, 5, 3), (4, 6, 1), (8, 2, 1), (11, 9, 1), (12, 10, 3)]
  | 7 => [(9, 3, 1)]
  | 8 => [(2, 7, -1), (9, 5, 3), (10, 4, -1), (11, 3, 1), (13, 8, -3)]
  | 9 => [(8, 7, -1), (10, 6, -1), (11, 5, 1), (12, 4, -3), (13, 2, -3)]
  | 10 => [(12, 6, -1)] | 11 => [(13, 7, 1)]

private def centralizerRootDividedPowerThreeEntries : Root → List (ℕ × ℕ × ℤ)
  | 0 => [(6, 3, 1), (9, 12, 1)]
  | 2 => [(3, 13, 1), (7, 9, -1)]
  | 3 => [(6, 13, -1), (7, 12, -1)]
  | 6 => [(3, 6, -1), (12, 9, -1)]
  | 8 => [(9, 7, 1), (13, 3, -1)]
  | 9 => [(12, 7, 1), (13, 6, 1)]
  | _ => []

private def zeroExponent : Exponent := fun _ => 0

private def variableExponent (i : Symbol) (n : Nat) : Exponent :=
  fun j => if j = i then n else 0

private def addExponent (e f : Exponent) : Exponent := fun i => e i + f i

private def exponentLess (e f : Exponent) : Bool :=
  decide (List.ofFn e < List.ofFn f)

private def insertMultiTerm (t : MultiTerm) : MultiPoly → MultiPoly
  | [] => if t.coefficient = 0 then [] else [t]
  | s :: p =>
      if t.coefficient = 0 then s :: p
      else if t.exponent = s.exponent then
        let c := t.coefficient + s.coefficient
        if c = 0 then p else { t with coefficient := c } :: p
      else if exponentLess t.exponent s.exponent then t :: s :: p
      else s :: insertMultiTerm t p

private def normalizeMultiPoly : MultiPoly → MultiPoly :=
  List.foldr insertMultiTerm []

private def multiZero : MultiPoly := []

private def multiOne : MultiPoly := [{ exponent := zeroExponent, coefficient := 1 }]

private def multiVariable (i : Symbol) (n : Nat := 1) : MultiPoly :=
  [{ exponent := variableExponent i n, coefficient := 1 }]

private def multiScaleInt (c : Int) (p : MultiPoly) : MultiPoly :=
  normalizeMultiPoly (p.map fun t => { t with coefficient := c * t.coefficient })

private def multiAdd (p q : MultiPoly) : MultiPoly :=
  normalizeMultiPoly (p ++ q)

private def multiMul (p q : MultiPoly) : MultiPoly :=
  normalizeMultiPoly <| p.flatMap fun t => q.map fun s =>
    { exponent := addExponent t.exponent s.exponent
      coefficient := t.coefficient * s.coefficient }

private def multiEq (p q : MultiPoly) : Bool :=
  decide (normalizeMultiPoly p = normalizeMultiPoly q)

private def evalMonomial {R : Type*} [CommRing R]
    (a : Symbol → R) (e : Exponent) : R :=
  ∏ i, a i ^ e i

private def evalMultiTerm {R : Type*} [CommRing R]
    (a : Symbol → R) (t : MultiTerm) : R :=
  (t.coefficient : R) * evalMonomial a t.exponent

private def evalMultiPoly {R : Type*} [CommRing R]
    (a : Symbol → R) (p : MultiPoly) : R :=
  p.foldr (fun t value => evalMultiTerm a t + value) 0

private lemma evalMonomial_add {R : Type*} [CommRing R]
    (a : Symbol → R) (e f : Exponent) :
    evalMonomial a (addExponent e f) =
      evalMonomial a e * evalMonomial a f := by
  simp [evalMonomial, addExponent, pow_add, Finset.prod_mul_distrib]

private lemma evalMultiPoly_insert {R : Type*} [CommRing R]
    (a : Symbol → R) (t : MultiTerm) (p : MultiPoly) :
    evalMultiPoly a (insertMultiTerm t p) =
      evalMultiTerm a t + evalMultiPoly a p := by
  induction p with
  | nil =>
      simp only [insertMultiTerm]
      by_cases hc : t.coefficient = 0
      · rw [if_pos hc]
        simp [evalMultiPoly, evalMultiTerm, hc]
      · rw [if_neg hc]
        simp [evalMultiPoly]
  | cons s p ih =>
      simp only [insertMultiTerm]
      by_cases hc : t.coefficient = 0
      · rw [if_pos hc]
        simp [evalMultiPoly, evalMultiTerm, hc]
      · rw [if_neg hc]
        by_cases he : t.exponent = s.exponent
        · rw [if_pos he]
          let c := t.coefficient + s.coefficient
          by_cases hsum : c = 0
          · rw [if_pos hsum]
            simp only [evalMultiPoly, List.foldr_cons]
            have hcast : (t.coefficient : R) + (s.coefficient : R) = 0 := by
              rw [← Int.cast_add, show t.coefficient + s.coefficient = c by rfl,
                hsum, Int.cast_zero]
            rw [evalMultiTerm, evalMultiTerm, he]
            calc
              evalMultiPoly a p =
                  ((t.coefficient : R) + (s.coefficient : R)) *
                    evalMonomial a s.exponent + evalMultiPoly a p := by
                      rw [hcast]; simp
              _ = (t.coefficient : R) * evalMonomial a s.exponent +
                    ((s.coefficient : R) * evalMonomial a s.exponent +
                      evalMultiPoly a p) := by ring
          · rw [if_neg hsum]
            simp only [evalMultiPoly, List.foldr_cons, evalMultiTerm]
            change ((c : Int) : R) * evalMonomial a t.exponent +
                evalMultiPoly a p =
              (t.coefficient : R) * evalMonomial a t.exponent +
                ((s.coefficient : R) * evalMonomial a s.exponent +
                  evalMultiPoly a p)
            rw [he]
            dsimp [c]
            push_cast
            ring
        · rw [if_neg he]
          by_cases hless : exponentLess t.exponent s.exponent = true
          · rw [if_pos hless]
            simp [evalMultiPoly]
          · rw [if_neg hless]
            simp only [evalMultiPoly, List.foldr_cons]
            change evalMultiTerm a s + evalMultiPoly a (insertMultiTerm t p) =
              evalMultiTerm a t + (evalMultiTerm a s + evalMultiPoly a p)
            rw [ih]
            ring

private lemma evalMultiPoly_normalize {R : Type*} [CommRing R]
    (a : Symbol → R) (p : MultiPoly) :
    evalMultiPoly a (normalizeMultiPoly p) = evalMultiPoly a p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      change evalMultiPoly a (insertMultiTerm t (normalizeMultiPoly p)) = _
      rw [evalMultiPoly_insert, ih]
      rfl

private lemma evalMultiPoly_append {R : Type*} [CommRing R]
    (a : Symbol → R) (p q : MultiPoly) :
    evalMultiPoly a (p ++ q) = evalMultiPoly a p + evalMultiPoly a q := by
  induction p with
  | nil => simp [evalMultiPoly]
  | cons t p ih =>
      simp only [List.cons_append, evalMultiPoly, List.foldr_cons]
      change evalMultiTerm a t + evalMultiPoly a (p ++ q) =
        (evalMultiTerm a t + evalMultiPoly a p) + evalMultiPoly a q
      rw [ih]
      ring

private lemma evalMultiPoly_add {R : Type*} [CommRing R]
    (a : Symbol → R) (p q : MultiPoly) :
    evalMultiPoly a (multiAdd p q) =
      evalMultiPoly a p + evalMultiPoly a q := by
  rw [multiAdd, evalMultiPoly_normalize, evalMultiPoly_append]

private lemma evalMultiPoly_map_mul {R : Type*} [CommRing R]
    (a : Symbol → R) (t : MultiTerm) (q : MultiPoly) :
    evalMultiPoly a
        (q.map fun s =>
          { exponent := addExponent t.exponent s.exponent
            coefficient := t.coefficient * s.coefficient }) =
      evalMultiTerm a t * evalMultiPoly a q := by
  induction q with
  | nil => simp [evalMultiPoly]
  | cons s q ih =>
      simp only [List.map_cons, evalMultiPoly, List.foldr_cons]
      change evalMultiTerm a
          { exponent := addExponent t.exponent s.exponent
            coefficient := t.coefficient * s.coefficient } +
            evalMultiPoly a
              (q.map fun s =>
                { exponent := addExponent t.exponent s.exponent
                  coefficient := t.coefficient * s.coefficient }) =
        evalMultiTerm a t * (evalMultiTerm a s + evalMultiPoly a q)
      rw [ih]
      simp only [evalMultiTerm, evalMonomial_add]
      push_cast
      ring

private lemma evalMultiPoly_flatMap_mul {R : Type*} [CommRing R]
    (a : Symbol → R) (p q : MultiPoly) :
    evalMultiPoly a
        (p.flatMap fun t => q.map fun s =>
          { exponent := addExponent t.exponent s.exponent
            coefficient := t.coefficient * s.coefficient }) =
      evalMultiPoly a p * evalMultiPoly a q := by
  induction p with
  | nil => simp [evalMultiPoly]
  | cons t p ih =>
      change evalMultiPoly a
          ((q.map fun s =>
            { exponent := addExponent t.exponent s.exponent
              coefficient := t.coefficient * s.coefficient }) ++
            (p.flatMap fun t => q.map fun s =>
              { exponent := addExponent t.exponent s.exponent
                coefficient := t.coefficient * s.coefficient })) = _
      rw [evalMultiPoly_append, evalMultiPoly_map_mul, ih]
      simp only [evalMultiPoly, List.foldr_cons]
      ring

private lemma evalMultiPoly_mul {R : Type*} [CommRing R]
    (a : Symbol → R) (p q : MultiPoly) :
    evalMultiPoly a (multiMul p q) =
      evalMultiPoly a p * evalMultiPoly a q := by
  rw [multiMul, evalMultiPoly_normalize, evalMultiPoly_flatMap_mul]

private lemma evalMultiPoly_scaleInt {R : Type*} [CommRing R]
    (a : Symbol → R) (c : Int) (p : MultiPoly) :
    evalMultiPoly a (multiScaleInt c p) = (c : R) * evalMultiPoly a p := by
  rw [multiScaleInt, evalMultiPoly_normalize]
  induction p with
  | nil => simp [evalMultiPoly]
  | cons t p ih =>
      simp only [List.map_cons, evalMultiPoly, List.foldr_cons, evalMultiTerm]
      change ((c * t.coefficient : Int) : R) * evalMonomial a t.exponent +
          evalMultiPoly a
            (p.map fun t =>
              { exponent := t.exponent
                coefficient := c * t.coefficient }) =
        (c : R) *
          ((t.coefficient : R) * evalMonomial a t.exponent +
            evalMultiPoly a p)
      rw [ih]
      push_cast
      ring

private lemma evalMultiPoly_one {R : Type*} [CommRing R]
    (a : Symbol → R) : evalMultiPoly a multiOne = 1 := by
  simp [evalMultiPoly, evalMultiTerm, multiOne, evalMonomial, zeroExponent]

private abbrev SparseMultiMatrix := List (Nat × Nat × MultiPoly)

private def multiSparseEntryLess (i j i' j' : Nat) : Bool :=
  decide (i < i' ∨ (i = i' ∧ j < j'))

private def insertSparseEntry (i j : Nat) (p : MultiPoly) :
    SparseMultiMatrix → SparseMultiMatrix
  | [] => if multiEq p multiZero then [] else [(i, j, normalizeMultiPoly p)]
  | e :: es =>
      let p' := normalizeMultiPoly p
      if multiEq p' multiZero then e :: es
      else if i = e.1 ∧ j = e.2.1 then
        let q := multiAdd p' e.2.2
        if multiEq q multiZero then es else (i, j, q) :: es
      else if multiSparseEntryLess i j e.1 e.2.1 then (i, j, p') :: e :: es
      else e :: insertSparseEntry i j p' es

private def normalizeSparseMatrix : SparseMultiMatrix → SparseMultiMatrix :=
  List.foldr (fun e acc => insertSparseEntry e.1 e.2.1 e.2.2 acc) []

private def sparseOne : SparseMultiMatrix :=
  centralizerAllBasis.map fun i => (i.val, i.val, multiOne)

private def sparseAdd (A B : SparseMultiMatrix) : SparseMultiMatrix :=
  normalizeSparseMatrix (A ++ B)

private def sparseScaleEntries (p : MultiPoly)
    (entries : List (Nat × Nat × Int)) : SparseMultiMatrix :=
  normalizeSparseMatrix <| entries.map fun e =>
    (e.1, e.2.1, multiScaleInt e.2.2 p)

private def sparseMul (A B : SparseMultiMatrix) : SparseMultiMatrix :=
  normalizeSparseMatrix <| A.flatMap fun e => B.filterMap fun f =>
    if e.2.1 = f.1 then some (e.1, f.2.1, multiMul e.2.2 f.2.2) else none

private def sparseProduct (factors : List SparseMultiMatrix) : SparseMultiMatrix :=
  factors.foldl sparseMul sparseOne

private def sparseEntry (A : SparseMultiMatrix) (i j : Nat) : MultiPoly :=
  A.foldr
    (fun e p => if e.1 = i ∧ e.2.1 = j then multiAdd e.2.2 p else p)
    multiZero

private def rootCurveSparse (r : Root) (t : MultiPoly) : SparseMultiMatrix :=
  sparseAdd
    (sparseAdd
      (sparseAdd sparseOne
        (sparseScaleEntries t (centralizerRootOperatorEntries r)))
      (sparseScaleEntries (multiMul t t)
        (centralizerRootDividedPowerTwoEntries r)))
    (sparseScaleEntries (multiMul (multiMul t t) t)
      (centralizerRootDividedPowerThreeEntries r))

private lemma evalMultiPoly_eq_of_multiEq_eq_true
    {R : Type*} [CommRing R] (a : Symbol → R) {p q : MultiPoly}
    (h : multiEq p q = true) :
    evalMultiPoly a p = evalMultiPoly a q := by
  have hn : normalizeMultiPoly p = normalizeMultiPoly q := of_decide_eq_true h
  rw [← evalMultiPoly_normalize a p, hn, evalMultiPoly_normalize]

private def evalSparseTerm {R : Type*} [CommRing R] (a : Symbol → R)
    (e : Nat × Nat × MultiPoly) : Matrix Basis Basis R :=
  if hi : e.1 < 14 then
    if hj : e.2.1 < 14 then
      Matrix.single ⟨e.1, hi⟩ ⟨e.2.1, hj⟩ (evalMultiPoly a e.2.2)
    else 0
  else 0

private def evalSparseMatrix {R : Type*} [CommRing R] (a : Symbol → R)
    (A : SparseMultiMatrix) : Matrix Basis Basis R :=
  (A.map (evalSparseTerm a)).sum

private lemma evalSparseTerm_normalize {R : Type*} [CommRing R]
    (a : Symbol → R) (i j : Nat) (p : MultiPoly) :
    evalSparseTerm a (i, j, normalizeMultiPoly p) =
      evalSparseTerm a (i, j, p) := by
  simp only [evalSparseTerm]
  split_ifs
  · rw [evalMultiPoly_normalize]
  all_goals rfl

private lemma evalSparseTerm_zero_of_multiEq_eq_true
    {R : Type*} [CommRing R] (a : Symbol → R) (i j : Nat)
    {p : MultiPoly} (h : multiEq p multiZero = true) :
    evalSparseTerm a (i, j, p) = 0 := by
  simp only [evalSparseTerm]
  split_ifs
  · rw [evalMultiPoly_eq_of_multiEq_eq_true a h]
    exact Matrix.single_zero _ _
  all_goals rfl

private lemma evalSparseTerm_add {R : Type*} [CommRing R]
    (a : Symbol → R) (i j : Nat) (p q : MultiPoly) :
    evalSparseTerm a (i, j, multiAdd p q) =
      evalSparseTerm a (i, j, p) + evalSparseTerm a (i, j, q) := by
  simp only [evalSparseTerm]
  split_ifs
  · rw [evalMultiPoly_add, Matrix.single_add]
  all_goals simp

private lemma evalSparseMatrix_cons {R : Type*} [CommRing R]
    (a : Symbol → R) (e : Nat × Nat × MultiPoly) (A : SparseMultiMatrix) :
    evalSparseMatrix a (e :: A) =
      evalSparseTerm a e + evalSparseMatrix a A := rfl

private lemma evalSparseMatrix_insert {R : Type*} [CommRing R]
    (a : Symbol → R) (i j : Nat) (p : MultiPoly) (A : SparseMultiMatrix) :
    evalSparseMatrix a (insertSparseEntry i j p A) =
      evalSparseTerm a (i, j, p) + evalSparseMatrix a A := by
  induction A generalizing p with
  | nil =>
      simp only [insertSparseEntry]
      by_cases hp : multiEq p multiZero = true
      · rw [if_pos hp, evalSparseTerm_zero_of_multiEq_eq_true a i j hp]
        simp [evalSparseMatrix]
      · rw [if_neg hp]
        simp [evalSparseMatrix, evalSparseTerm_normalize]
  | cons e es ih =>
      rcases e with ⟨i', j', q⟩
      simp only [insertSparseEntry]
      let p' := normalizeMultiPoly p
      by_cases hp : multiEq p' multiZero = true
      · rw [if_pos hp]
        rw [← evalSparseTerm_normalize a i j p,
          evalSparseTerm_zero_of_multiEq_eq_true a i j hp]
        simp
      · rw [if_neg hp]
        by_cases hij : i = i' ∧ j = j'
        · rw [if_pos hij]
          rcases hij with ⟨rfl, rfl⟩
          let psum := multiAdd p' q
          by_cases hsum : multiEq psum multiZero = true
          · rw [if_pos hsum]
            have hzero := evalSparseTerm_zero_of_multiEq_eq_true
              a i j hsum
            rw [evalSparseTerm_add, evalSparseTerm_normalize] at hzero
            rw [evalSparseMatrix_cons]
            calc
              evalSparseMatrix a es = 0 + evalSparseMatrix a es := by simp
              _ = (evalSparseTerm a (i, j, p) +
                    evalSparseTerm a (i, j, q)) +
                  evalSparseMatrix a es := by rw [hzero]
              _ = evalSparseTerm a (i, j, p) +
                  (evalSparseTerm a (i, j, q) +
                    evalSparseMatrix a es) := by ac_rfl
          · rw [if_neg hsum]
            rw [evalSparseMatrix_cons, evalSparseMatrix_cons,
              evalSparseTerm_add, evalSparseTerm_normalize]
            ac_rfl
        · rw [if_neg hij]
          by_cases hless : multiSparseEntryLess i j i' j' = true
          · rw [if_pos hless]
            simp [evalSparseMatrix_cons, evalSparseTerm_normalize]
          · rw [if_neg hless]
            rw [evalSparseMatrix_cons, evalSparseMatrix_cons,
              ih (p := normalizeMultiPoly p), evalSparseTerm_normalize]
            ac_rfl

private lemma evalSparseMatrix_normalize {R : Type*} [CommRing R]
    (a : Symbol → R) (A : SparseMultiMatrix) :
    evalSparseMatrix a (normalizeSparseMatrix A) = evalSparseMatrix a A := by
  induction A with
  | nil => rfl
  | cons e es ih =>
      rcases e with ⟨i, j, p⟩
      change evalSparseMatrix a
          (insertSparseEntry i j p (normalizeSparseMatrix es)) = _
      rw [evalSparseMatrix_insert, ih]
      rfl

private lemma evalSparseMatrix_append {R : Type*} [CommRing R]
    (a : Symbol → R) (A B : SparseMultiMatrix) :
    evalSparseMatrix a (A ++ B) =
      evalSparseMatrix a A + evalSparseMatrix a B := by
  induction A with
  | nil => simp [evalSparseMatrix]
  | cons e es ih =>
      rw [List.cons_append, evalSparseMatrix_cons, evalSparseMatrix_cons, ih]
      ac_rfl

private lemma evalSparseMatrix_add {R : Type*} [CommRing R]
    (a : Symbol → R) (A B : SparseMultiMatrix) :
    evalSparseMatrix a (sparseAdd A B) =
      evalSparseMatrix a A + evalSparseMatrix a B := by
  rw [sparseAdd, evalSparseMatrix_normalize, evalSparseMatrix_append]
private lemma evalSparseMatrix_one {R : Type*} [CommRing R] (a : Symbol → R) :
    evalSparseMatrix a sparseOne = 1 := by
  have hterm (i : Basis) :
      evalSparseTerm a (i.val, i.val, multiOne) = Matrix.single i i 1 := by
    simp [evalSparseTerm, i.isLt, evalMultiPoly_one]
  have hmap : sparseOne.map (evalSparseTerm a) =
      centralizerAllBasis.map (fun i => Matrix.single i i 1) := by
    simp only [sparseOne, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i hi
    exact hterm i
  rw [evalSparseMatrix, hmap]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centralizerAllBasis]

private def SparseMatrixValid (A : SparseMultiMatrix) : Prop :=
  ∀ e ∈ A, e.1 < 14 ∧ e.2.1 < 14

private lemma sparseMatrixValid_insert (i j : ℕ) (p : MultiPoly)
    (A : SparseMultiMatrix) (hi : i < 14) (hj : j < 14)
    (hA : SparseMatrixValid A) :
    SparseMatrixValid (insertSparseEntry i j p A) := by
  induction A generalizing p with
  | nil =>
      simp only [insertSparseEntry]
      split_ifs
      · intro e he
        simp at he
      · intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        subst e
        exact ⟨hi, hj⟩
  | cons e es ih =>
      rcases e with ⟨i', j', q⟩
      have he : i' < 14 ∧ j' < 14 := hA (i', j', q) (by simp)
      have hes : SparseMatrixValid es := by
        intro f hf
        exact hA f (by simp [hf])
      simp only [insertSparseEntry]
      let p' := normalizeMultiPoly p
      by_cases hp : multiEq p' multiZero = true
      · rw [if_pos hp]
        exact hA
      · rw [if_neg hp]
        by_cases hcoord : i = i' ∧ j = j'
        · rw [if_pos hcoord]
          let psum := multiAdd p' q
          by_cases hsum : multiEq psum multiZero = true
          · rw [if_pos hsum]
            exact hes
          · rw [if_neg hsum]
            intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | hf
            · exact ⟨hi, hj⟩
            · exact hes f hf
        · rw [if_neg hcoord]
          by_cases hless : multiSparseEntryLess i j i' j' = true
          · rw [if_pos hless]
            intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | hf
            · exact ⟨hi, hj⟩
            · exact hA f (by simpa only [List.mem_cons] using hf)
          · rw [if_neg hless]
            intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | hf
            · exact he
            · exact ih (p := p') hes f hf

private lemma sparseMatrixValid_normalize (A : SparseMultiMatrix)
    (hA : SparseMatrixValid A) :
    SparseMatrixValid (normalizeSparseMatrix A) := by
  induction A with
  | nil => simp [SparseMatrixValid, normalizeSparseMatrix]
  | cons e es ih =>
      rcases e with ⟨i, j, p⟩
      have he : i < 14 ∧ j < 14 := hA (i, j, p) (by simp)
      have hes : SparseMatrixValid es := by
        intro f hf
        exact hA f (by simp [hf])
      exact sparseMatrixValid_insert i j p (normalizeSparseMatrix es)
        he.1 he.2 (ih hes)

private lemma sparseMatrixValid_add (A B : SparseMultiMatrix)
    (hA : SparseMatrixValid A) (hB : SparseMatrixValid B) :
    SparseMatrixValid (sparseAdd A B) := by
  apply sparseMatrixValid_normalize
  intro e he
  rw [List.mem_append] at he
  exact he.elim (hA e) (hB e)

private lemma sparseMatrixValid_one : SparseMatrixValid sparseOne := by
  intro e he
  simp only [sparseOne, List.mem_map] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨i.isLt, i.isLt⟩

private lemma evalSparseTerm_mul {R : Type*} [CommRing R] (a : Symbol → R)
    (e f : ℕ × ℕ × MultiPoly)
    (he : e.1 < 14 ∧ e.2.1 < 14) (hf : f.1 < 14 ∧ f.2.1 < 14) :
    evalSparseTerm a e * evalSparseTerm a f =
      if e.2.1 = f.1 then
        evalSparseTerm a (e.1, f.2.1, multiMul e.2.2 f.2.2)
      else 0 := by
  rcases e with ⟨i, j, p⟩
  rcases f with ⟨j', k, q⟩
  simp only at he hf
  simp only [evalSparseTerm, he.1, he.2, hf.1, hf.2,
    dif_pos, evalMultiPoly_mul]
  by_cases hj : j = j'
  · subst j'
    rw [if_pos rfl, Matrix.single_mul_single_same]
  · rw [if_neg hj, Matrix.single_mul_single_of_ne]
    intro hfin
    exact hj (Fin.ext_iff.mp hfin)

private lemma evalSparseMatrix_filterMap_mul {R : Type*} [CommRing R]
    (a : Symbol → R) (e : ℕ × ℕ × MultiPoly) (B : SparseMultiMatrix)
    (he : e.1 < 14 ∧ e.2.1 < 14) (hB : SparseMatrixValid B) :
    evalSparseMatrix a
        (B.filterMap fun f =>
          if e.2.1 = f.1 then
            some (e.1, f.2.1, multiMul e.2.2 f.2.2)
          else none) =
      evalSparseTerm a e * evalSparseMatrix a B := by
  induction B with
  | nil => simp [evalSparseMatrix]
  | cons f fs ih =>
      have hf := hB f (by simp)
      have hfs : SparseMatrixValid fs := by
        intro g hg
        exact hB g (by simp [hg])
      simp only [List.filterMap_cons]
      split_ifs with hmatch
      · rw [evalSparseMatrix_cons, evalSparseMatrix_cons,
          ih hfs, mul_add, evalSparseTerm_mul a e f he hf, if_pos hmatch]
      · rw [evalSparseMatrix_cons, ih hfs, mul_add,
          evalSparseTerm_mul a e f he hf, if_neg hmatch, zero_add]

private lemma evalSparseMatrix_flatMap_mul {R : Type*} [CommRing R]
    (a : Symbol → R) (A B : SparseMultiMatrix)
    (hA : SparseMatrixValid A) (hB : SparseMatrixValid B) :
    evalSparseMatrix a
        (A.flatMap fun e =>
          B.filterMap fun f =>
            if e.2.1 = f.1 then
              some (e.1, f.2.1, multiMul e.2.2 f.2.2)
            else none) =
      evalSparseMatrix a A * evalSparseMatrix a B := by
  induction A with
  | nil => simp [evalSparseMatrix]
  | cons e es ih =>
      have he := hA e (by simp)
      have hes : SparseMatrixValid es := by
        intro f hf
        exact hA f (by simp [hf])
      rw [List.flatMap_cons, evalSparseMatrix_append,
        evalSparseMatrix_filterMap_mul a e B he hB, ih hes,
        evalSparseMatrix_cons, add_mul]

private lemma evalSparseMatrix_mul {R : Type*} [CommRing R]
    (a : Symbol → R) (A B : SparseMultiMatrix)
    (hA : SparseMatrixValid A) (hB : SparseMatrixValid B) :
    evalSparseMatrix a (sparseMul A B) =
      evalSparseMatrix a A * evalSparseMatrix a B := by
  rw [sparseMul, evalSparseMatrix_normalize,
    evalSparseMatrix_flatMap_mul a A B hA hB]

private lemma sparseMatrixValid_mul (A B : SparseMultiMatrix)
    (hA : SparseMatrixValid A) (hB : SparseMatrixValid B) :
    SparseMatrixValid (sparseMul A B) := by
  apply sparseMatrixValid_normalize
  intro e he
  simp only [List.mem_flatMap, List.mem_filterMap] at he
  obtain ⟨x, hxA, g, hgB, hif⟩ := he
  split at hif
  · simp only [Option.some.injEq] at hif
    subst e
    exact ⟨(hA x hxA).1, (hB g hgB).2⟩
  · contradiction

private def IntegralEntriesValid (entries : List (ℕ × ℕ × ℤ)) : Prop :=
  ∀ e ∈ entries, e.1 < 14 ∧ e.2.1 < 14

private def IntegralEntryCoordinatesNodup
    (entries : List (ℕ × ℕ × ℤ)) : Prop :=
  (entries.map fun e => (e.1, e.2.1)).Nodup

private def specializeIntegralEntry {R : Type*} [CommRing R]
    (e : ℕ × ℕ × ℤ) : Matrix Basis Basis R :=
  if hi : e.1 < 14 then
    if hj : e.2.1 < 14 then
      Matrix.single ⟨e.1, hi⟩ ⟨e.2.1, hj⟩ (e.2.2 : R)
    else 0
  else 0

private lemma evalSparseTerm_scaleInt {R : Type*} [CommRing R]
    (a : Symbol → R) (p : MultiPoly) (e : ℕ × ℕ × ℤ) :
    evalSparseTerm a (e.1, e.2.1, multiScaleInt e.2.2 p) =
      evalMultiPoly a p • specializeIntegralEntry (R := R) e := by
  rcases e with ⟨i, j, c⟩
  simp only [evalSparseTerm, specializeIntegralEntry]
  split_ifs
  · rw [evalMultiPoly_scaleInt]
    ext row col
    simp [Matrix.single_apply, mul_comm]
  all_goals simp

private lemma evalSparseMatrix_scaleEntries {R : Type*} [CommRing R]
    (a : Symbol → R) (p : MultiPoly) (entries : List (ℕ × ℕ × ℤ)) :
    evalSparseMatrix a (sparseScaleEntries p entries) =
      evalMultiPoly a p •
        (entries.map (specializeIntegralEntry (R := R))).sum := by
  rw [sparseScaleEntries, evalSparseMatrix_normalize]
  induction entries with
  | nil => simp [evalSparseMatrix]
  | cons e es ih =>
      rw [List.map_cons, evalSparseMatrix_cons, evalSparseTerm_scaleInt,
        ih, List.map_cons, List.sum_cons, smul_add]

private lemma sparseMatrixValid_scaleEntries (p : MultiPoly)
    (entries : List (ℕ × ℕ × ℤ)) (hentries : IntegralEntriesValid entries) :
    SparseMatrixValid (sparseScaleEntries p entries) := by
  apply sparseMatrixValid_normalize
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  exact hentries f hf

private lemma matrixOfEntries_apply_eq_zero_of_not_mem
    (entries : List (ℕ × ℕ × ℤ)) (row col : Basis)
    (hnot : (row.val, col.val) ∉ entries.map fun e => (e.1, e.2.1)) :
    matrixOfEntries entries row col = 0 := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
      rcases e with ⟨i, j, c⟩
      have hcoord : ¬(row.val = i ∧ col.val = j) := by
        intro h
        exact hnot (by simp [h])
      have htail : (row.val, col.val) ∉ es.map fun e => (e.1, e.2.1) := by
        intro h
        exact hnot (by simp [h])
      change (if row.val = i ∧ col.val = j then c
        else matrixOfEntries es row col) = 0
      rw [if_neg hcoord, ih htail]

private lemma specialize_matrixOfEntries_eq_sum {R : Type*} [CommRing R]
    (entries : List (ℕ × ℕ × ℤ))
    (hvalid : IntegralEntriesValid entries)
    (hnodup : IntegralEntryCoordinatesNodup entries) :
    specialize (R := R) (matrixOfEntries entries) =
      (entries.map (specializeIntegralEntry (R := R))).sum := by
  induction entries with
  | nil =>
      ext row col
      simp [specialize, matrixOfEntries]
  | cons e es ih =>
      rcases e with ⟨i, j, c⟩
      have he : i < 14 ∧ j < 14 := hvalid (i, j, c) (by simp)
      have hvalidTail : IntegralEntriesValid es := by
        intro f hf
        exact hvalid f (by simp [hf])
      have hnodup' := List.nodup_cons.mp hnodup
      have hnodupTail : IntegralEntryCoordinatesNodup es := hnodup'.2
      have hnot : (i, j) ∉ es.map fun f => (f.1, f.2.1) := hnodup'.1
      rw [List.map_cons, List.sum_cons, ← ih hvalidTail hnodupTail]
      ext row col
      by_cases hcoord : row.val = i ∧ col.val = j
      · have hrow : row = ⟨i, he.1⟩ := Fin.ext hcoord.1
        have hcol : col = ⟨j, he.2⟩ := Fin.ext hcoord.2
        subst row
        subst col
        have hzero := matrixOfEntries_apply_eq_zero_of_not_mem es
          ⟨i, he.1⟩ ⟨j, he.2⟩ hnot
        change ((if i = i ∧ j = j then c
            else matrixOfEntries es ⟨i, he.1⟩ ⟨j, he.2⟩ : ℤ) : R) =
          specializeIntegralEntry (R := R) (i, j, c) ⟨i, he.1⟩ ⟨j, he.2⟩ +
            ((matrixOfEntries es ⟨i, he.1⟩ ⟨j, he.2⟩ : ℤ) : R)
        rw [if_pos ⟨rfl, rfl⟩, hzero]
        have hentry : specializeIntegralEntry (R := R) (i, j, c) =
            Matrix.single ⟨i, he.1⟩ ⟨j, he.2⟩ (c : R) := by
          simp [specializeIntegralEntry, he.1, he.2]
        rw [hentry]
        simp
      · have hsingle : specializeIntegralEntry (R := R) (i, j, c) row col = 0 := by
          simp only [specializeIntegralEntry, he.1, he.2, dif_pos]
          by_cases hrow : (⟨i, he.1⟩ : Basis) = row
          · have hrowVal : row.val = i := (Fin.ext_iff.mp hrow).symm
            have hcol : (⟨j, he.2⟩ : Basis) ≠ col := by
              intro hcol
              exact hcoord ⟨hrowVal, (Fin.ext_iff.mp hcol).symm⟩
            simp [hrow, hcol]
          · simp [hrow]
        simp only [Matrix.add_apply, hsingle, zero_add, specialize,
          Matrix.map_apply]
        change ((if row.val = i ∧ col.val = j then c
          else matrixOfEntries es row col : ℤ) : R) = _
        rw [if_neg hcoord]
        rfl

private lemma centralizerRootOperatorEntries_eq (r : Root) :
    centralizerRootOperatorEntries r = rootOperatorEntries r := by
  fin_cases r <;> rfl

private lemma centralizerRootDividedPowerTwoEntries_eq (r : Root) :
    centralizerRootDividedPowerTwoEntries r = rootDividedPowerTwoEntries r := by
  fin_cases r <;> rfl

private lemma centralizerRootDividedPowerThreeEntries_eq (r : Root) :
    centralizerRootDividedPowerThreeEntries r = rootDividedPowerThreeEntries r := by
  fin_cases r <;> rfl

private lemma centralizerRootOperatorEntries_valid (r : Root) :
    IntegralEntriesValid (centralizerRootOperatorEntries r) := by
  fin_cases r <;>
    simp [IntegralEntriesValid, centralizerRootOperatorEntries]

private lemma centralizerRootDividedPowerTwoEntries_valid (r : Root) :
    IntegralEntriesValid (centralizerRootDividedPowerTwoEntries r) := by
  fin_cases r <;>
    simp [IntegralEntriesValid, centralizerRootDividedPowerTwoEntries]

private lemma centralizerRootDividedPowerThreeEntries_valid (r : Root) :
    IntegralEntriesValid (centralizerRootDividedPowerThreeEntries r) := by
  fin_cases r <;>
    simp [IntegralEntriesValid, centralizerRootDividedPowerThreeEntries]

private lemma centralizerRootOperatorEntries_nodup (r : Root) :
    IntegralEntryCoordinatesNodup (centralizerRootOperatorEntries r) := by
  fin_cases r <;>
    simp [IntegralEntryCoordinatesNodup, centralizerRootOperatorEntries]

private lemma centralizerRootDividedPowerTwoEntries_nodup (r : Root) :
    IntegralEntryCoordinatesNodup (centralizerRootDividedPowerTwoEntries r) := by
  fin_cases r <;>
    simp [IntegralEntryCoordinatesNodup,
      centralizerRootDividedPowerTwoEntries]

private lemma centralizerRootDividedPowerThreeEntries_nodup (r : Root) :
    IntegralEntryCoordinatesNodup (centralizerRootDividedPowerThreeEntries r) := by
  fin_cases r <;>
    simp [IntegralEntryCoordinatesNodup,
      centralizerRootDividedPowerThreeEntries]

private lemma evalSparseMatrix_scaleRootOperator {R : Type*} [CommRing R]
    (a : Symbol → R) (p : MultiPoly) (r : Root) :
    evalSparseMatrix a
        (sparseScaleEntries p (centralizerRootOperatorEntries r)) =
      evalMultiPoly a p • specialize (R := R) (rootDividedPower r 1) := by
  rw [evalSparseMatrix_scaleEntries,
    ← specialize_matrixOfEntries_eq_sum
      (centralizerRootOperatorEntries r)
      (centralizerRootOperatorEntries_valid r)
      (centralizerRootOperatorEntries_nodup r),
    centralizerRootOperatorEntries_eq]
  rfl

private lemma evalSparseMatrix_scaleRootDividedPowerTwo
    {R : Type*} [CommRing R] (a : Symbol → R) (p : MultiPoly) (r : Root) :
    evalSparseMatrix a
        (sparseScaleEntries p
          (centralizerRootDividedPowerTwoEntries r)) =
      evalMultiPoly a p • specialize (R := R) (rootDividedPower r 2) := by
  rw [evalSparseMatrix_scaleEntries,
    ← specialize_matrixOfEntries_eq_sum
      (centralizerRootDividedPowerTwoEntries r)
      (centralizerRootDividedPowerTwoEntries_valid r)
      (centralizerRootDividedPowerTwoEntries_nodup r),
    centralizerRootDividedPowerTwoEntries_eq]
  rfl

private lemma evalSparseMatrix_scaleRootDividedPowerThree
    {R : Type*} [CommRing R] (a : Symbol → R) (p : MultiPoly) (r : Root) :
    evalSparseMatrix a
        (sparseScaleEntries p
          (centralizerRootDividedPowerThreeEntries r)) =
      evalMultiPoly a p • specialize (R := R) (rootDividedPower r 3) := by
  rw [evalSparseMatrix_scaleEntries,
    ← specialize_matrixOfEntries_eq_sum
      (centralizerRootDividedPowerThreeEntries r)
      (centralizerRootDividedPowerThreeEntries_valid r)
      (centralizerRootDividedPowerThreeEntries_nodup r),
    centralizerRootDividedPowerThreeEntries_eq]
  rfl

private lemma sparseMatrixValid_rootCurveSparse (r : Root) (p : MultiPoly) :
    SparseMatrixValid (rootCurveSparse r p) := by
  apply sparseMatrixValid_add
  · apply sparseMatrixValid_add
    · apply sparseMatrixValid_add sparseOne
        (sparseScaleEntries p (centralizerRootOperatorEntries r))
        sparseMatrixValid_one
      exact sparseMatrixValid_scaleEntries p _
        (centralizerRootOperatorEntries_valid r)
    · exact sparseMatrixValid_scaleEntries (multiMul p p) _
        (centralizerRootDividedPowerTwoEntries_valid r)
  · exact sparseMatrixValid_scaleEntries (multiMul (multiMul p p) p) _
      (centralizerRootDividedPowerThreeEntries_valid r)

private lemma evalSparseMatrix_rootCurveSparse {R : Type*} [CommRing R]
    (a : Symbol → R) (r : Root) (p : MultiPoly) :
    evalSparseMatrix a (rootCurveSparse r p) =
      rootCurve r (evalMultiPoly a p) := by
  simp only [rootCurveSparse]
  rw [evalSparseMatrix_add, evalSparseMatrix_add,
    evalSparseMatrix_add, evalSparseMatrix_one,
    evalSparseMatrix_scaleRootOperator,
    evalSparseMatrix_scaleRootDividedPowerTwo,
    evalSparseMatrix_scaleRootDividedPowerThree]
  simp_rw [evalMultiPoly_mul]
  simp [rootCurve, pow_succ]

private def integralMatrixSparse
    (entries : List (Nat × Nat × Int)) : SparseMultiMatrix :=
  sparseScaleEntries multiOne entries

private lemma sparseMatrixValid_integralMatrixSparse
    (entries : List (Nat × Nat × Int))
    (hentries : IntegralEntriesValid entries) :
    SparseMatrixValid (integralMatrixSparse entries) :=
  sparseMatrixValid_scaleEntries multiOne entries hentries

private lemma evalSparseMatrix_integralMatrixSparse
    {R : Type*} [CommRing R] (a : Symbol → R)
    (entries : List (Nat × Nat × Int))
    (hvalid : IntegralEntriesValid entries)
    (hnodup : IntegralEntryCoordinatesNodup entries) :
    evalSparseMatrix a (integralMatrixSparse entries) =
      specialize (R := R) (matrixOfEntries entries) := by
  rw [integralMatrixSparse, evalSparseMatrix_scaleEntries,
    evalMultiPoly_one, one_smul,
    specialize_matrixOfEntries_eq_sum entries hvalid hnodup]

private lemma weylEntries_valid (i : Fin 2) :
    IntegralEntriesValid (centralizerWeylEntries i) := by
  fin_cases i <;> simp [IntegralEntriesValid, centralizerWeylEntries]

private lemma weylEntries_nodup (i : Fin 2) :
    IntegralEntryCoordinatesNodup (centralizerWeylEntries i) := by
  fin_cases i <;> simp [IntegralEntryCoordinatesNodup, centralizerWeylEntries]

private lemma centralizerWeylEntries_eq (i : Fin 2) :
    centralizerWeylEntries i = weylEntries i := by
  fin_cases i <;> rfl

private lemma sparseMatrixValid_weyl (i : Fin 2) :
    SparseMatrixValid (integralMatrixSparse (centralizerWeylEntries i)) :=
  sparseMatrixValid_integralMatrixSparse _ (weylEntries_valid i)

private lemma evalSparseMatrix_weyl {R : Type*} [CommRing R]
    (a : Symbol → R) (i : Fin 2) :
    evalSparseMatrix a (integralMatrixSparse (centralizerWeylEntries i)) =
      specialize (R := R) (weyl i) := by
  calc
    evalSparseMatrix a (integralMatrixSparse (centralizerWeylEntries i)) =
        specialize (R := R) (matrixOfEntries (centralizerWeylEntries i)) :=
      evalSparseMatrix_integralMatrixSparse a (centralizerWeylEntries i)
        (weylEntries_valid i) (weylEntries_nodup i)
    _ = specialize (R := R) (weyl i) := by
      rw [centralizerWeylEntries_eq]
      rfl

private lemma sparseMatrixValid_foldl_sparseMul
    (factors : List SparseMultiMatrix) (A : SparseMultiMatrix)
    (hA : SparseMatrixValid A)
    (hfactors : ∀ B ∈ factors, SparseMatrixValid B) :
    SparseMatrixValid (factors.foldl sparseMul A) := by
  induction factors generalizing A with
  | nil => exact hA
  | cons B factors ih =>
      apply ih (sparseMul A B)
      · exact sparseMatrixValid_mul A B hA (hfactors B (by simp))
      · intro C hC
        exact hfactors C (by simp [hC])

private lemma evalSparseMatrix_foldl_sparseMul
    {R : Type*} [CommRing R] (a : Symbol → R)
    (factors : List SparseMultiMatrix) (A : SparseMultiMatrix)
    (hA : SparseMatrixValid A)
    (hfactors : ∀ B ∈ factors, SparseMatrixValid B) :
    evalSparseMatrix a (factors.foldl sparseMul A) =
      evalSparseMatrix a A * (factors.map (evalSparseMatrix a)).prod := by
  induction factors generalizing A with
  | nil => simp
  | cons B factors ih =>
      have hB : SparseMatrixValid B := hfactors B (by simp)
      have htail : ∀ C ∈ factors, SparseMatrixValid C := by
        intro C hC
        exact hfactors C (by simp [hC])
      rw [List.foldl_cons, ih (sparseMul A B)
        (sparseMatrixValid_mul A B hA hB) htail,
        evalSparseMatrix_mul a A B hA hB]
      simp [mul_assoc]

private lemma sparseMatrixValid_sparseProduct
    (factors : List SparseMultiMatrix)
    (hfactors : ∀ B ∈ factors, SparseMatrixValid B) :
    SparseMatrixValid (sparseProduct factors) :=
  sparseMatrixValid_foldl_sparseMul factors sparseOne
    sparseMatrixValid_one hfactors

private lemma evalSparseMatrix_sparseProduct
    {R : Type*} [CommRing R] (a : Symbol → R)
    (factors : List SparseMultiMatrix)
    (hfactors : ∀ B ∈ factors, SparseMatrixValid B) :
    evalSparseMatrix a (sparseProduct factors) =
      (factors.map (evalSparseMatrix a)).prod := by
  rw [sparseProduct,
    evalSparseMatrix_foldl_sparseMul a factors sparseOne
      sparseMatrixValid_one hfactors,
    evalSparseMatrix_one, one_mul]

private def rootSymbol (i : RootSymbol) : Symbol :=
  finSumFinEquiv (Sum.inl i : RootSymbol ⊕ Fin 4)

private def torusSymbol (i : Fin 4) : Symbol :=
  finSumFinEquiv (Sum.inr i : RootSymbol ⊕ Fin 4)

private def negativeSlot (i : Fin 6) : RootSymbol :=
  finSumFinEquiv (Sum.inl i : Fin 6 ⊕ Fin 6)

private def positiveSlot (i : Fin 6) : RootSymbol :=
  finSumFinEquiv (Sum.inr i : Fin 6 ⊕ Fin 6)

private lemma evalMultiPoly_variable {R : Type*} [CommRing R]
    (a : Symbol → R) (i : Symbol) (n : Nat) :
    evalMultiPoly a (multiVariable i n) = a i ^ n := by
  simp [multiVariable, evalMultiPoly, evalMultiTerm, evalMonomial,
    variableExponent]

private def negativeRoot : Fin 6 → Root
  | 0 => 6 | 1 => 10 | 2 => 9 | 3 => 11 | 4 => 8 | 5 => 7

private def positiveRoot : Fin 6 → Root
  | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 5 | 4 => 2 | 5 => 1

private def rootFactor (negative : Bool) (i : Fin 6) : SparseMultiMatrix :=
  let r := if negative then negativeRoot i else positiveRoot i
  let slot : RootSymbol := if negative then negativeSlot i else positiveSlot i
  rootCurveSparse r (multiVariable (rootSymbol slot))

private def torusMonomial : Fin 14 → MultiPoly
  | 0 | 1 => multiOne
  | 2 => multiMul (multiVariable (torusSymbol 2) 2) (multiVariable (torusSymbol 1))
  | 3 => multiMul (multiVariable (torusSymbol 0) 3) (multiVariable (torusSymbol 3) 2)
  | 4 => multiMul (multiVariable (torusSymbol 0)) (multiVariable (torusSymbol 3))
  | 5 => multiVariable (torusSymbol 2)
  | 6 => multiMul (multiVariable (torusSymbol 2) 3) (multiVariable (torusSymbol 1))
  | 7 => multiVariable (torusSymbol 3)
  | 8 => multiMul (multiVariable (torusSymbol 0) 2) (multiVariable (torusSymbol 3))
  | 9 => multiMul (multiVariable (torusSymbol 2) 3) (multiVariable (torusSymbol 1) 2)
  | 10 => multiMul (multiVariable (torusSymbol 2)) (multiVariable (torusSymbol 1))
  | 11 => multiVariable (torusSymbol 0)
  | 12 => multiMul (multiVariable (torusSymbol 0) 3) (multiVariable (torusSymbol 3))
  | 13 => multiVariable (torusSymbol 1)

private def torusSparse : SparseMultiMatrix :=
  centralizerAllBasis.map fun i => (i.val, i.val, torusMonomial i)

private def symbolicBruhatFactors (j : Fin 12) : List SparseMultiMatrix :=
    (([0, 1, 2, 3, 4, 5] : List (Fin 6)).map (rootFactor true)) ++
    ((centralizerCanonicalWeylWord j).map fun i =>
      integralMatrixSparse (centralizerWeylEntries i)) ++
    [torusSparse] ++
    (([0, 1, 2, 3, 4, 5] : List (Fin 6)).map (rootFactor false))

private def symbolicBruhat (j : Fin 12) : SparseMultiMatrix :=
  sparseProduct (symbolicBruhatFactors j)

private def sparseRowOne (row : Basis) : SparseMultiMatrix :=
  [(row.val, row.val, multiOne)]

private def symbolicBruhatRow (j : Fin 12) (row : Basis) : SparseMultiMatrix :=
  (symbolicBruhatFactors j).foldl sparseMul (sparseRowOne row)

private def bruhatAssignment {k : Type*} [Field k]
    (aNeg aPos : Fin 6 → k) (u : TorusParameter k) : Symbol → k :=
  fun i =>
    match (finSumFinEquiv : RootSymbol ⊕ Fin 4 ≃ Symbol).symm i with
    | Sum.inl r =>
        match (finSumFinEquiv : Fin 6 ⊕ Fin 6 ≃ RootSymbol).symm r with
        | Sum.inl q => aNeg q
        | Sum.inr q => aPos q
    | Sum.inr q =>
        match q with
        | 0 => u 0
        | 1 => u 1
        | 2 => ↑(u 0)⁻¹
        | 3 => ↑(u 1)⁻¹

private lemma bruhatAssignment_negative {k : Type*} [Field k]
    (aNeg aPos : Fin 6 → k) (u : TorusParameter k) (i : Fin 6) :
    bruhatAssignment aNeg aPos u
      (rootSymbol (negativeSlot i)) = aNeg i := by
  simp [bruhatAssignment, rootSymbol, negativeSlot]

private lemma bruhatAssignment_positive {k : Type*} [Field k]
    (aNeg aPos : Fin 6 → k) (u : TorusParameter k) (i : Fin 6) :
    bruhatAssignment aNeg aPos u
      (rootSymbol (positiveSlot i)) = aPos i := by
  simp [bruhatAssignment, rootSymbol, positiveSlot]

private lemma bruhatAssignment_torus {k : Type*} [Field k]
    (aNeg aPos : Fin 6 → k) (u : TorusParameter k) (i : Fin 4) :
    bruhatAssignment aNeg aPos u (torusSymbol i) =
      match i with
      | 0 => u 0
      | 1 => u 1
      | 2 => ↑(u 0)⁻¹
      | 3 => ↑(u 1)⁻¹ := by
  fin_cases i <;> simp [bruhatAssignment, torusSymbol]

private lemma sparseMatrixValid_rootFactor (negative : Bool) (i : Fin 6) :
    SparseMatrixValid (rootFactor negative i) := by
  simp only [rootFactor]
  exact sparseMatrixValid_rootCurveSparse _ _

private lemma evalSparseMatrix_negativeRootFactor {k : Type*} [Field k]
    (aNeg aPos : Fin 6 → k) (u : TorusParameter k) (i : Fin 6) :
    evalSparseMatrix (bruhatAssignment aNeg aPos u) (rootFactor true i) =
      rootCurve (negativeRoot i) (aNeg i) := by
  simp [rootFactor, evalSparseMatrix_rootCurveSparse, evalMultiPoly_variable,
    bruhatAssignment_negative]

private lemma evalSparseMatrix_positiveRootFactor {k : Type*} [Field k]
    (aNeg aPos : Fin 6 → k) (u : TorusParameter k) (i : Fin 6) :
    evalSparseMatrix (bruhatAssignment aNeg aPos u) (rootFactor false i) =
      rootCurve (positiveRoot i) (aPos i) := by
  simp [rootFactor, evalSparseMatrix_rootCurveSparse, evalMultiPoly_variable,
    bruhatAssignment_positive]

private lemma evalMultiPoly_torusMonomial {k : Type*} [Field k]
    (aNeg aPos : Fin 6 → k) (u : TorusParameter k) (i : Basis) :
    evalMultiPoly (bruhatAssignment aNeg aPos u) (torusMonomial i) =
      (basisTorusUnit u i : k) := by
  fin_cases i <;>
    simp [torusMonomial, evalMultiPoly_one, evalMultiPoly_variable,
      evalMultiPoly_mul, bruhatAssignment_torus, basisTorusUnit, basisWeight,
      basisRoot, Root.pairingSimple, Root.coord, pow_succ] <;> ring

private lemma sparseMatrixValid_torusSparse :
    SparseMatrixValid torusSparse := by
  intro e he
  simp only [torusSparse, List.mem_map] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨i.isLt, i.isLt⟩

set_option maxHeartbeats 2000000 in
private lemma evalSparseMatrix_torusSparse {k : Type*} [Field k]
    (aNeg aPos : Fin 6 → k) (u : TorusParameter k) :
    evalSparseMatrix (bruhatAssignment aNeg aPos u) torusSparse =
      (torusElement u : Matrix Basis Basis k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evalSparseMatrix, torusSparse, centralizerAllBasis, evalSparseTerm,
      evalMultiPoly_torusMonomial, torusElement]

private def bruhatMatrixFactors {k : Type*} [Field k]
    (j : Fin 12) (aNeg : Fin 6 → k) (u : TorusParameter k)
    (aPos : Fin 6 → k) : List (Matrix Basis Basis k) :=
  (([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun i =>
      rootCurve (negativeRoot i) (aNeg i)) ++
    ((canonicalWeylWord j).map fun i => specialize (R := k) (weyl i)) ++
    [(torusElement u : Matrix Basis Basis k)] ++
    (([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun i =>
      rootCurve (positiveRoot i) (aPos i))

private lemma symbolicBruhatFactors_valid (j : Fin 12) :
    ∀ B ∈ symbolicBruhatFactors j, SparseMatrixValid B := by
  intro B hB
  simp only [symbolicBruhatFactors, List.mem_append, List.mem_map,
    List.mem_singleton] at hB
  rcases hB with ((hNeg | hWeyl) | hTorus) | hPos
  · obtain ⟨i, _, hi⟩ := hNeg
    exact hi ▸ sparseMatrixValid_rootFactor true i
  · obtain ⟨i, _, hi⟩ := hWeyl
    exact hi ▸ sparseMatrixValid_weyl i
  · exact hTorus ▸ sparseMatrixValid_torusSparse
  · obtain ⟨i, _, hi⟩ := hPos
    exact hi ▸ sparseMatrixValid_rootFactor false i

private lemma sparseMatrixValid_sparseRowOne (row : Basis) :
    SparseMatrixValid (sparseRowOne row) := by
  intro e he
  simp only [sparseRowOne, List.mem_singleton] at he
  subst e
  exact ⟨row.isLt, row.isLt⟩

private lemma sparseMatrixValid_symbolicBruhatRow (j : Fin 12) (row : Basis) :
    SparseMatrixValid (symbolicBruhatRow j row) := by
  exact sparseMatrixValid_foldl_sparseMul (symbolicBruhatFactors j)
    (sparseRowOne row) (sparseMatrixValid_sparseRowOne row)
    (symbolicBruhatFactors_valid j)

private def bruhatMatrix {k : Type*} [Field k]
    (j : Fin 12) (aNeg : Fin 6 → k) (u : TorusParameter k)
    (aPos : Fin 6 → k) : Matrix Basis Basis k :=
  (bruhatMatrixFactors j aNeg u aPos).prod

set_option maxHeartbeats 5000000 in
private lemma evalSparseMatrix_symbolicBruhat {k : Type*} [Field k]
    (j : Fin 12) (aNeg aPos : Fin 6 → k) (u : TorusParameter k) :
    evalSparseMatrix (bruhatAssignment aNeg aPos u) (symbolicBruhat j) =
      bruhatMatrix j aNeg u aPos := by

  rw [symbolicBruhat, evalSparseMatrix_sparseProduct
    (bruhatAssignment aNeg aPos u) (symbolicBruhatFactors j)
    (symbolicBruhatFactors_valid j)]
  have hneg :
      (([0, 1, 2, 3, 4, 5] : List (Fin 6)).map (rootFactor true)).map
          (evalSparseMatrix (bruhatAssignment aNeg aPos u)) =
        ([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun i =>
          rootCurve (negativeRoot i) (aNeg i) := by
    simp only [List.map_cons, List.map_nil,
      evalSparseMatrix_negativeRootFactor]
  have hweyl :
      ((centralizerCanonicalWeylWord j).map fun i =>
          integralMatrixSparse (centralizerWeylEntries i)).map
          (evalSparseMatrix (bruhatAssignment aNeg aPos u)) =
        (centralizerCanonicalWeylWord j).map fun i =>
          specialize (R := k) (weyl i) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    simpa only [Function.comp_apply] using
      evalSparseMatrix_weyl (bruhatAssignment aNeg aPos u) i
  have hpos :
      (([0, 1, 2, 3, 4, 5] : List (Fin 6)).map (rootFactor false)).map
          (evalSparseMatrix (bruhatAssignment aNeg aPos u)) =
        ([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun i =>
          rootCurve (positiveRoot i) (aPos i) := by
    simp only [List.map_cons, List.map_nil,
      evalSparseMatrix_positiveRootFactor]
  unfold bruhatMatrix bruhatMatrixFactors symbolicBruhatFactors
  simp only [List.map_append]
  rw [hneg, hweyl, hpos]
  rw [centralizerCanonicalWeylWord_eq]
  simp only [List.map_cons, List.map_nil,
    evalSparseMatrix_torusSparse aNeg aPos u]

private lemma evalSparseMatrix_sparseRowOne {R : Type*} [CommRing R]
    (a : Symbol → R) (row : Basis) :
    evalSparseMatrix a (sparseRowOne row) = Matrix.single row row 1 := by
  ext i q
  simp [sparseRowOne, evalSparseMatrix, evalSparseTerm, evalMultiPoly_one]

set_option maxHeartbeats 5000000 in
private lemma evalSparseMatrix_symbolicBruhatRow {k : Type*} [Field k]
    (j : Fin 12) (aNeg aPos : Fin 6 → k) (u : TorusParameter k)
    (row col : Basis) :
    evalSparseMatrix (bruhatAssignment aNeg aPos u)
        (symbolicBruhatRow j row) row col =
      bruhatMatrix j aNeg u aPos row col := by
  have hprod :
      ((symbolicBruhatFactors j).map
        (evalSparseMatrix (bruhatAssignment aNeg aPos u))).prod =
        bruhatMatrix j aNeg u aPos := by
    rw [← evalSparseMatrix_sparseProduct
      (bruhatAssignment aNeg aPos u) (symbolicBruhatFactors j)
      (symbolicBruhatFactors_valid j)]
    exact evalSparseMatrix_symbolicBruhat j aNeg aPos u
  rw [symbolicBruhatRow,
    evalSparseMatrix_foldl_sparseMul
      (bruhatAssignment aNeg aPos u) (symbolicBruhatFactors j)
      (sparseRowOne row) (sparseMatrixValid_sparseRowOne row)
      (symbolicBruhatFactors_valid j),
    evalSparseMatrix_sparseRowOne, hprod]
  rw [Matrix.single_mul_eq_updateRow_zero]
  simp

private def zeroVariables (solved : List RootSymbol) (p : MultiPoly) : MultiPoly :=
  p.filter fun t => solved.all fun i => decide (t.exponent (rootSymbol i) = 0)

private def sparseZeroVariables (solved : List RootSymbol)
    (A : SparseMultiMatrix) : SparseMultiMatrix :=
  normalizeSparseMatrix <| A.map fun e =>
    (e.1, e.2.1, zeroVariables solved e.2.2)

private def symbolicBruhatRowSolved (j : Fin 12) (solved : List RootSymbol)
    (row : Basis) : SparseMultiMatrix :=
  (symbolicBruhatFactors j).foldl
    (fun A B => sparseMul A (sparseZeroVariables solved B))
    (sparseRowOne row)

private structure CertificateStep where
  row : Basis
  col : Basis
  target : Option RootSymbol

private def stepVar (row col : Basis) (target : RootSymbol) : CertificateStep :=
  { row, col, target := some target }

private def stepConst (row col : Basis) : CertificateStep :=
  { row, col, target := none }

private def stepValid (j : Fin 12) (solved : List RootSymbol)
    (s : CertificateStep) : Bool :=
  decide (centralizerBasisWeight s.row ≠ centralizerBasisWeight s.col) &&
  match normalizeMultiPoly
      (sparseEntry (symbolicBruhatRowSolved j solved s.row)
        s.row.val s.col.val) with
  | [t] =>
      decide (t.coefficient = 1 ∨ t.coefficient = -1) &&
      match s.target with
      | some v =>
          decide (0 < t.exponent (rootSymbol v)) &&
          (List.finRange 12).all fun i =>
            decide (i = v.val ∨ t.exponent (rootSymbol ⟨i, by omega⟩) = 0)
      | none =>
          (List.finRange 12).all fun i =>
            decide (t.exponent (rootSymbol ⟨i, by omega⟩) = 0)
  | _ => false

private def certificateValidAux (j : Fin 12) :
    List RootSymbol → List CertificateStep → Bool
  | _, [] => true
  | solved, s :: ss =>
      stepValid j solved s &&
        certificateValidAux j (s.target.elim solved fun i => i :: solved) ss

private def certificateValid (j : Fin 12) (steps : List CertificateStep) : Bool :=
  certificateValidAux j [] steps

private def certificate : (j : Fin 12) → List CertificateStep
  | 0 => [stepVar 6 7 5, stepVar 2 7 4, stepVar 0 7 3, stepVar 1 6 1,
      stepVar 2 6 2, stepVar 0 2 0, stepVar 0 8 6, stepVar 0 10 10,
      stepVar 0 12 7, stepVar 0 13 9, stepVar 1 9 11, stepVar 2 13 8]
  | 1 => [stepVar 6 7 5, stepVar 2 7 4, stepVar 0 7 3, stepVar 2 3 2,
      stepVar 0 3 1, stepVar 0 9 11, stepVar 1 12 7, stepConst 2 8]
  | 2 => [stepVar 1 7 1, stepVar 2 7 2, stepVar 2 6 4, stepVar 0 6 3,
      stepVar 0 4 0, stepVar 0 8 6, stepVar 0 10 10, stepVar 0 12 7,
      stepVar 0 13 9, stepConst 2 4]
  | 3 => [stepVar 1 7 5, stepVar 2 6 4, stepVar 0 6 3, stepVar 2 9 2,
      stepConst 2 10]
  | 4 => [stepVar 1 7 1, stepVar 2 7 2, stepVar 0 5 0, stepVar 0 3 3,
      stepVar 0 9 11, stepConst 2 5]
  | 5 => [stepVar 1 7 5, stepVar 0 4 4, stepVar 0 3 3, stepVar 0 9 11,
      stepVar 0 10 10, stepVar 1 13 9, stepConst 2 11]
  | 6 => [stepVar 1 6 1, stepVar 2 6 2, stepVar 0 5 0, stepVar 2 3 6,
      stepVar 0 11 8, stepVar 0 12 7, stepConst 2 5]
  | 7 => [stepVar 1 6 5, stepVar 0 2 4, stepVar 0 8 6, stepVar 1 12 7,
      stepConst 2 11]
  | 8 => [stepVar 0 4 0, stepVar 0 3 1, stepVar 0 9 11, stepVar 0 10 10,
      stepConst 2 4]
  | 9 => [stepVar 1 3 5, stepVar 1 9 11, stepConst 2 10]
  | 10 => [stepVar 0 2 0, stepVar 0 8 6, stepConst 3 12]
  | 11 => [stepConst 2 8]

private lemma evalSparseTerm_apply_of_valid {R : Type*} [CommRing R]
    (a : Symbol → R) (row col : Nat) (p : MultiPoly)
    (hrow : row < 14) (hcol : col < 14) (i j : Basis) :
    evalSparseTerm a (row, col, p) i j =
      if row = i.val ∧ col = j.val then evalMultiPoly a p else 0 := by
  simp only [evalSparseTerm, hrow, hcol, dif_pos]
  by_cases h : row = i.val ∧ col = j.val
  · rw [if_pos h]
    have hi : (⟨row, hrow⟩ : Basis) = i := Fin.ext h.1
    have hj : (⟨col, hcol⟩ : Basis) = j := Fin.ext h.2
    simp [hi, hj]
  · rw [if_neg h]
    by_cases hi : (⟨row, hrow⟩ : Basis) = i
    · have hcol' : (⟨col, hcol⟩ : Basis) ≠ j := by
        intro hj
        exact h ⟨Fin.ext_iff.mp hi, Fin.ext_iff.mp hj⟩
      simp [hi, hcol']
    · simp [hi]

private lemma evalSparseMatrix_apply_eq_evalSparseEntry
    {R : Type*} [CommRing R] (a : Symbol → R) (A : SparseMultiMatrix)
    (hA : SparseMatrixValid A) (i j : Basis) :
    evalSparseMatrix a A i j = evalMultiPoly a (sparseEntry A i.val j.val) := by
  induction A with
  | nil => simp [evalSparseMatrix, sparseEntry, multiZero, evalMultiPoly]
  | cons e A ih =>
      rcases e with ⟨row, col, p⟩
      have he : row < 14 ∧ col < 14 := hA (row, col, p) (by simp)
      have htail : SparseMatrixValid A := by
        intro f hf
        exact hA f (by simp [hf])
      rw [evalSparseMatrix_cons, Matrix.add_apply,
        evalSparseTerm_apply_of_valid a row col p he.1 he.2 i j,
        ih htail]
      simp only [sparseEntry, List.foldr_cons]
      by_cases h : row = i.val ∧ col = j.val
      · simp only [if_pos h, evalMultiPoly_add]
      · simp only [if_neg h, zero_add]

private lemma evalMultiTerm_zero_of_solved
    {R : Type*} [CommRing R] (a : Symbol → R) (solved : List RootSymbol)
    (t : MultiTerm)
    (hzero : ∀ v ∈ solved, a (rootSymbol v) = 0)
    (hfilter : solved.all
      (fun v => decide (t.exponent (rootSymbol v) = 0)) = false) :
    evalMultiTerm a t = 0 := by
  have hbad : ∃ v ∈ solved, t.exponent (rootSymbol v) ≠ 0 := by
    by_contra h
    push Not at h
    have hall : solved.all
        (fun v => decide (t.exponent (rootSymbol v) = 0)) = true := by
      apply List.all_eq_true.mpr
      intro v hv
      exact decide_eq_true (h v hv)
    rw [hall] at hfilter
    exact Bool.noConfusion hfilter
  obtain ⟨v, hv, hexp⟩ := hbad
  have hpow : a (rootSymbol v) ^ t.exponent (rootSymbol v) = 0 := by
    rw [hzero v hv]
    exact zero_pow hexp
  have hmonomial : evalMonomial a t.exponent = 0 := by
    apply Finset.prod_eq_zero (i := rootSymbol v)
    · exact Finset.mem_univ _
    · exact hpow
  simp [evalMultiTerm, hmonomial]

private lemma evalMultiPoly_zeroVariables
    {R : Type*} [CommRing R] (a : Symbol → R) (solved : List RootSymbol)
    (p : MultiPoly) (hzero : ∀ v ∈ solved, a (rootSymbol v) = 0) :
    evalMultiPoly a (zeroVariables solved p) = evalMultiPoly a p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      simp only [zeroVariables, List.filter_cons]
      by_cases hfilter : solved.all
          (fun v => decide (t.exponent (rootSymbol v) = 0)) = true
      · rw [if_pos hfilter]
        simp only [evalMultiPoly, List.foldr_cons]
        change evalMultiTerm a t + evalMultiPoly a (zeroVariables solved p) =
          evalMultiTerm a t + evalMultiPoly a p
        rw [ih]
      · have hfilterFalse : solved.all
            (fun v => decide (t.exponent (rootSymbol v) = 0)) = false :=
          Bool.eq_false_of_not_eq_true hfilter
        rw [if_neg hfilter]
        simp only [evalMultiPoly, List.foldr_cons]
        change evalMultiPoly a (zeroVariables solved p) =
          evalMultiTerm a t + evalMultiPoly a p
        rw [ih, evalMultiTerm_zero_of_solved a solved t hzero hfilterFalse,
          zero_add]

private lemma sparseMatrixValid_sparseZeroVariables
    (solved : List RootSymbol) (A : SparseMultiMatrix)
    (hA : SparseMatrixValid A) :
    SparseMatrixValid (sparseZeroVariables solved A) := by
  apply sparseMatrixValid_normalize
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  exact hA f hf

private lemma sparseMatrixValid_symbolicBruhatRowSolved
    (j : Fin 12) (solved : List RootSymbol) (row : Basis) :
    SparseMatrixValid (symbolicBruhatRowSolved j solved row) := by
  unfold symbolicBruhatRowSolved
  rw [← List.foldl_map]
  apply sparseMatrixValid_foldl_sparseMul
  · exact sparseMatrixValid_sparseRowOne row
  · intro B hB
    simp only [List.mem_map] at hB
    obtain ⟨C, hC, rfl⟩ := hB
    exact sparseMatrixValid_sparseZeroVariables solved C
      (symbolicBruhatFactors_valid j C hC)

private lemma evalSparseTerm_zeroVariables
    {R : Type*} [CommRing R] (a : Symbol → R)
    (solved : List RootSymbol) (e : Nat × Nat × MultiPoly)
    (hzero : ∀ v ∈ solved, a (rootSymbol v) = 0) :
    evalSparseTerm a (e.1, e.2.1, zeroVariables solved e.2.2) =
      evalSparseTerm a e := by
  rcases e with ⟨i, q, p⟩
  simp only [evalSparseTerm]
  split_ifs
  · rw [evalMultiPoly_zeroVariables a solved p hzero]
  all_goals rfl

private lemma evalSparseMatrix_sparseZeroVariables
    {R : Type*} [CommRing R] (a : Symbol → R)
    (solved : List RootSymbol) (A : SparseMultiMatrix)
    (hzero : ∀ v ∈ solved, a (rootSymbol v) = 0) :
    evalSparseMatrix a (sparseZeroVariables solved A) =
      evalSparseMatrix a A := by
  rw [sparseZeroVariables, evalSparseMatrix_normalize]
  induction A with
  | nil => rfl
  | cons e A ih =>
      simp only [List.map_cons, evalSparseMatrix_cons]
      rw [evalSparseTerm_zeroVariables a solved e hzero, ih]

private lemma evalSparseMatrix_symbolicBruhatRowSolved
    {k : Type*} [Field k]
    (j : Fin 12) (aNeg aPos : Fin 6 → k) (u : TorusParameter k)
    (solved : List RootSymbol)
    (hzero : ∀ v ∈ solved,
      bruhatAssignment aNeg aPos u (rootSymbol v) = 0)
    (row col : Basis) :
    evalSparseMatrix (bruhatAssignment aNeg aPos u)
        (symbolicBruhatRowSolved j solved row) row col =
      bruhatMatrix j aNeg u aPos row col := by
  have hfactors :
      ∀ B ∈ symbolicBruhatFactors j,
        SparseMatrixValid (sparseZeroVariables solved B) := by
    intro B hB
    exact sparseMatrixValid_sparseZeroVariables solved B
      (symbolicBruhatFactors_valid j B hB)
  have hmap :
      (symbolicBruhatFactors j).map
          (fun B => evalSparseMatrix (bruhatAssignment aNeg aPos u)
            (sparseZeroVariables solved B)) =
        (symbolicBruhatFactors j).map
          (evalSparseMatrix (bruhatAssignment aNeg aPos u)) := by
    apply List.map_congr_left
    intro B _
    exact evalSparseMatrix_sparseZeroVariables
      (bruhatAssignment aNeg aPos u) solved B hzero
  have hprod :
      ((symbolicBruhatFactors j).map
        (evalSparseMatrix (bruhatAssignment aNeg aPos u))).prod =
        bruhatMatrix j aNeg u aPos := by
    rw [← evalSparseMatrix_sparseProduct
      (bruhatAssignment aNeg aPos u) (symbolicBruhatFactors j)
      (symbolicBruhatFactors_valid j)]
    exact evalSparseMatrix_symbolicBruhat j aNeg aPos u
  rw [symbolicBruhatRowSolved, ← List.foldl_map,
    evalSparseMatrix_foldl_sparseMul
      (bruhatAssignment aNeg aPos u)
      ((symbolicBruhatFactors j).map
        (sparseZeroVariables solved))
      (sparseRowOne row) (sparseMatrixValid_sparseRowOne row)]
  · rw [evalSparseMatrix_sparseRowOne, List.map_map]
    change ((Matrix.single row row (1 : k) : Matrix Basis Basis k) *
      ((symbolicBruhatFactors j).map (fun B =>
        evalSparseMatrix (bruhatAssignment aNeg aPos u)
          (sparseZeroVariables solved B))).prod) row col = _
    rw [hmap, hprod, Matrix.single_mul_eq_updateRow_zero]
    simp
  · intro B hB
    simp only [List.mem_map] at hB
    obtain ⟨C, hC, rfl⟩ := hB
    exact hfactors C hC

private lemma symbol_eq_root_or_torus (i : Symbol) :
    (∃ r : RootSymbol, i = rootSymbol r) ∨
      ∃ q : Fin 4, i = torusSymbol q := by
  generalize hs :
    (finSumFinEquiv : RootSymbol ⊕ Fin 4 ≃ Symbol).symm i = s
  cases s with
  | inl r =>
      left
      refine ⟨r, ?_⟩
      have h := congrArg (finSumFinEquiv : RootSymbol ⊕ Fin 4 ≃ Symbol) hs
      simpa [rootSymbol] using h
  | inr q =>
      right
      refine ⟨q, ?_⟩
      have h := congrArg (finSumFinEquiv : RootSymbol ⊕ Fin 4 ≃ Symbol) hs
      simpa [torusSymbol] using h

private lemma evalMonomial_ne_zero_of_root_support
    {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (a : Symbol → R) (e : Exponent)
    (hroot : ∀ r : RootSymbol, e (rootSymbol r) ≠ 0 →
      a (rootSymbol r) ≠ 0)
    (htorus : ∀ q : Fin 4, a (torusSymbol q) ≠ 0) :
    evalMonomial a e ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rcases symbol_eq_root_or_torus i with ⟨r, rfl⟩ | ⟨q, rfl⟩
  · by_cases he : e (rootSymbol r) = 0
    · simp [he]
    · exact pow_ne_zero _ (hroot r he)
  · exact pow_ne_zero _ (htorus q)

private lemma intCast_ne_zero_of_one_or_negOne {k : Type*} [Field k]
    (c : Int) (hc : c = 1 ∨ c = -1) : (c : k) ≠ 0 := by
  rcases hc with rfl | rfl <;> norm_num

private lemma bruhatAssignment_torus_ne_zero {k : Type*} [Field k]
    (aNeg aPos : Fin 6 → k) (u : TorusParameter k) (q : Fin 4) :
    bruhatAssignment aNeg aPos u (torusSymbol q) ≠ 0 := by
  fin_cases q <;> simp [bruhatAssignment_torus]

private lemma exponent_zero_of_all_roots_zero (t : MultiTerm)
    (hall : ((List.finRange 12).all fun i =>
      decide (t.exponent (rootSymbol i) = 0)) = true)
    (r : RootSymbol) : t.exponent (rootSymbol r) = 0 := by
  have hr := List.all_eq_true.mp hall r (by simp)
  exact of_decide_eq_true hr

private lemma exponent_zero_of_all_roots_except (t : MultiTerm)
    (v : RootSymbol)
    (hall : ((List.finRange 12).all fun i =>
      decide (i = v.val ∨ t.exponent (rootSymbol ⟨i, by omega⟩) = 0)) = true)
    (r : RootSymbol) (hrv : r ≠ v) :
    t.exponent (rootSymbol r) = 0 := by
  have hr := List.all_eq_true.mp hall r (by simp)
  have hor : r.val = v.val ∨
      t.exponent (rootSymbol ⟨r.val, by omega⟩) = 0 :=
    of_decide_eq_true hr
  rcases hor with heq | hz
  · exact False.elim (hrv (Fin.ext heq))
  · simpa only [Fin.ext_iff] using hz


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem certificate_valid_all :
        ∀ j : Fin 12, certificateValid j (certificate j) = true := by
  intro j
  fin_cases j <;> rfl

private theorem certificate_valid (j : Fin 12) :
    certificateValid j (certificate j) = true :=
  certificate_valid_all j

private lemma certificateStep_sound {k : Type*} [Field k]
    (j : Fin 12) (aNeg aPos : Fin 6 → k) (u : TorusParameter k)
    (solved : List RootSymbol) (s : CertificateStep)
    (hvalid : stepValid j solved s = true)
    (hzero : ∀ v ∈ solved,
      bruhatAssignment aNeg aPos u (rootSymbol v) = 0)
    (hdiag : ∀ i q : Basis, basisWeight i ≠ basisWeight q →
      bruhatMatrix j aNeg u aPos i q = 0) :
    match s.target with
    | some v => bruhatAssignment aNeg aPos u (rootSymbol v) = 0
    | none => False := by
  unfold stepValid at hvalid
  have hpairs := hvalid
  simp only [Bool.and_eq_true] at hpairs
  have hweight' : centralizerBasisWeight s.row ≠
      centralizerBasisWeight s.col := of_decide_eq_true hpairs.1
  have hweight : basisWeight s.row ≠ basisWeight s.col := by
    rw [← centralizerBasisWeight_eq, ← centralizerBasisWeight_eq]
    exact hweight'
  generalize hpoly : normalizeMultiPoly
      (sparseEntry (symbolicBruhatRowSolved j solved s.row)
        s.row.val s.col.val) = p at hpairs
  cases p with
  | nil => simp at hpairs
  | cons t rest =>
    cases rest with
    | cons t' rest => simp at hpairs
    | nil =>
      have hterm := hpairs.2
      simp only [Bool.and_eq_true] at hterm
      have hcoeff : t.coefficient = 1 ∨ t.coefficient = -1 :=
        of_decide_eq_true hterm.1
      have hA : SparseMatrixValid
          (symbolicBruhatRowSolved j solved s.row) :=
        sparseMatrixValid_symbolicBruhatRowSolved j solved s.row
      have hmatrix := hdiag s.row s.col hweight
      rw [← evalSparseMatrix_symbolicBruhatRowSolved
        j aNeg aPos u solved hzero s.row s.col] at hmatrix
      rw [evalSparseMatrix_apply_eq_evalSparseEntry
        (bruhatAssignment aNeg aPos u)
        (symbolicBruhatRowSolved j solved s.row) hA] at hmatrix
      have hzeroed : evalMultiPoly (bruhatAssignment aNeg aPos u)
          (sparseEntry (symbolicBruhatRowSolved j solved s.row)
            s.row.val s.col.val) = 0 :=
        hmatrix
      have hnormalized : evalMultiPoly (bruhatAssignment aNeg aPos u)
          (normalizeMultiPoly
            (sparseEntry (symbolicBruhatRowSolved j solved s.row)
              s.row.val s.col.val)) = 0 := by
        rw [evalMultiPoly_normalize]
        exact hzeroed
      rw [hpoly] at hnormalized
      simp only [evalMultiPoly, List.foldr_cons, List.foldr_nil, add_zero]
        at hnormalized
      cases hs : s.target with
      | none =>
        simp only [hs] at hterm ⊢
        have hroot : ∀ r : RootSymbol,
            t.exponent (rootSymbol r) ≠ 0 →
              bruhatAssignment aNeg aPos u (rootSymbol r) ≠ 0 := by
          intro r hr
          exact False.elim
            (hr (exponent_zero_of_all_roots_zero t hterm.2 r))
        have hmonomial := evalMonomial_ne_zero_of_root_support
          (bruhatAssignment aNeg aPos u) t.exponent hroot
          (bruhatAssignment_torus_ne_zero aNeg aPos u)
        exact (mul_ne_zero
          (intCast_ne_zero_of_one_or_negOne _ hcoeff) hmonomial) hnormalized
      | some v =>
        simp only [hs] at hterm ⊢
        have htargetParts := hterm.2
        simp only [Bool.and_eq_true] at htargetParts
        by_contra hv
        have hroot : ∀ r : RootSymbol,
            t.exponent (rootSymbol r) ≠ 0 →
              bruhatAssignment aNeg aPos u (rootSymbol r) ≠ 0 := by
          intro r hr
          by_cases hrv : r = v
          · subst r
            exact hv
          · exact False.elim
              (hr (exponent_zero_of_all_roots_except t v htargetParts.2 r hrv))
        have hmonomial := evalMonomial_ne_zero_of_root_support
          (bruhatAssignment aNeg aPos u) t.exponent hroot
          (bruhatAssignment_torus_ne_zero aNeg aPos u)
        exact (mul_ne_zero
          (intCast_ne_zero_of_one_or_negOne _ hcoeff) hmonomial) hnormalized

private lemma certificateValidAux_targets_zero {k : Type*} [Field k]
    (j : Fin 12) (aNeg aPos : Fin 6 → k) (u : TorusParameter k)
    (solved : List RootSymbol) (steps : List CertificateStep)
    (hvalid : certificateValidAux j solved steps = true)
    (hzero : ∀ v ∈ solved,
      bruhatAssignment aNeg aPos u (rootSymbol v) = 0)
    (hdiag : ∀ i q : Basis, basisWeight i ≠ basisWeight q →
      bruhatMatrix j aNeg u aPos i q = 0) :
    ∀ s ∈ steps, ∃ v, s.target = some v ∧
      bruhatAssignment aNeg aPos u (rootSymbol v) = 0 := by
  induction steps generalizing solved with
  | nil => simp
  | cons s steps ih =>
    simp only [certificateValidAux, Bool.and_eq_true] at hvalid
    have hs := certificateStep_sound j aNeg aPos u solved s
      hvalid.1 hzero hdiag
    cases ht : s.target with
    | none => simp [ht] at hs
    | some v =>
      simp only [ht] at hs
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨v, ht, hs⟩
      · apply ih (v :: solved) (by simpa [ht] using hvalid.2)
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact hs
          · exact hzero w hw
        · exact hq

private theorem bruhatMatrix_separation {k : Type*} [Field k]
    (j : Fin 12) (aNeg aPos : Fin 6 → k) (u : TorusParameter k)
    (hdiag : ∀ i q : Basis, basisWeight i ≠ basisWeight q →
      bruhatMatrix j aNeg u aPos i q = 0) :
    j = 0 ∧ (∀ i, aNeg i = 0) ∧ ∀ i, aPos i = 0 := by
  have hvalid := certificate_valid j
  unfold certificateValid at hvalid
  have hall := certificateValidAux_targets_zero j aNeg aPos u
    [] (certificate j) hvalid (by simp) hdiag
  have hnoConst : ∀ s ∈ certificate j, s.target ≠ none := by
    intro s hs hnone
    obtain ⟨v, hv, _⟩ := hall s hs
    rw [hnone] at hv
    simp at hv
  have hj : j = 0 := by
    fin_cases j <;> simp [certificate, stepConst] at hnoConst ⊢
  subst j
  have hroot : ∀ v : RootSymbol,
      bruhatAssignment aNeg aPos u (rootSymbol v) = 0 := by
    intro v
    have hv : ∃ s ∈ certificate (0 : Fin 12), s.target = some v := by
      fin_cases v <;> simp [certificate, stepVar]
    obtain ⟨s, hs, htarget⟩ := hv
    obtain ⟨w, hw, hzero⟩ := hall s hs
    have hwv : w = v := Option.some.inj (hw.symm.trans htarget)
    subst w
    exact hzero
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    rw [← bruhatAssignment_negative aNeg aPos u i]
    exact hroot (negativeSlot i)
  · intro i
    rw [← bruhatAssignment_positive aNeg aPos u i]
    exact hroot (positiveSlot i)

private noncomputable def carrierGL {k : Type*} [Field k] [IsAlgClosed k]
    (x : CarrierPoint (k := k)) :
    LinearMap.GeneralLinearGroup k (Basis → k) :=
  glPointEquivOf k (Basis → k) (carrierBasis (k := k))
    ((ambientClosedCarrier (k := k)).inclusion.onPoints x)

private lemma glPointEquivOf_mul {k : Type*} [Field k] [IsAlgClosed k]
    (x y : Variety.Point (Ambient k)) :
    glPointEquivOf k (Basis → k) (carrierBasis (k := k)) (x * y) =
      glPointEquivOf k (Basis → k) (carrierBasis (k := k)) x *
        glPointEquivOf k (Basis → k) (carrierBasis (k := k)) y := by
  let e := glPointEquivOf k (Basis → k) (carrierBasis (k := k))
  have hx : x = generalLinearRepresentationPoint (carrierBasis (k := k)) (e x) := by
    apply e.injective
    exact (glPointEquivOf_generalLinearRepresentationPoint
      (carrierBasis (k := k)) (e x)).symm
  have hy : y = generalLinearRepresentationPoint (carrierBasis (k := k)) (e y) := by
    apply e.injective
    exact (glPointEquivOf_generalLinearRepresentationPoint
      (carrierBasis (k := k)) (e y)).symm
  rw [hx, hy, ← generalLinearRepresentationPoint_mul,
    glPointEquivOf_generalLinearRepresentationPoint]
  have hx' : glPointEquivOf k (Basis → k) (carrierBasis (k := k))
      (generalLinearRepresentationPoint (carrierBasis (k := k)) (e x)) = e x :=
    glPointEquivOf_generalLinearRepresentationPoint (carrierBasis (k := k)) (e x)
  have hy' : glPointEquivOf k (Basis → k) (carrierBasis (k := k))
      (generalLinearRepresentationPoint (carrierBasis (k := k)) (e y)) = e y :=
    glPointEquivOf_generalLinearRepresentationPoint (carrierBasis (k := k)) (e y)
  rw [hx', hy']

private lemma glPointEquivOf_one {k : Type*} [Field k] [IsAlgClosed k] :
    glPointEquivOf k (Basis → k) (carrierBasis (k := k))
        (1 : Variety.Point (Ambient k)) = 1 := by
  rw [show (1 : Variety.Point (Ambient k)) =
      generalLinearRepresentationPoint (carrierBasis (k := k)) 1 by
    rw [generalLinearRepresentationPoint_one]]
  exact glPointEquivOf_generalLinearRepresentationPoint (carrierBasis (k := k)) 1

private noncomputable def carrierGLHom {k : Type*} [Field k] [IsAlgClosed k] :
    CarrierPoint (k := k) →* LinearMap.GeneralLinearGroup k (Basis → k) where
  toFun := carrierGL
  map_one' := by
    rw [carrierGL, map_one, glPointEquivOf_one]
  map_mul' := by
    intro x y
    rw [carrierGL, map_mul, glPointEquivOf_mul]
    rfl

private noncomputable def carrierMatrix {k : Type*} [Field k] [IsAlgClosed k]
    (x : CarrierPoint (k := k)) : Matrix Basis Basis k :=
  LinearMap.toMatrix (Pi.basisFun k Basis) (Pi.basisFun k Basis)
    ((carrierGLHom (k := k) x : LinearMap.GeneralLinearGroup k (Basis → k)) :
      Module.End k (Basis → k))

private lemma carrierMatrix_mul {k : Type*} [Field k] [IsAlgClosed k]
    (x y : CarrierPoint (k := k)) :
    carrierMatrix (x * y) = carrierMatrix x * carrierMatrix y := by
  simp only [carrierMatrix, map_mul]
  exact LinearMap.toMatrix_mul (Pi.basisFun k Basis) _ _

private lemma carrierMatrix_one {k : Type*} [Field k] [IsAlgClosed k] :
    carrierMatrix (1 : CarrierPoint (k := k)) = 1 := by
  simp [carrierMatrix]

private lemma carrierGL_rootFactor {k : Type*} [Field k] [IsAlgClosed k]
    (r : Root) (a : k) :
    carrierGLHom (k := k) (carrierRootFactor r a) =
      Matrix.GeneralLinearGroup.toLin (rootCurveUnit r a) := by
  change carrierGL (carrierRootFactor r a) = _
  simp only [carrierGL, carrierRootFactor]
  rw [rootMorphism_inclusion_apply, rootAmbientMorphism_apply,
    glPointEquivOf_generalLinearRepresentationPoint]
  rfl

private lemma carrierMatrix_rootFactor {k : Type*} [Field k] [IsAlgClosed k]
    (r : Root) (a : k) :
    carrierMatrix (k := k) (carrierRootFactor r a) = rootCurve r a := by
  simp only [carrierMatrix, carrierGL_rootFactor]
  ext i j
  simp [rootCurveUnit]

private noncomputable def weylWordUnit {k : Type*} [Field k]
    (w : List (Fin 2)) : (Matrix Basis Basis k)ˣ :=
  (w.map fun i => weylMatrixUnit (R := k) i).prod

private lemma carrierGL_weylRepresentative {k : Type*} [Field k] [IsAlgClosed k]
    (i : Fin 2) :
    carrierGLHom (k := k) (carrierWeylRepresentative i) =
      Matrix.GeneralLinearGroup.toLin (weylMatrixUnit (R := k) i) := by
  change carrierGL (carrierWeylRepresentative i) = _
  simp only [carrierGL]
  rw [carrierWeylRepresentative_ambient_matrix,
    glPointEquivOf_generalLinearRepresentationPoint]

private lemma carrierGL_weylWord {k : Type*} [Field k] [IsAlgClosed k]
    (w : List (Fin 2)) :
    carrierGLHom (k := k) (carrierWeylWord w) =
      Matrix.GeneralLinearGroup.toLin (weylWordUnit (k := k) w) := by
  induction w with
  | nil => simp [carrierWeylWord, weylWordUnit]
  | cons i w ih =>
      rw [carrierWeylWord, map_mul, carrierGL_weylRepresentative, ih]
      simp [weylWordUnit, map_mul]

private lemma carrierMatrix_weylWord {k : Type*} [Field k] [IsAlgClosed k]
    (w : List (Fin 2)) :
    carrierMatrix (k := k) (carrierWeylWord w) = (weylWordUnit (k := k) w : _) := by
  simp only [carrierMatrix, carrierGL_weylWord]
  ext i j
  simp

private lemma carrierGL_splitTorus {k : Type*} [Field k] [IsAlgClosed k]
    (t : Variety.Point (dVariety k 2)) :
    carrierGLHom (k := k) ((splitTorusMorphism (k := k)).onPoints t) =
      Matrix.GeneralLinearGroup.toLin (torusElement (dPointEquiv 2 t)) := by
  change carrierGL ((splitTorusMorphism (k := k)).onPoints t) = _
  simp only [carrierGL]
  rw [splitTorusMorphism_inclusion_apply, torusAmbientMorphism_apply,
    glPointEquivOf_generalLinearRepresentationPoint]
  rfl

private lemma carrierMatrix_splitTorus {k : Type*} [Field k] [IsAlgClosed k]
    (t : Variety.Point (dVariety k 2)) :
    carrierMatrix ((splitTorusMorphism (k := k)).onPoints t) =
      (torusElement (dPointEquiv 2 t) : Matrix Basis Basis k) := by
  simp only [carrierMatrix, carrierGL_splitTorus]
  ext i j
  simp

private def rootProductMatrix {k : Type*} [Field k]
    (roots : Fin 6 → Root) (a : Fin 6 → k) : Matrix Basis Basis k :=
  (([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun i => rootCurve (roots i) (a i)).prod

private lemma carrierMatrix_rootWordProduct {k : Type*} [Field k] [IsAlgClosed k]
    (roots : Fin 6 → Root) (a : Fin 6 → k) :
    carrierMatrix (carrierRootWordProduct
      ((([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun i => (roots i, a i)))) =
      rootProductMatrix roots a := by
  simp [carrierRootWordProduct, rootProductMatrix, carrierMatrix_mul,
    carrierMatrix_rootFactor]

private lemma carrierMatrix_negativeRootProduct {k : Type*}
    [Field k] [IsAlgClosed k] (a : Fin 6 → k) :
    carrierMatrix (carrierNegativeRootProduct (k := k) a) =
      rootProductMatrix negativeRoot a := by
  have hroots : (fun i => -positiveConvexRoot i) = negativeRoot := by
    funext i
    fin_cases i <;> rfl
  rw [← hroots]
  simpa [carrierNegativeRootProduct, carrierRootWordProduct] using
    (carrierMatrix_rootWordProduct (k := k)
      (fun i => -positiveConvexRoot i) a)

private lemma carrierMatrix_positiveRootProduct {k : Type*}
    [Field k] [IsAlgClosed k] (a : Fin 6 → k) :
    carrierMatrix (carrierPositiveRootProduct (k := k) a) =
      rootProductMatrix positiveRoot a := by
  have hroots : positiveConvexRoot = positiveRoot := by
    funext i
    fin_cases i <;> rfl
  rw [← hroots]
  exact carrierMatrix_rootWordProduct positiveConvexRoot a

private def basisTorusExponent (b : Basis) : Fin 2 → ℤ :=
  fun i => -basisWeight b i

private lemma basisTorusUnit_dLaurentCharacter_apply {k : Type*}
    [Field k] [IsAlgClosed k]
    (x : Variety.Point (dVariety k 2)) (b : Basis) :
    dPointEquiv 1 ((dLaurentCharacter 2 (basisTorusExponent b)).onPoints x) 0 =
      (basisTorusUnit (dPointEquiv 2 x) b : k) := by
  rw [dLaurentCharacter_apply]
  rfl

private lemma basisTorusUnit_separate {k : Type*} [Field k] [IsAlgClosed k]
    {p q : Basis} (hpq : basisWeight p ≠ basisWeight q) :
    ∃ x : Variety.Point (dVariety k 2),
      (basisTorusUnit (dPointEquiv 2 x) p : k) ≠
        (basisTorusUnit (dPointEquiv 2 x) q : k) := by
  by_contra hnone
  push Not at hnone
  have hchars :
      dLaurentCharacter (k := k) 2 (basisTorusExponent p) =
        dLaurentCharacter 2 (basisTorusExponent q) := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    apply (dPointEquiv 1).injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    apply Units.ext
    exact (basisTorusUnit_dLaurentCharacter_apply x p).trans
      ((hnone x).trans (basisTorusUnit_dLaurentCharacter_apply x q).symm)
  have hexp := dLaurentCharacter_injective (k := k) 2 hchars
  apply hpq
  funext i
  have hi := congrFun hexp i
  simp only [basisTorusExponent, neg_inj] at hi
  exact hi

private lemma centralizer_matrix_offWeight_zero {k : Type*}
    [Field k] [IsAlgClosed k]
    (g : CarrierPoint (k := k))
    (hg : g ∈ (splitTorus (k := k)).centralizer.toSubgroup)
    (p q : Basis) (hpq : basisWeight p ≠ basisWeight q) :
    carrierMatrix g p q = 0 := by
  obtain ⟨x, hx⟩ := basisTorusUnit_separate (k := k) hpq
  have htx : (splitTorusMorphism (k := k)).onPoints x ∈
      (splitTorus (k := k)).toSubgroup := ⟨x, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hg _ htx
  have hmatrix := congrArg carrierMatrix hcomm
  rw [carrierMatrix_mul, carrierMatrix_mul, carrierMatrix_splitTorus] at hmatrix
  have hentry := congrFun (congrFun hmatrix p) q
  simp only [torusElement, Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
  have hfactor :
      ((basisTorusUnit (dPointEquiv 2 x) p : k) -
          (basisTorusUnit (dPointEquiv 2 x) q : k)) * carrierMatrix g p q = 0 := by
    rw [sub_mul, mul_comm (basisTorusUnit (dPointEquiv 2 x) q : k)]
    exact sub_eq_zero.mpr hentry
  exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hx)

private lemma weylWordUnit_coe {k : Type*} [Field k] (w : List (Fin 2)) :
    (weylWordUnit (k := k) w : Matrix Basis Basis k) =
      (w.map fun i => specialize (R := k) (weyl i)).prod := by
  induction w with
  | nil => simp [weylWordUnit]
  | cons i w ih =>
      simp only [List.map_cons, List.prod_cons]
      change (↑(weylMatrixUnit (R := k) i * weylWordUnit (k := k) w) :
          Matrix Basis Basis k) = _
      rw [Units.val_mul, ih]
      rfl

private lemma carrierMatrix_bruhatCellPoint {k : Type*}
    [Field k] [IsAlgClosed k] (j : Fin 12)
    (z : Variety.Point (BruhatCellDomain k)) :
    carrierMatrix (bruhatCellPoint (k := k) j z) =
      bruhatMatrix j (bruhatCellNegativeParameters (k := k) z)
        (dPointEquiv 2 (bruhatCellTorusParameter (k := k) z))
        (bruhatCellPositiveParameters (k := k) z) := by
  simp only [bruhatCellPoint, carrierMatrix_mul, carrierMatrix_negativeRootProduct,
    carrierMatrix_weylWord, carrierMatrix_splitTorus,
    carrierMatrix_positiveRootProduct]
  unfold bruhatMatrix bruhatMatrixFactors rootProductMatrix
  simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  simp [mul_assoc, weylWordUnit_coe]

private theorem centralizing_bruhatCellPoint_mem_splitTorus {k : Type*}
    [Field k] [IsAlgClosed k] (j : Fin 12)
    (z : Variety.Point (BruhatCellDomain k))
    (hg : bruhatCellPoint (k := k) j z ∈
      (splitTorus (k := k)).centralizer.toSubgroup) :
    bruhatCellPoint (k := k) j z ∈ (splitTorus (k := k)).toSubgroup := by
  let aNeg := bruhatCellNegativeParameters (k := k) z
  let aPos := bruhatCellPositiveParameters (k := k) z
  let u := dPointEquiv 2 (bruhatCellTorusParameter (k := k) z)
  have hmatrix : carrierMatrix (bruhatCellPoint (k := k) j z) =
      bruhatMatrix j aNeg u aPos := by
    exact carrierMatrix_bruhatCellPoint j z
  have hdiag : ∀ p q : Basis, basisWeight p ≠ basisWeight q →
      bruhatMatrix j aNeg u aPos p q = 0 := by
    intro p q hpq
    rw [← hmatrix]
    exact centralizer_matrix_offWeight_zero _ hg p q hpq
  obtain ⟨hj, hNeg, hPos⟩ :=
    bruhatMatrix_separation j aNeg aPos u hdiag
  subst j
  have hNeg' : aNeg = 0 := funext hNeg
  have hPos' : aPos = 0 := funext hPos
  have hkzero : kPlusPoint (0 : k) = 1 := by
    apply (additiveGroupPointEquiv k).injective
    rfl
  refine ⟨bruhatCellTorusParameter (k := k) z, ?_⟩
  simp [bruhatCellPoint, aNeg, aPos, hNeg', hPos',
    carrierNegativeRootProduct, carrierPositiveRootProduct,
    carrierRootFactor, carrierWeylWord,
    canonicalWeylWord, hkzero]

/-- The centralizer of the explicit split torus in the closed integral `G2`
Chevalley carrier is the split torus itself, in every characteristic. -/
public theorem splitTorus_centralizer_eq {k : Type*} [Field k] [IsAlgClosed k] :
    (splitTorus (k := k)).centralizer.toSubgroup =
      (splitTorus (k := k)).toSubgroup := by
  ext g
  constructor
  · intro hg
    obtain ⟨j, z, hz⟩ := carrier_bruhatCell_cover (k := k) g
    rw [hz, bruhatCellMorphism_apply] at hg ⊢
    exact centralizing_bruhatCellPoint_mem_splitTorus j z hg
  · intro hg
    change g ∈ Subgroup.centralizer
      ((splitTorus (k := k)).toSubgroup : Set (CarrierPoint (k := k)))
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    let T := splitTorus (k := k)
    let _ := T.carrierAlgebraicGroup
    let gt : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨g, hg⟩
    let tt : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨t, ht⟩
    have hcomm := (splitTorus_isSubtorus (k := k)).isMulCommutative
    rw [isMulCommutative_iff] at hcomm
    have hamb := congrArg T.inclusion.onPoints (hcomm tt gt)
    have htt : T.inclusion.onPoints tt = t := by
      change (T.pointEquiv tt).val = t
      dsimp only [tt]
      rw [T.pointEquiv.apply_symm_apply]
    have hgt : T.inclusion.onPoints gt = g := by
      change (T.pointEquiv gt).val = g
      dsimp only [gt]
      rw [T.pointEquiv.apply_symm_apply]
    simpa only [map_mul, htt, hgt] using hamb

end Theory.AlgebraicGroup.G2Chevalley
