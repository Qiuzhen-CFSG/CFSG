module

public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyRootCurves

/-!
# Explicit G2 root-curve commutator tables

This module records the characteristic-free collection table for the twelve
root curves in the explicit integral `G2` Chevalley representation.  For two
non-equal, non-opposite roots `r` and `s`, `rootCurveCommutatorTerms r s`
is the correction word in

`x_r(a) x_s(b) = x_s(b) x_r(a) correction`.

Each correction parameter is an integral monomial `c * a^i * b^j`, so the
data specialize uniformly in characteristics two and three.  The public
checker evaluates both sides in a small computable two-variable integral
polynomial model built directly from the sparse divided-power matrices of
`G2ChevalleyRepresentation`; no division or source-level root classification
is involved.  The same-root collection relation is supplied as an actual unit
identity from the cubic root-curve addition law, while opposite-root exchanges
are intentionally left to the separate Weyl-lift/rank-one Bruhat identities.

The ordered correction table is the matrix input needed by the later explicit
Bruhat cover: arbitrary words can use these adjacent swaps, together with the
torus conjugation package from `G2ChevalleyRootCurves`, to move non-opposite
root generators toward negative-root, split-torus, positive-root order.
-/

open scoped Matrix

namespace Theory.AlgebraicGroup.G2Chevalley

@[expose] public section

/-- One correction factor in a two-root collection relation. -/
public structure RootCurveCommutatorTerm where
  root : Root
  leftPower : ℕ
  rightPower : ℕ
  coeff : ℤ
  deriving DecidableEq, Repr

public def mkTerm (root : Root) (leftPower rightPower : ℕ) (coeff : ℤ) :
    RootCurveCommutatorTerm where
  root := root
  leftPower := leftPower
  rightPower := rightPower
  coeff := coeff

/-- The fixed positive-root order used by the collection table. -/
public def rootCurvePositiveOrder : List Root :=
  [Root.short, Root.long, Root.shortLong, Root.twoShortLong,
    Root.threeShortLong, Root.threeShortTwoLong]

/-- The fixed negative-root order used by the collection table. -/
public def rootCurveNegativeOrder : List Root :=
  [Root.negShort, Root.negLong, Root.negShortLong, Root.negTwoShortLong,
    Root.negThreeShortLong, Root.negThreeShortTwoLong]

/-- Ordered correction words for swapping `x_r(a)` past `x_s(b)`.

The empty word is used when no mixed root occurs, and also for equal or
opposite roots; the latter require the separate rank-one Bruhat exchange
package rather than a pure commutator correction word. -/
public def rootCurveCommutatorTerms : Root → Root → List RootCurveCommutatorTerm
  | 0, 1 => [mkTerm 2 1 1 1, mkTerm 3 2 1 (-1), mkTerm 4 3 1 (-1),
      mkTerm 5 3 2 (-2)]
  | 0, 2 => [mkTerm 3 1 1 2, mkTerm 5 1 2 3, mkTerm 4 2 1 3]
  | 0, 3 => [mkTerm 4 1 1 (-3)]
  | 0, 8 => [mkTerm 7 1 1 (-3)]
  | 0, 9 => [mkTerm 8 1 1 (-2), mkTerm 11 1 2 3, mkTerm 7 2 1 (-3)]
  | 0, 10 => [mkTerm 9 1 1 1, mkTerm 8 2 1 1, mkTerm 7 3 1 1,
      mkTerm 11 3 2 (-2)]
  | 1, 0 => [mkTerm 2 1 1 (-1), mkTerm 3 1 2 1, mkTerm 4 1 3 1,
      mkTerm 5 2 3 (-1)]
  | 1, 4 => [mkTerm 5 1 1 (-1)]
  | 1, 8 => [mkTerm 6 1 1 1, mkTerm 9 1 2 1, mkTerm 11 1 3 1,
      mkTerm 10 2 3 1]
  | 1, 11 => [mkTerm 10 1 1 1]
  | 2, 0 => [mkTerm 3 1 1 (-2), mkTerm 4 1 2 (-3), mkTerm 5 2 1 (-3)]
  | 2, 3 => [mkTerm 5 1 1 (-3)]
  | 2, 6 => [mkTerm 1 1 1 3]
  | 2, 7 => [mkTerm 0 1 1 (-1), mkTerm 3 2 1 (-1), mkTerm 5 3 1 (-1),
      mkTerm 4 3 2 2]
  | 2, 9 => [mkTerm 6 1 1 2, mkTerm 10 1 2 (-3), mkTerm 1 2 1 (-3)]
  | 2, 11 => [mkTerm 9 1 1 1, mkTerm 6 2 1 (-1), mkTerm 1 3 1 1,
      mkTerm 10 3 2 2]
  | 3, 0 => [mkTerm 4 1 1 3]
  | 3, 2 => [mkTerm 5 1 1 3]
  | 3, 6 => [mkTerm 2 1 1 2, mkTerm 1 1 2 3, mkTerm 5 2 1 (-3)]
  | 3, 8 => [mkTerm 0 1 1 (-2), mkTerm 7 1 2 3, mkTerm 4 2 1 3]
  | 3, 10 => [mkTerm 6 1 1 (-1), mkTerm 2 2 1 1, mkTerm 5 3 1 (-1),
      mkTerm 1 3 2 (-2)]
  | 3, 11 => [mkTerm 8 1 1 (-1), mkTerm 0 2 1 (-1), mkTerm 4 3 1 1,
      mkTerm 7 3 2 (-2)]
  | 4, 1 => [mkTerm 5 1 1 1]
  | 4, 6 => [mkTerm 3 1 1 (-1), mkTerm 2 1 2 (-1), mkTerm 1 1 3 (-1),
      mkTerm 5 2 3 (-1)]
  | 4, 9 => [mkTerm 0 1 1 1, mkTerm 8 1 2 (-1), mkTerm 11 1 3 1,
      mkTerm 7 2 3 (-1)]
  | 4, 11 => [mkTerm 7 1 1 (-1)]
  | 5, 7 => [mkTerm 4 1 1 (-1)]
  | 5, 8 => [mkTerm 3 1 1 (-1), mkTerm 0 1 2 1, mkTerm 7 1 3 (-1),
      mkTerm 4 2 3 1]
  | 5, 9 => [mkTerm 2 1 1 1, mkTerm 6 1 2 1, mkTerm 10 1 3 (-1),
      mkTerm 1 2 3 (-1)]
  | 5, 10 => [mkTerm 1 1 1 1]
  | 6, 2 => [mkTerm 1 1 1 (-3)]
  | 6, 3 => [mkTerm 2 1 1 (-2), mkTerm 5 1 2 3, mkTerm 1 2 1 (-3)]
  | 6, 4 => [mkTerm 3 1 1 1, mkTerm 2 2 1 1, mkTerm 1 3 1 1,
      mkTerm 5 3 2 (-2)]
  | 6, 7 => [mkTerm 8 1 1 1, mkTerm 9 2 1 (-1), mkTerm 10 3 1 (-1),
      mkTerm 11 3 2 (-2)]
  | 6, 8 => [mkTerm 9 1 1 2, mkTerm 11 1 2 3, mkTerm 10 2 1 3]
  | 6, 9 => [mkTerm 10 1 1 (-3)]
  | 7, 2 => [mkTerm 0 1 1 1, mkTerm 3 1 2 1, mkTerm 5 1 3 1,
      mkTerm 4 2 3 1]
  | 7, 5 => [mkTerm 4 1 1 1]
  | 7, 6 => [mkTerm 8 1 1 (-1), mkTerm 9 1 2 1, mkTerm 10 1 3 1,
      mkTerm 11 2 3 (-1)]
  | 7, 10 => [mkTerm 11 1 1 (-1)]
  | 8, 0 => [mkTerm 7 1 1 3]
  | 8, 1 => [mkTerm 6 1 1 (-1), mkTerm 9 2 1 (-1), mkTerm 11 3 1 (-1),
      mkTerm 10 3 2 2]
  | 8, 3 => [mkTerm 0 1 1 2, mkTerm 4 1 2 (-3), mkTerm 7 2 1 (-3)]
  | 8, 5 => [mkTerm 3 1 1 1, mkTerm 0 2 1 (-1), mkTerm 7 3 1 1,
      mkTerm 4 3 2 2]
  | 8, 6 => [mkTerm 9 1 1 (-2), mkTerm 10 1 2 (-3), mkTerm 11 2 1 (-3)]
  | 8, 9 => [mkTerm 11 1 1 (-3)]
  | 9, 0 => [mkTerm 8 1 1 2, mkTerm 7 1 2 3, mkTerm 11 2 1 (-3)]
  | 9, 2 => [mkTerm 6 1 1 (-2), mkTerm 1 1 2 3, mkTerm 10 2 1 3]
  | 9, 4 => [mkTerm 0 1 1 (-1), mkTerm 8 2 1 1, mkTerm 11 3 1 (-1),
      mkTerm 7 3 2 (-2)]
  | 9, 5 => [mkTerm 2 1 1 (-1), mkTerm 6 2 1 (-1), mkTerm 10 3 1 1,
      mkTerm 1 3 2 (-2)]
  | 9, 6 => [mkTerm 10 1 1 3]
  | 9, 8 => [mkTerm 11 1 1 3]
  | 10, 0 => [mkTerm 9 1 1 (-1), mkTerm 8 1 2 (-1), mkTerm 7 1 3 (-1),
      mkTerm 11 2 3 (-1)]
  | 10, 3 => [mkTerm 6 1 1 1, mkTerm 2 1 2 (-1), mkTerm 5 1 3 1,
      mkTerm 1 2 3 (-1)]
  | 10, 5 => [mkTerm 1 1 1 (-1)]
  | 10, 7 => [mkTerm 11 1 1 1]
  | 11, 1 => [mkTerm 10 1 1 (-1)]
  | 11, 2 => [mkTerm 9 1 1 (-1), mkTerm 6 1 2 1, mkTerm 1 1 3 (-1),
      mkTerm 10 2 3 1]
  | 11, 3 => [mkTerm 8 1 1 1, mkTerm 0 1 2 1, mkTerm 4 1 3 (-1),
      mkTerm 7 2 3 (-1)]
  | 11, 4 => [mkTerm 7 1 1 1]
  | _, _ => []

/-- The field element attached to one correction factor. -/
public def rootCurveTermParameter {R : Type*} [CommRing R] (a b : R)
    (q : RootCurveCommutatorTerm) : R :=
  (q.coeff : R) * a ^ q.leftPower * b ^ q.rightPower

/-- The unit-valued correction word attached to an ordered pair of roots. -/
public def rootCurveCorrectionWord {R : Type*} [CommRing R] (r s : Root)
    (a b : R) : (Matrix Basis Basis R)ˣ :=
  (rootCurveCommutatorTerms r s).map
      (fun q => rootCurveUnit q.root (rootCurveTermParameter a b q)) |>.prod

/-- The intended swap relation represented by the correction table. -/
public def rootCurveSwapRelation {R : Type*} [CommRing R] (r s : Root)
    (a b : R) : Prop :=
  rootCurveUnit r a * rootCurveUnit s b =
    rootCurveUnit s b * rootCurveUnit r a *
      rootCurveCorrectionWord r s a b

/-- Same-root collection is ordinary addition of root-curve parameters. -/
public theorem rootCurveUnit_same_root_collection {R : Type*} [CommRing R]
    (r : Root) (a b : R) :
    rootCurveUnit r a * rootCurveUnit r b = rootCurveUnit r (a + b) := by
  apply Units.ext
  exact (rootCurve_add r a b).symm

public abbrev BiPoly := List (ℕ × ℕ × ℤ)

public def monomialLess (i j i' j' : ℕ) : Bool :=
  decide (i < i' ∨ (i = i' ∧ j < j'))

public def insertTerm (i j : ℕ) (c : ℤ) : BiPoly → BiPoly
  | [] => if c = 0 then [] else [(i, j, c)]
  | e :: es =>
      if c = 0 then e :: es
      else if i = e.1 ∧ j = e.2.1 then
        let csum := c + e.2.2
        if csum = 0 then es else (i, j, csum) :: es
      else if monomialLess i j e.1 e.2.1 then
        (i, j, c) :: e :: es
      else
        e :: insertTerm i j c es

public def normalizeBiPoly : BiPoly → BiPoly :=
  List.foldr (fun e acc => insertTerm e.1 e.2.1 e.2.2 acc) []

public def biZero : BiPoly := []

public def biOne : BiPoly := [(0, 0, 1)]

public def biMonomial (c : ℤ) (i j : ℕ) : BiPoly :=
  if c = 0 then [] else [(i, j, c)]

public def biAdd (p q : BiPoly) : BiPoly :=
  normalizeBiPoly (p ++ q)

public def biMul (p q : BiPoly) : BiPoly :=
  normalizeBiPoly (p.flatMap fun e =>
    q.map fun f => (e.1 + f.1, e.2.1 + f.2.1, e.2.2 * f.2.2))

public def biScaleInt (c : ℤ) (p : BiPoly) : BiPoly :=
  normalizeBiPoly (p.map fun e => (e.1, e.2.1, c * e.2.2))

public def biEq (p q : BiPoly) : Bool :=
  decide (normalizeBiPoly p = normalizeBiPoly q)

public abbrev BiMatrix := Basis → Basis → BiPoly

public def allBasis : List Basis :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

public def allRoots : List Root :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- Local copy of root negation for the native checker. -/
public def checkerRootNeg : Root → Root
  | 0 => 6
  | 1 => 7
  | 2 => 8
  | 3 => 9
  | 4 => 10
  | 5 => 11
  | 6 => 0
  | 7 => 1
  | 8 => 2
  | 9 => 3
  | 10 => 4
  | 11 => 5

/-- Local copy of root coordinates for the native checker. -/
public def checkerRootCoord : Root → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (2, 1)
  | 4 => (3, 1)
  | 5 => (3, 2)
  | 6 => (-1, 0)
  | 7 => (0, -1)
  | 8 => (-1, -1)
  | 9 => (-2, -1)
  | 10 => (-3, -1)
  | 11 => (-3, -2)

/-- Local sparse-matrix evaluator for the native checker. -/
public def checkerMatrixOfEntries (entries : List (ℕ × ℕ × ℤ)) : IntegralMatrix :=
  fun row col =>
    entries.foldr
      (fun e value => if row.val = e.1 ∧ col.val = e.2.1 then e.2.2 else value) 0

/-- Local copy of the first divided-power sparse table for the native checker. -/
public def checkerRootOperatorEntries : Root → List (ℕ × ℕ × ℤ)
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

/-- Local copy of the second divided-power sparse table for the native checker. -/
public def checkerRootDividedPowerTwoEntries : Root → List (ℕ × ℕ × ℤ)
  | 0 => [(2, 8, 1), (5, 3, 1), (6, 4, 3), (9, 11, 3), (10, 12, 1)]
  | 1 => [(3, 9, 1)]
  | 2 => [(3, 11, 3), (4, 10, -1), (5, 9, 1), (7, 2, -3), (8, 13, -1)]
  | 3 => [(2, 13, -1), (4, 12, -1), (5, 11, 1), (6, 10, -3), (7, 8, -3)]
  | 4 => [(6, 12, -1)]
  | 5 => [(7, 13, 1)]
  | 6 => [(3, 5, 3), (4, 6, 1), (8, 2, 1), (11, 9, 1), (12, 10, 3)]
  | 7 => [(9, 3, 1)]
  | 8 => [(2, 7, -1), (9, 5, 3), (10, 4, -1), (11, 3, 1), (13, 8, -3)]
  | 9 => [(8, 7, -1), (10, 6, -1), (11, 5, 1), (12, 4, -3), (13, 2, -3)]
  | 10 => [(12, 6, -1)]
  | 11 => [(13, 7, 1)]

/-- Local copy of the third divided-power sparse table for the native checker. -/
public def checkerRootDividedPowerThreeEntries : Root → List (ℕ × ℕ × ℤ)
  | 0 => [(6, 3, 1), (9, 12, 1)]
  | 2 => [(3, 13, 1), (7, 9, -1)]
  | 3 => [(6, 13, -1), (7, 12, -1)]
  | 6 => [(3, 6, -1), (12, 9, -1)]
  | 8 => [(9, 7, 1), (13, 3, -1)]
  | 9 => [(12, 7, 1), (13, 6, 1)]
  | _ => []

public def checkerIntegralMatrixOne : IntegralMatrix :=
  fun i j => if i = j then 1 else 0

/-- Local copy of the divided powers for the native checker. -/
public def checkerRootDividedPower (r : Root) (m : Fin 4) : IntegralMatrix :=
  match m with
  | 0 => checkerIntegralMatrixOne
  | 1 => checkerMatrixOfEntries (checkerRootOperatorEntries r)
  | 2 => checkerMatrixOfEntries (checkerRootDividedPowerTwoEntries r)
  | 3 => checkerMatrixOfEntries (checkerRootDividedPowerThreeEntries r)

public def biMatrixOne : BiMatrix :=
  fun i j => if i = j then biOne else biZero

public def biMatrixAdd (A B : BiMatrix) : BiMatrix :=
  fun i j => biAdd (A i j) (B i j)

public def biMatrixMul (A B : BiMatrix) : BiMatrix :=
  fun i j =>
    allBasis.foldl
      (fun acc m => biAdd acc (biMul (A i m) (B m j))) biZero

public def biMatrixScaleIntegral (p : BiPoly) (A : IntegralMatrix) : BiMatrix :=
  fun i j => biScaleInt (A i j) p

public def rootCurvePoly (r : Root) (t : BiPoly) : BiMatrix :=
  biMatrixAdd
    (biMatrixAdd
      (biMatrixAdd biMatrixOne
        (biMatrixScaleIntegral t (checkerRootDividedPower r 1)))
      (biMatrixScaleIntegral (biMul t t) (checkerRootDividedPower r 2)))
    (biMatrixScaleIntegral (biMul (biMul t t) t) (checkerRootDividedPower r 3))

public def rootCurveCommutatorWordPoly (r s : Root) : BiMatrix :=
  (rootCurveCommutatorTerms r s).foldl
    (fun acc q =>
      biMatrixMul acc
        (rootCurvePoly q.root
          (biMonomial q.coeff q.leftPower q.rightPower)))
    biMatrixOne

public def rootCurveCommutatorLeftPoly (r s : Root) : BiMatrix :=
  biMatrixMul (rootCurvePoly r (biMonomial 1 1 0))
    (rootCurvePoly s (biMonomial 1 0 1))

public def rootCurveCommutatorRightPoly (r s : Root) : BiMatrix :=
  biMatrixMul
    (biMatrixMul (rootCurvePoly s (biMonomial 1 0 1))
      (rootCurvePoly r (biMonomial 1 1 0)))
    (rootCurveCommutatorWordPoly r s)

public def biMatrixEq (A B : BiMatrix) : Bool :=
  allBasis.all fun i => allBasis.all fun j => biEq (A i j) (B i j)

public abbrev SparseBiMatrix := List (ℕ × ℕ × BiPoly)

public def sparseEntryLess (i j i' j' : ℕ) : Bool :=
  decide (i < i' ∨ (i = i' ∧ j < j'))

public def insertSparseBiMatrixEntry (i j : ℕ) (p : BiPoly) :
    SparseBiMatrix → SparseBiMatrix
  | [] => if biEq p biZero then [] else [(i, j, normalizeBiPoly p)]
  | e :: es =>
      let p' := normalizeBiPoly p
      if biEq p' biZero then e :: es
      else if i = e.1 ∧ j = e.2.1 then
        let psum := biAdd p' e.2.2
        if biEq psum biZero then es else (i, j, psum) :: es
      else if sparseEntryLess i j e.1 e.2.1 then
        (i, j, p') :: e :: es
      else
        e :: insertSparseBiMatrixEntry i j p' es

public def normalizeSparseBiMatrix : SparseBiMatrix → SparseBiMatrix :=
  List.foldr (fun e acc => insertSparseBiMatrixEntry e.1 e.2.1 e.2.2 acc) []

public def sparseBiMatrixOne : SparseBiMatrix :=
  allBasis.map fun i => (i.val, i.val, biOne)

public def sparseBiMatrixAdd (A B : SparseBiMatrix) : SparseBiMatrix :=
  normalizeSparseBiMatrix (A ++ B)

public def sparseBiMatrixScaleEntries (p : BiPoly)
    (entries : List (ℕ × ℕ × ℤ)) : SparseBiMatrix :=
  normalizeSparseBiMatrix <|
    entries.map fun e => (e.1, e.2.1, biScaleInt e.2.2 p)

public def sparseBiMatrixMul (A B : SparseBiMatrix) : SparseBiMatrix :=
  normalizeSparseBiMatrix <|
    A.flatMap fun e =>
      B.filterMap fun f =>
        if e.2.1 = f.1 then
          some (e.1, f.2.1, biMul e.2.2 f.2.2)
        else
          none

public def rootCurvePolySparse (r : Root) (t : BiPoly) : SparseBiMatrix :=
  sparseBiMatrixAdd
    (sparseBiMatrixAdd
      (sparseBiMatrixAdd sparseBiMatrixOne
        (sparseBiMatrixScaleEntries t (checkerRootOperatorEntries r)))
      (sparseBiMatrixScaleEntries (biMul t t)
        (checkerRootDividedPowerTwoEntries r)))
    (sparseBiMatrixScaleEntries (biMul (biMul t t) t)
      (checkerRootDividedPowerThreeEntries r))

public def rootCurveCommutatorWordSparse (r s : Root) : SparseBiMatrix :=
  (rootCurveCommutatorTerms r s).foldl
    (fun acc q =>
      sparseBiMatrixMul acc
        (rootCurvePolySparse q.root
          (biMonomial q.coeff q.leftPower q.rightPower)))
    sparseBiMatrixOne

public def rootCurveCommutatorLeftSparse (r s : Root) : SparseBiMatrix :=
  sparseBiMatrixMul (rootCurvePolySparse r (biMonomial 1 1 0))
    (rootCurvePolySparse s (biMonomial 1 0 1))

public def rootCurveCommutatorRightSparse (r s : Root) : SparseBiMatrix :=
  sparseBiMatrixMul
    (sparseBiMatrixMul (rootCurvePolySparse s (biMonomial 1 0 1))
      (rootCurvePolySparse r (biMonomial 1 1 0)))
    (rootCurveCommutatorWordSparse r s)

public def sparseBiMatrixEq (A B : SparseBiMatrix) : Bool :=
  decide (normalizeSparseBiMatrix A = normalizeSparseBiMatrix B)

/-- Equal and opposite roots are collected by additive or rank-one Bruhat
relations, not by the pure non-opposite commutator table. -/
public def rootCurvePairIsRankOneOrSame (r s : Root) : Bool :=
  decide (r = s ∨ s = checkerRootNeg r)

/-- Boolean matrix check for the displayed correction word of one root pair. -/
public def rootCurveCommutatorPairChecked (r s : Root) : Bool :=
  sparseBiMatrixEq (rootCurveCommutatorLeftSparse r s)
    (rootCurveCommutatorRightSparse r s)

/-- Matrix check for one row of the ordered root-pair table. -/
public def rootCurveCommutatorRowValid (r : Root) : Bool :=
  allRoots.all fun s =>
    rootCurvePairIsRankOneOrSame r s ||
      rootCurveCommutatorPairChecked r s

/-- Matrix check for all non-equal, non-opposite root pairs. -/
public def rootCurveCommutatorTableValid : Bool :=
  allRoots.all rootCurveCommutatorRowValid

public def termCoordinateValid (r s : Root) (q : RootCurveCommutatorTerm) : Bool :=
  decide
    (0 < q.leftPower ∧ 0 < q.rightPower ∧
      (checkerRootCoord q.root).1 =
        (q.leftPower : ℤ) * (checkerRootCoord r).1 +
          (q.rightPower : ℤ) * (checkerRootCoord s).1 ∧
      (checkerRootCoord q.root).2 =
        (q.leftPower : ℤ) * (checkerRootCoord r).2 +
          (q.rightPower : ℤ) * (checkerRootCoord s).2)

/-- Root-coordinate support check for every listed correction term. -/
public def rootCurveCommutatorSupportValid : Bool :=
  allRoots.all fun r =>
    allRoots.all fun s =>
      (rootCurveCommutatorTerms r s).all (termCoordinateValid r s)

/-- The finite checker combines matrix equality and root-coordinate support. -/
public def rootCurveCollectionPackageValid : Bool :=
  rootCurveCommutatorTableValid && rootCurveCommutatorSupportValid

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem rootCurve_commutator_table_row0 :
    rootCurveCommutatorRowValid 0 = true := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem rootCurve_commutator_table_row1 :
    rootCurveCommutatorRowValid 1 = true := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem rootCurve_commutator_table_row2 :
    rootCurveCommutatorRowValid 2 = true := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem rootCurve_commutator_table_row3 :
    rootCurveCommutatorRowValid 3 = true := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem rootCurve_commutator_table_row4 :
    rootCurveCommutatorRowValid 4 = true := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem rootCurve_commutator_table_row5 :
    rootCurveCommutatorRowValid 5 = true := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem rootCurve_commutator_table_row6 :
    rootCurveCommutatorRowValid 6 = true := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem rootCurve_commutator_table_row7 :
    rootCurveCommutatorRowValid 7 = true := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem rootCurve_commutator_table_row8 :
    rootCurveCommutatorRowValid 8 = true := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem rootCurve_commutator_table_row9 :
    rootCurveCommutatorRowValid 9 = true := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem rootCurve_commutator_table_row10 :
    rootCurveCommutatorRowValid 10 = true := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem rootCurve_commutator_table_row11 :
    rootCurveCommutatorRowValid 11 = true := by
  decide

set_option maxHeartbeats 0 in
/-- The correction words are exactly the integral matrix identities for all
non-opposite pairs of explicit `G2` root curves. -/
public theorem rootCurve_commutator_table_checked :
    rootCurveCommutatorTableValid = true := by
  simp [rootCurveCommutatorTableValid, allRoots,
    rootCurve_commutator_table_row0, rootCurve_commutator_table_row1,
    rootCurve_commutator_table_row2, rootCurve_commutator_table_row3,
    rootCurve_commutator_table_row4, rootCurve_commutator_table_row5,
    rootCurve_commutator_table_row6, rootCurve_commutator_table_row7,
    rootCurve_commutator_table_row8, rootCurve_commutator_table_row9,
    rootCurve_commutator_table_row10, rootCurve_commutator_table_row11]

set_option maxHeartbeats 0 in
/-- Every listed correction term has positive powers and the advertised root
coordinate `i*r + j*s`. -/
public theorem rootCurve_commutator_support_checked :
    rootCurveCommutatorSupportValid = true := by
  decide

set_option maxHeartbeats 0 in
/-- Public package theorem for the explicit `G2` root-curve collection data. -/
public theorem rootCurve_collection_package :
    rootCurveCollectionPackageValid = true := by
  simp [rootCurveCollectionPackageValid, rootCurve_commutator_table_checked,
    rootCurve_commutator_support_checked]

end

end Theory.AlgebraicGroup.G2Chevalley
