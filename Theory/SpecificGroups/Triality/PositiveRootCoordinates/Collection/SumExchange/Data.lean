module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.Relations
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Geometry
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Binary coefficient matrices on the full D₄ Geck lattice

The index equivalence retains all four Cartan coordinates and all 24 root
coordinates. The linear coefficient raises a root along a root string, sends
an opposite root to its simple-coroot coordinates, and acts on a Cartan
coordinate by the corresponding pairing. The quadratic coefficient connects
opposite roots. All displayed coefficients lie in `ZMod 2`.

This module defines concrete matrices and proves their root-coordinate and
scalar-extension interfaces. Their comparison with the canonical integral
root operators and their polynomial exchange identity are separate proof
obligations. Evaluating a two-variable polynomial identity gives the exchange
identity over every commutative ring of characteristic two, without any bound
on the field size.

Source: the common-lattice Chevalley construction in GLS3 §§2.4–2.6 and the
positive-root collection in 2.3.6–7 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open scoped BigOperators
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

namespace Triality.Standard.PositiveCoordinates.SumExchangeData

abbrev Index := Fin 4 ⊕ Fin 24

/-- Reindex all 28 coordinates; no quotient or invariant subspace is taken. -/
def latticeEnumeration : Index ≃ LatticeIndex :=
  Equiv.sumCongr (typeDRootPairing_baseEquiv 2) rootEnumeration

def positiveIndex : Fin 12 → Fin 24 := ![1, 21, 20, 13, 5, 17, 16, 9, 12, 8, 4, 0]

theorem rootEnumeration_positiveIndex (i : Fin 12) :
    rootEnumeration (positiveIndex i) = rootIndex i := by
  fin_cases i <;> rfl

def simpleIndex : Fin 4 → Fin 24 := ![1, 13, 21, 20]

theorem rootEnumeration_simpleIndex (i : Fin 4) :
    rootEnumeration (simpleIndex i) = typeDSimpleRootIndex 2 i := by
  fin_cases i <;> rfl

def negativeIndex : Fin 24 → Fin 24 :=
  ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16,
    23, 22, 21, 20]

def simpleCoefficients : Fin 24 → Fin 4 → ℤ :=
  ![![1,2,1,1], ![1,0,0,0], ![-1,0,0,0], ![-1,-2,-1,-1],
    ![1,1,1,1], ![1,1,0,0], ![-1,-1,0,0], ![-1,-1,-1,-1],
    ![1,1,0,1], ![1,1,1,0], ![-1,-1,-1,0], ![-1,-1,0,-1],
    ![0,1,1,1], ![0,1,0,0], ![0,-1,0,0], ![0,-1,-1,-1],
    ![0,1,0,1], ![0,1,1,0], ![0,-1,-1,0], ![0,-1,0,-1],
    ![0,0,0,1], ![0,0,1,0], ![0,0,-1,0], ![0,0,0,-1]]

def rootPairing (r : Fin 24) (j : Fin 4) : ℤ :=
  ∑ k : Fin 4, rootCoords r k * rootCoords (simpleIndex j) k

theorem rootCoords_negativeIndex (r : Fin 24) :
    rootCoords (negativeIndex r) = -rootCoords r := by
  revert r
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem simpleCoefficients_spec (r : Fin 24) :
    rootCoords r = ∑ j : Fin 4, simpleCoefficients r j • rootCoords (simpleIndex j) := by
  revert r
  decide +kernel

def linearCoefficient (r : Fin 24) : Matrix Index Index (ZMod 2)
  | .inl _, .inl _ => 0
  | .inl k, .inr s => if s = negativeIndex r then (simpleCoefficients r k : ZMod 2) else 0
  | .inr q, .inl j => if q = r then (rootPairing r j : ZMod 2) else 0
  | .inr q, .inr s => if rootCoords q = rootCoords r + rootCoords s then 1 else 0

def quadraticCoefficient (r : Fin 24) : Matrix Index Index (ZMod 2) :=
  fun q s => if q = .inr r ∧ s = .inr (negativeIndex r) then 1 else 0

def scalarMap (F : Type*) [CommRing F] [CharP F 2] : ZMod 2 →+* F :=
  ZMod.castHom (dvd_refl 2) F

def matrixCurve {F : Type*} [CommRing F] [CharP F 2]
    (r : Fin 24) (t : F) : Matrix Index Index F :=
  1 + t • (scalarMap F).mapMatrix (linearCoefficient r) +
    t ^ 2 • (scalarMap F).mapMatrix (quadraticCoefficient r)

theorem root_sum_iff (i j k : Fin 12) :
    (typeDRootPairing 2).root (rootIndex k) =
      (typeDRootPairing 2).root (rootIndex i) + (typeDRootPairing 2).root (rootIndex j) ↔
    rootCoords (positiveIndex k) = rootCoords (positiveIndex i) + rootCoords (positiveIndex j) := by
  simp only [← rootEnumeration_positiveIndex]
  rw [Subtype.ext_iff, funext_iff, funext_iff]
  simp only [Submodule.coe_add, Pi.add_apply, rootCoords_spec, ← Int.cast_add, Int.cast_inj]

/-- All ordered positive root-sum triples in the published enumeration. -/
def sumTriples : List (Fin 12 × Fin 12 × Fin 12) :=
  [(0,3,4), (0,5,7), (0,6,9), (0,8,10),
   (1,3,5), (1,4,7), (1,6,8), (1,9,10),
   (2,3,6), (2,4,9), (2,5,8), (2,7,10),
   (3,0,4), (3,1,5), (3,2,6), (3,10,11),
   (4,1,7), (4,2,9), (4,8,11),
   (5,0,7), (5,2,8), (5,9,11),
   (6,0,9), (6,1,8), (6,7,11),
   (7,2,10), (7,6,11), (8,0,10), (8,4,11),
   (9,1,10), (9,5,11), (10,3,11)]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem mem_sumTriples_iff (i j k : Fin 12) :
    (i, j, k) ∈ sumTriples ↔
      rootCoords (positiveIndex k) = rootCoords (positiveIndex i) + rootCoords (positiveIndex j) := by
  revert i j k
  decide +kernel

theorem map_matrixCurve {F K : Type*} [CommRing F] [CharP F 2]
    [CommRing K] [CharP K 2] (f : F →+* K) (r : Fin 24) (t : F) :
    f.mapMatrix (matrixCurve r t) = matrixCurve r (f t) := by
  have hc (x : ZMod 2) : f (scalarMap F x) = scalarMap K x := by
    have he : f.comp (scalarMap F) = scalarMap K := Subsingleton.elim _ _
    exact DFunLike.congr_fun he x
  ext a b
  simp only [matrixCurve, map_add, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hc]
  simp [Matrix.one_apply]

abbrev PolynomialRing := MvPolynomial (Fin 2) (ZMod 2)

def polynomialCurve (r : Fin 24) (v : Fin 2) : Matrix Index Index PolynomialRing :=
  matrixCurve r (MvPolynomial.X v)

theorem matrix_exchange_of_polynomial {F : Type*} [CommRing F] [CharP F 2]
    (i j k : Fin 12)
    (h : polynomialCurve (positiveIndex i) 0 * polynomialCurve (positiveIndex j) 1 =
      polynomialCurve (positiveIndex j) 1 * polynomialCurve (positiveIndex i) 0 *
        matrixCurve (positiveIndex k) ((MvPolynomial.X 0 : PolynomialRing) * MvPolynomial.X 1))
    (a b : F) :
    matrixCurve (positiveIndex i) a * matrixCurve (positiveIndex j) b =
      matrixCurve (positiveIndex j) b * matrixCurve (positiveIndex i) a *
        matrixCurve (positiveIndex k) (a * b) := by
  let ev : PolynomialRing →+* F := MvPolynomial.eval₂Hom (scalarMap F) ![a, b]
  have he := congrArg ev.mapMatrix h
  simpa only [polynomialCurve, map_mul, map_matrixCurve, ev,
    MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using he

/-- The proposed four coefficients, including the constant and cubic terms. -/
def dividedCoefficient (r : Fin 24) (d : Fin 4) : Matrix Index Index (ZMod 2) :=
  ![1, linearCoefficient r, quadraticCoefficient r, 0] d

/-- The actual integral divided power, reduced modulo two on the full lattice. -/
def canonicalCoefficient (i : Fin 12) (d : Fin 4) : Matrix Index Index (ZMod 2) :=
  Matrix.reindexRingEquiv (ZMod 2) latticeEnumeration.symm
    (RootPairing.IntegralGeckConstruction.specializeMatrix
      (RootPairing.IntegralGeckConstruction.rootDividedPower
        (b := typeDRootPairing_base 2) (rootIndex i) d))

end Triality.Standard.PositiveCoordinates.SumExchangeData
