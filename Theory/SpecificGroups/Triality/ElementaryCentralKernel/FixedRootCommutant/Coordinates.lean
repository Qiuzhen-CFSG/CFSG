module
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Comparison
public import Mathlib.Tactic.LinearCombination

/-!
# Numerical coordinates for the fixed-root commutant

The four Cartan coordinates followed by the lexicographic 24 roots identify
Geck's D4 lattice with `Fin 28`. The sparse linear and quadratic coefficients
below are checked against the integral root-string formulas, then specialized
to characteristic two. No assertion about the commutant is used here.

Source: GLS3 §§2.2–2.4, with the integral Geck comparison in
`LeviRankOneMatrices.Comparison`.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open RootPairing.SimpleGeckGroup
namespace Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

/-- Cartan coordinates, then the lexicographic root coordinates. -/
def coordinates : Fin 28 ≃ LatticeIndex :=
  (finSumFinEquiv : Fin 4 ⊕ Fin 24 ≃ Fin 28).symm.trans
    (Equiv.sumCongr (typeDRootPairing_baseEquiv 2) rootEnumeration)

/-- Numbered coordinates of the root-string ordering at vertex `i`. -/
def orderedCoordinates (i : Fin 4) : FlatIndex ≃ Fin 28 :=
  (Equiv.sumCongr (Equiv.refl _) (rootOrder i)).trans finSumFinEquiv

lemma coordinates_ordered (i : Fin 4) (r : FlatIndex) :
    coordinates (orderedCoordinates i r) = flatEquiv i r := by
  simp [coordinates, orderedCoordinates, flatEquiv]

/-- Positions with linear coefficient one; `true` denotes the positive root. -/
def linearSupport (i : Fin 4) (s : Bool) : List (Fin 28 × Fin 28) :=
  if s then
    ![[(0, 6), (5, 1), (8, 16), (9, 17), (12, 20), (13, 21), (18, 10), (19, 11), (22, 14), (23, 15)],
      [(1, 18), (4, 8), (6, 10), (9, 5), (11, 7), (17, 0), (17, 2), (17, 3), (20, 24), (21, 25), (26, 22), (27, 23)],
      [(2, 26), (8, 12), (10, 14), (13, 9), (15, 11), (16, 20), (18, 22), (21, 17), (23, 19), (25, 1)],
      [(3, 27), (8, 13), (10, 15), (12, 9), (14, 11), (16, 21), (18, 23), (20, 17), (22, 19), (24, 1)]] i
  else
    ![[(0, 5), (6, 1), (10, 18), (11, 19), (14, 22), (15, 23), (16, 8), (17, 9), (20, 12), (21, 13)],
      [(1, 17), (5, 9), (7, 11), (8, 4), (10, 6), (18, 0), (18, 2), (18, 3), (22, 26), (23, 27), (24, 20), (25, 21)],
      [(2, 25), (9, 13), (11, 15), (12, 8), (14, 10), (17, 21), (19, 23), (20, 16), (22, 18), (26, 1)],
      [(3, 24), (9, 12), (11, 14), (13, 8), (15, 10), (17, 20), (19, 22), (21, 16), (23, 18), (27, 1)]] i

/-- The sole quadratic coefficient joins the two opposite simple roots. -/
def quadraticPosition (i : Fin 4) (s : Bool) : Fin 28 × Fin 28 :=
  if s then ![(5, 6), (17, 18), (25, 26), (24, 27)] i
  else ![(6, 5), (18, 17), (26, 25), (27, 24)] i

/-- Explicit polynomial matrix of a signed pinned simple root. -/
def rootMatrix {F : Type*} [CommRing F] (i : Fin 4) (s : Bool) (t : F) :
    Matrix (Fin 28) (Fin 28) F := fun r c =>
  (if r = c then 1 else 0) +
    (if (r, c) ∈ linearSupport i s then t else 0) +
    (if (r, c) = quadraticPosition i s then t ^ 2 else 0)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma linearCoefficient_check (i : Fin 4) (s : Bool) (r c : FlatIndex) :
    (if s then eData i r c else fData i r c) % 2 =
      if (orderedCoordinates i r, orderedCoordinates i c) ∈ linearSupport i s
      then (1 : ℤ) else 0 := by
  revert i s r c
  simp only [Sum.forall]
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma quadraticCoefficient_check (i : Fin 4) (s : Bool) (r c : FlatIndex) :
    (r = .inr (if s then 0 else 1) ∧ c = .inr (if s then 1 else 0)) ↔
      (orderedCoordinates i r, orderedCoordinates i c) = quadraticPosition i s := by
  revert i s r c
  simp only [Sum.forall]
  decide +kernel

variable {F : Type*} [CommRing F] [CharP F 2]

lemma positiveMatrix_coordinates (i : Fin 4) (t : F) :
    (positiveMatrix (typeDRootPairing_baseEquiv 2 i) t).submatrix
      coordinates coordinates = rootMatrix i true t := by
  ext r c
  obtain ⟨r, rfl⟩ := (orderedCoordinates i).surjective r
  obtain ⟨c, rfl⟩ := (orderedCoordinates i).surjective c
  simp only [Matrix.submatrix_apply, coordinates_ordered, positiveMatrix_entry]
  have he := linearCoefficient_check i true r c
  change eData i r c % 2 = _ at he
  rw [CharTwo.intCast_eq_mod, he]
  simp only [rootMatrix, (orderedCoordinates i).injective.eq_iff,
    Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero,
    ← quadraticCoefficient_check i true, ite_true]

lemma negativeMatrix_coordinates (i : Fin 4) (t : F) :
    (negativeMatrix (typeDRootPairing_baseEquiv 2 i) t).submatrix
      coordinates coordinates = rootMatrix i false t := by
  ext r c
  obtain ⟨r, rfl⟩ := (orderedCoordinates i).surjective r
  obtain ⟨c, rfl⟩ := (orderedCoordinates i).surjective c
  simp only [Matrix.submatrix_apply, coordinates_ordered, negativeMatrix_entry]
  have he := linearCoefficient_check i false r c
  change fData i r c % 2 = _ at he
  rw [CharTwo.intCast_eq_mod, he]
  simp only [rootMatrix, (orderedCoordinates i).injective.eq_iff,
    Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero,
    ← quadraticCoefficient_check i false, Bool.false_eq_true, ite_false]

end
end Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
