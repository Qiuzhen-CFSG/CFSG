module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.RootDuality
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Coordinates for the exceptional F4 module comparison

The Cartan-plus-root lattice has a distinguished coordinate subspace spanned
by the short roots and their simple Cartan coordinates. The matrix below kills
these coordinates and sends each remaining coordinate to its dual short
coordinate. Its image is exactly the short coordinate subspace.

This supplies the coordinate map for comparing the quotient and submodule in
the characteristic-two adjoint representation. The module proves only the
coordinate identities; compatibility with root curves and faithfulness of
their action require separate representation-theoretic arguments.

The root involution and numbering convention are those of `RootDuality`.
-/

public section

namespace ReeF4.WordRelations

open Theory.AlgebraicGroup.StandardRootSystem
open scoped Classical Matrix

abbrev Coordinate := typeF4RootPairing_base.support ⊕ typeF4Roots

noncomputable local instance : Fintype typeF4Roots := Fintype.ofFinite _

/-- The short-root part, including the two short simple Cartan coordinates. -/
@[expose] def IsShortCoordinate : Coordinate → Prop
  | Sum.inl i => IsShortRoot i.val
  | Sum.inr r => IsShortRoot r

/-- Diagram reversal on the simple Cartan coordinates. -/
noncomputable def simplePermutation : Equiv.Perm typeF4RootPairing_base.support :=
  typeF4RootPairing_baseEquiv.symm.trans
    (Fin.revPerm.trans typeF4RootPairing_baseEquiv)

@[simp] theorem simplePermutation_numbered (i : Fin 4) :
    simplePermutation (typeF4RootPairing_baseEquiv i) =
      typeF4RootPairing_baseEquiv (Fin.revPerm i) := by
  simp [simplePermutation]

theorem simplePermutation_val (i : typeF4RootPairing_base.support) :
    (simplePermutation i).val = exceptionalRootPermutation i.val := by
  obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
  simpa [simplePermutation] using (exceptionalRootPermutation_simple i).symm

theorem simplePermutation_involutive : Function.Involutive simplePermutation := by
  intro i
  apply Subtype.ext
  simp only [simplePermutation_val]
  exact exceptionalRootPermutation_involutive i.val

/-- Simultaneous diagram reversal and root duality on all 52 coordinates. -/
noncomputable def coordinatePermutation : Equiv.Perm Coordinate :=
  Equiv.sumCongr simplePermutation exceptionalRootPermutation

@[simp] theorem coordinatePermutation_inl (i : typeF4RootPairing_base.support) :
    coordinatePermutation (Sum.inl i) = Sum.inl (simplePermutation i) := by rfl

@[simp] theorem coordinatePermutation_inr (r : typeF4Roots) :
    coordinatePermutation (Sum.inr r) = Sum.inr (exceptionalRootPermutation r) := by rfl

theorem coordinatePermutation_involutive : Function.Involutive coordinatePermutation := by
  intro i
  cases i with
  | inl i => exact congrArg Sum.inl (simplePermutation_involutive i)
  | inr r => exact congrArg Sum.inr (exceptionalRootPermutation_involutive r)

theorem coordinatePermutation_short_iff (i : Coordinate) :
    IsShortCoordinate (coordinatePermutation i) ↔ ¬IsShortCoordinate i := by
  have hr (r : typeF4Roots) :
      IsShortRoot (exceptionalRootPermutation r) ↔ ¬IsShortRoot r := by
    simpa only [IsShortRoot, not_not] using
      (exceptionalRootPermutation_long_iff r).symm
  cases i with
  | inl i => simpa only [coordinatePermutation, Equiv.sumCongr_apply, Sum.map_inl,
      IsShortCoordinate, simplePermutation_val] using hr i.val
  | inr r => exact hr r

/-- Projection to the long quotient followed by its coordinate identification
with the short subspace. This matrix is not invertible. -/
noncomputable def quotientToIdeal {K : Type*} [Zero K] [One K] :
    Matrix Coordinate Coordinate K := by
  classical
  exact fun i j => if IsShortCoordinate j then 0 else
    if i = coordinatePermutation j then 1 else 0

theorem quotientToIdeal_apply {K : Type*} [Zero K] [One K] (i j : Coordinate) :
    quotientToIdeal (K := K) i j = if IsShortCoordinate j then 0 else
      if i = coordinatePermutation j then 1 else 0 := by rfl

theorem mul_quotientToIdeal {K : Type*} [Semiring K]
    (A : Matrix Coordinate Coordinate K) (i j : Coordinate) :
    (A * quotientToIdeal (K := K)) i j =
      if IsShortCoordinate j then 0 else A i (coordinatePermutation j) := by
  classical
  by_cases hj : IsShortCoordinate j <;>
    simp [Matrix.mul_apply, quotientToIdeal, hj]

/-- Fixing the image of the comparison matrix is exactly fixing every short
coordinate vector. -/
theorem mul_quotientToIdeal_eq_iff {K : Type*} [Semiring K]
    (A : Matrix Coordinate Coordinate K) :
    A * quotientToIdeal = quotientToIdeal ↔
      ∀ j, IsShortCoordinate j → ∀ i, A i j = if i = j then 1 else 0 := by
  classical
  constructor
  · intro h j hj i
    have hc := congrFun (congrFun h i) (coordinatePermutation j)
    have hn : ¬IsShortCoordinate (coordinatePermutation j) := by
      rw [coordinatePermutation_short_iff]
      exact not_not.mpr hj
    simpa only [mul_quotientToIdeal, quotientToIdeal, if_neg hn,
      coordinatePermutation_involutive j] using hc
  · intro h
    ext i j
    rw [mul_quotientToIdeal]
    by_cases hj : IsShortCoordinate j
    · simp [quotientToIdeal, hj]
    · simpa only [quotientToIdeal, if_neg hj] using
        h (coordinatePermutation j) ((coordinatePermutation_short_iff j).mpr hj) i

end ReeF4.WordRelations
