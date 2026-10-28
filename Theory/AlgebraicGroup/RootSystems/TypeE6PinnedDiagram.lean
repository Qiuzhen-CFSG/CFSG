module

public import Theory.AlgebraicGroup.RootSystems.TypeE6DiagramRootStrings
public import Theory.AlgebraicGroup.RootSystems.GeckDiagramEquivariance
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# The integral pinned E6 diagram action

The graph involution acts on the finite Chevalley lattice by reindexing the
Cartan and root coordinates.  This file records that concrete permutation and
the resulting ambient matrix-ring equivalence. Root-string invariance proves
that this permutation carries the positive and negative simple operators and
all their integral divided powers to those at the diagram image. Consequently
it preserves the simple-root pinning over every coefficient ring. The action
is involutive and is nonidentity over every nonzero ring; it commutes with
entrywise coefficient maps. Restriction to the all-root generated subgroup is
constructed in `TwistedE6SplitCarrier`.

This is the ambient coordinate action used in the graph-field construction
of GLS3, §§2.1–2.3 (`refs/KGroup/GLS3/chapter2.tex`).
-/

namespace Theory.AlgebraicGroup.StandardRootSystem

@[expose] public section

abbrev typeE6PinnedIndex := typeE6RootPairing_base.support ⊕ typeE6Roots

noncomputable instance typeE6Roots_fintype : Fintype typeE6Roots := Fintype.ofFinite _

noncomputable def typeE6PinnedIndexEquiv : Equiv.Perm typeE6PinnedIndex :=
  Equiv.sumCongr typeE6DiagramBasePermutation typeE6DiagramEquiv.indexEquiv

@[simp] theorem typeE6PinnedIndexEquiv_inl (i : typeE6RootPairing_base.support) :
    typeE6PinnedIndexEquiv (Sum.inl i) =
      Sum.inl (typeE6DiagramBasePermutation i) := by
  simp [typeE6PinnedIndexEquiv]

@[simp] theorem typeE6PinnedIndexEquiv_inr (r : typeE6Roots) :
    typeE6PinnedIndexEquiv (Sum.inr r) =
    Sum.inr (typeE6DiagramEquiv.indexEquiv r) := by
  simp [typeE6PinnedIndexEquiv]

@[simp] theorem typeE6PinnedIndexEquiv_twice (i : typeE6PinnedIndex) :
    typeE6PinnedIndexEquiv (typeE6PinnedIndexEquiv i) = i := by
  rcases i with i | r
  · simp [typeE6PinnedIndexEquiv, typeE6DiagramBasePermutation_twice]
  · simp [typeE6PinnedIndexEquiv]

noncomputable def typeE6PinnedMatrixRingEquiv (R : Type*) [CommRing R] :
    Matrix typeE6PinnedIndex typeE6PinnedIndex R ≃+*
      Matrix typeE6PinnedIndex typeE6PinnedIndex R :=
  Matrix.reindexRingEquiv R typeE6PinnedIndexEquiv

@[simp] theorem typeE6PinnedMatrixRingEquiv_apply (R : Type*) [CommRing R]
    (A : Matrix typeE6PinnedIndex typeE6PinnedIndex R) (i j : typeE6PinnedIndex) :
    typeE6PinnedMatrixRingEquiv R A i j =
      A (typeE6PinnedIndexEquiv.symm i) (typeE6PinnedIndexEquiv.symm j) := by
  rfl

theorem typeE6PinnedMatrixRingEquiv_apply_twiceIndex (R : Type*) [CommRing R]
    (A : Matrix typeE6PinnedIndex typeE6PinnedIndex R) (i j : typeE6PinnedIndex) :
    typeE6PinnedMatrixRingEquiv R A i j =
      A (typeE6PinnedIndexEquiv i) (typeE6PinnedIndexEquiv j) := by
  rw [typeE6PinnedMatrixRingEquiv_apply]
  have hinv : typeE6PinnedIndexEquiv.symm = typeE6PinnedIndexEquiv := by
    ext x
    apply typeE6PinnedIndexEquiv.injective
    simp [typeE6PinnedIndexEquiv_twice]
  simp [hinv]

@[simp] theorem typeE6PinnedMatrixRingEquiv_twice (R : Type*) [CommRing R]
    (A : Matrix typeE6PinnedIndex typeE6PinnedIndex R) :
    typeE6PinnedMatrixRingEquiv R (typeE6PinnedMatrixRingEquiv R A) = A := by
  ext i j
  rw [typeE6PinnedMatrixRingEquiv_apply, typeE6PinnedMatrixRingEquiv_apply]
  have hinv : typeE6PinnedIndexEquiv.symm = typeE6PinnedIndexEquiv := by
    ext x
    apply typeE6PinnedIndexEquiv.injective
    simp [typeE6PinnedIndexEquiv_twice]
  simp [hinv, typeE6PinnedIndexEquiv_twice]

/-- Reindexing commutes with every entrywise change of coefficients. -/
theorem typeE6PinnedMatrixRingEquiv_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R → S) (A : Matrix typeE6PinnedIndex typeE6PinnedIndex R) :
    typeE6PinnedMatrixRingEquiv S (A.map f) =
      (typeE6PinnedMatrixRingEquiv R A).map f := rfl

/-- The ambient diagram automorphism after extension to any coefficient ring. -/
noncomputable def typeE6PinnedUnitsEquiv (R : Type*) [CommRing R] :
    (Matrix typeE6PinnedIndex typeE6PinnedIndex R)ˣ ≃*
      (Matrix typeE6PinnedIndex typeE6PinnedIndex R)ˣ :=
  Units.mapEquiv (typeE6PinnedMatrixRingEquiv R).toMulEquiv

@[simp] theorem typeE6PinnedUnitsEquiv_apply (R : Type*) [CommRing R]
    (g : (Matrix typeE6PinnedIndex typeE6PinnedIndex R)ˣ) (i j : typeE6PinnedIndex) :
    (typeE6PinnedUnitsEquiv R g : Matrix typeE6PinnedIndex typeE6PinnedIndex R) i j =
      (g : Matrix typeE6PinnedIndex typeE6PinnedIndex R)
        (typeE6PinnedIndexEquiv i) (typeE6PinnedIndexEquiv j) :=
  typeE6PinnedMatrixRingEquiv_apply_twiceIndex R g i j

@[simp] theorem typeE6PinnedUnitsEquiv_twice (R : Type*) [CommRing R]
    (g : (Matrix typeE6PinnedIndex typeE6PinnedIndex R)ˣ) :
    typeE6PinnedUnitsEquiv R (typeE6PinnedUnitsEquiv R g) = g := by
  apply Units.ext
  exact typeE6PinnedMatrixRingEquiv_twice R g

/-- In particular the ambient diagram action commutes with field Frobenius. -/
theorem typeE6PinnedUnitsEquiv_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : (Matrix typeE6PinnedIndex typeE6PinnedIndex R)ˣ) :
    typeE6PinnedUnitsEquiv S (Units.map (f.mapMatrix.toMonoidHom) g) =
      Units.map (f.mapMatrix.toMonoidHom) (typeE6PinnedUnitsEquiv R g) := by
  apply Units.ext
  rfl

open RootPairing.IntegralGeckConstruction

/-- The specified E6 permutation preserves the positive integral pinning. -/
@[simp] theorem typeE6Pinned_eMatrix (i : typeE6RootPairing_base.support) :
    typeE6PinnedMatrixRingEquiv ℤ (eMatrix i) =
      eMatrix (typeE6DiagramBasePermutation i) :=
  diagram_eMatrix typeE6DiagramEquiv typeE6DiagramBasePermutation
    typeE6DiagramEquiv_simple i

/-- The specified E6 permutation preserves the negative integral pinning. -/
@[simp] theorem typeE6Pinned_fMatrix (i : typeE6RootPairing_base.support) :
    typeE6PinnedMatrixRingEquiv ℤ (fMatrix i) =
      fMatrix (typeE6DiagramBasePermutation i) :=
  diagram_fMatrix typeE6DiagramEquiv typeE6DiagramBasePermutation
    typeE6DiagramEquiv_simple i

@[simp] theorem typeE6Pinned_eDividedPower (i : typeE6RootPairing_base.support) (n : ℕ) :
    typeE6PinnedMatrixRingEquiv ℤ (eDividedPower i n) =
      eDividedPower (typeE6DiagramBasePermutation i) n :=
  diagram_eDividedPower typeE6DiagramEquiv typeE6DiagramBasePermutation
    typeE6DiagramEquiv_simple i n

@[simp] theorem typeE6Pinned_fDividedPower (i : typeE6RootPairing_base.support) (n : ℕ) :
    typeE6PinnedMatrixRingEquiv ℤ (fDividedPower i n) =
      fDividedPower (typeE6DiagramBasePermutation i) n :=
  diagram_fDividedPower typeE6DiagramEquiv typeE6DiagramBasePermutation
    typeE6DiagramEquiv_simple i n

private theorem pinned_smul {S : Type*} [CommRing S] (t : S)
    (A : Matrix typeE6PinnedIndex typeE6PinnedIndex S) :
    typeE6PinnedMatrixRingEquiv S (t • A) = t • typeE6PinnedMatrixRingEquiv S A := rfl

/-- Positive simple curves are pinned over every coefficient ring. -/
@[simp] theorem typeE6Pinned_positiveUnit {S : Type*} [CommRing S]
    (i : typeE6RootPairing_base.support) (t : S) :
    typeE6PinnedUnitsEquiv S (RootPairing.SimpleGeckGroup.positiveUnit i t) =
      RootPairing.SimpleGeckGroup.positiveUnit (typeE6DiagramBasePermutation i) t := by
  apply Units.ext
  change typeE6PinnedMatrixRingEquiv S (RootPairing.SimpleGeckGroup.positiveMatrix i t) =
    RootPairing.SimpleGeckGroup.positiveMatrix (typeE6DiagramBasePermutation i) t
  simp only [RootPairing.SimpleGeckGroup.positiveMatrix_formula, map_add, RingEquiv.map_one,
    pinned_smul, typeE6PinnedMatrixRingEquiv_map, typeE6Pinned_eDividedPower]

/-- Negative simple curves are pinned with the same parameter. -/
@[simp] theorem typeE6Pinned_negativeUnit {S : Type*} [CommRing S]
    (i : typeE6RootPairing_base.support) (t : S) :
    typeE6PinnedUnitsEquiv S (RootPairing.SimpleGeckGroup.negativeUnit i t) =
      RootPairing.SimpleGeckGroup.negativeUnit (typeE6DiagramBasePermutation i) t := by
  apply Units.ext
  change typeE6PinnedMatrixRingEquiv S (RootPairing.SimpleGeckGroup.negativeMatrix i t) =
    RootPairing.SimpleGeckGroup.negativeMatrix (typeE6DiagramBasePermutation i) t
  simp only [RootPairing.SimpleGeckGroup.negativeMatrix_formula, map_add, RingEquiv.map_one,
    pinned_smul, typeE6PinnedMatrixRingEquiv_map, typeE6Pinned_fDividedPower]

/-- Distinct simple roots give distinct unit-parameter positive root elements. -/
theorem typeE6PositiveUnit_ne {S : Type*} [CommRing S] [Nontrivial S]
    {i j : typeE6RootPairing_base.support} (hij : i ≠ j) :
    RootPairing.SimpleGeckGroup.positiveUnit i (1 : S) ≠
      RootPairing.SimpleGeckGroup.positiveUnit j (1 : S) := by
  let := typeE6RootPairing.indexNeg
  intro h
  have he := congrArg (fun g : (Matrix typeE6PinnedIndex typeE6PinnedIndex S)ˣ =>
    (g : Matrix typeE6PinnedIndex typeE6PinnedIndex S) (Sum.inl i)
      (Sum.inr (-i : typeE6Roots))) h
  simp [RootPairing.SimpleGeckGroup.positiveUnit_val,
    RootPairing.SimpleGeckGroup.positiveMatrix_formula, eDividedPower, eMatrix, hij] at he

/-- The concrete action moves the first positive simple curve over every nonzero ring. -/
theorem typeE6Pinned_moves_positive_zero {S : Type*} [CommRing S] [Nontrivial S] :
    typeE6PinnedUnitsEquiv S
      (RootPairing.SimpleGeckGroup.positiveUnit (typeE6RootPairing_baseEquiv 0) (1 : S)) ≠
      RootPairing.SimpleGeckGroup.positiveUnit (typeE6RootPairing_baseEquiv 0) (1 : S) := by
  rw [typeE6Pinned_positiveUnit, typeE6DiagramBasePermutation_numbered]
  apply typeE6PositiveUnit_ne
  intro h
  have hh := typeE6RootPairing_baseEquiv.injective h
  exact (by decide : (5 : Fin 6) ≠ 0) hh

end

end Theory.AlgebraicGroup.StandardRootSystem
