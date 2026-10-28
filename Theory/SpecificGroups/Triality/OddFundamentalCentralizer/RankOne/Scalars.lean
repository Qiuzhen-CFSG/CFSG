module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.RankOne.Construction

/-!
# Scalar involutions on the integral D4 lattice

In the common Cartan-plus-root coordinates, each rank-one scalar is a diagonal
sign matrix. The three arm signs coincide. An adjacent scalar changes the sign
of each degree-one positive-root coefficient and preserves degree two, proving
the exact identity hᵢ(-1)xⱼ(t) = xⱼ(-t)hᵢ(-1). The finite sign identities are
checked over ℤ before specializing to a field.

Source: GLS3 §§2.4 and 2.6, especially Proposition 2.6.2
(`refs/KGroup/GLS3/chapter2.tex`). These are the scalar-kernel calculations
needed by the odd triality fundamental subgroup of Aschbacher–Smith A.2.17.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.OddFundamentalCentralizer.RankOne
open Parabolics Parabolics.RankOneMatrices
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

def globalEquiv : FlatIndex ≃ LatticeIndex :=
  Equiv.sumCongr (typeDRootPairing_baseEquiv 2) rootEnumeration

def blockToGlobal (i : Fin 4) : BlockIndex ≃ FlatIndex :=
  blockToFlat.trans (Equiv.sumCongr (Equiv.refl _) (rootOrder i))

lemma globalEquiv_blockToGlobal (i : Fin 4) (r : BlockIndex) :
    globalEquiv (blockToGlobal i r) = latticeEquiv i r := by
  rcases r with (r | r) | r <;> rfl

def scalarSign (i : Fin 4) : FlatIndex → ℤ
  | .inl _ => 1
  | .inr r => if i = 1 then
      if r.val < 8 ∨ 16 ≤ r.val then -1 else 1
    else if 4 ≤ r.val ∧ r.val < 20 then -1 else 1

def blockSign : BlockIndex → ℤ
  | .inr (.inl _) => -1
  | _ => 1

set_option maxRecDepth 4000 in
lemma scalarSign_blockToGlobal (i : Fin 4) (r : BlockIndex) :
    scalarSign i (blockToGlobal i r) = blockSign r := by
  revert i r
  decide +kernel

lemma blockMatrix_neg_one (i : Fin 4) {F : Type*} [CommRing F] (r s : BlockIndex) :
    blockMatrix i (-1 : SL(2, F)) r s =
      if r = s then (blockSign r : F) else 0 := by
  rcases r with (r | r) | (⟨r, k⟩ | r) <;>
    rcases s with (s | s) | (⟨s, l⟩ | s)
  all_goals
    simp [blockMatrix, specialBlock, blockSign, SpecialLinearGroup.coe_neg,
      SpecialLinearGroup.coe_one, Matrix.one_apply, Matrix.blockDiagonal]
  all_goals try (guard_hyp r : Fin 2; fin_cases r)
  all_goals try (guard_hyp s : Fin 2; fin_cases s)
  all_goals simp

def scalarMatrix {F : Type*} [CommRing F] (i : Fin 4) :
    Matrix LatticeIndex LatticeIndex F :=
  Matrix.diagonal fun r => (scalarSign i (globalEquiv.symm r) : F)

lemma scalarMatrix_entry {F : Type*} [CommRing F] (i : Fin 4) (r s : FlatIndex) :
    scalarMatrix (F := F) i (globalEquiv r) (globalEquiv s) =
      if r = s then (scalarSign i r : F) else 0 := by
  simp [scalarMatrix, Matrix.diagonal_apply, globalEquiv.injective.eq_iff]

lemma ambientHom_neg_one {F : Type*} [CommRing F] (i : Fin 4) :
    (ambientHom i (-1 : SL(2, F))).val = scalarMatrix i := by
  ext r s
  obtain ⟨r, rfl⟩ := (latticeEquiv i).surjective r
  obtain ⟨s, rfl⟩ := (latticeEquiv i).surjective s
  rw [ambientHom_entry, blockMatrix_neg_one, ← globalEquiv_blockToGlobal,
    ← globalEquiv_blockToGlobal, scalarMatrix_entry]
  simp only [(blockToGlobal i).injective.eq_iff, scalarSign_blockToGlobal]

lemma scalarMatrix_arms {F : Type*} [CommRing F] (i j : Fin 4)
    (hi : i ≠ 1) (hj : j ≠ 1) : scalarMatrix (F := F) i = scalarMatrix j := by
  unfold scalarMatrix
  congr 1
  funext r
  congr 1
  cases globalEquiv.symm r <;> simp [scalarSign, hi, hj]

lemma pinned_scalar_arms (P : Parameters) (i j : Fin 4)
    (hi : i ≠ 1) (hj : j ≠ 1) :
    (pinnedRankOneMaps P).hom i (-1) = (pinnedRankOneMaps P).hom j (-1) := by
  apply Subtype.ext
  apply Units.ext
  simp only [pinnedRankOneMaps_hom_val, ambientHom_neg_one]
  exact scalarMatrix_arms i j hi hj

def flatToGlobal (i : Fin 4) : FlatIndex ≃ FlatIndex :=
  Equiv.sumCongr (Equiv.refl _) (rootOrder i)

lemma globalEquiv_flatToGlobal (i : Fin 4) (r : FlatIndex) :
    globalEquiv (flatToGlobal i r) = flatEquiv i r := by
  cases r <;> rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma scalarSign_eData (i j : Fin 4) (hij : cartanAbs i j = 1) (r s : FlatIndex) :
    scalarSign i (flatToGlobal j r) * eData j r s =
      -(eData j r s * scalarSign i (flatToGlobal j s)) := by
  revert i j r s
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma scalarSign_eTwo (i j : Fin 4) (r s : FlatIndex) :
    scalarSign i (flatToGlobal j r) * (if r = .inr 0 ∧ s = .inr 1 then 1 else 0) =
      (if r = .inr 0 ∧ s = .inr 1 then 1 else 0) * scalarSign i (flatToGlobal j s) := by
  revert i j r s
  decide +kernel

lemma scalarMatrix_positive_swap {F : Type*} [CommRing F]
    (i j : Fin 4) (hij : cartanAbs i j = 1) (t : F) :
    scalarMatrix i * RootPairing.SimpleGeckGroup.positiveMatrix
        (typeDRootPairing_baseEquiv 2 j) t =
      RootPairing.SimpleGeckGroup.positiveMatrix
        (typeDRootPairing_baseEquiv 2 j) (-t) * scalarMatrix i := by
  ext r s
  obtain ⟨r, rfl⟩ := (flatEquiv j).surjective r
  obtain ⟨s, rfl⟩ := (flatEquiv j).surjective s
  simp only [scalarMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    positiveMatrix_entry]
  rw [← globalEquiv_flatToGlobal, ← globalEquiv_flatToGlobal]
  simp only [Equiv.symm_apply_apply]
  have he : (scalarSign i (flatToGlobal j r) : F) * (eData j r s : F) =
      -((eData j r s : F) * (scalarSign i (flatToGlobal j s) : F)) := by
    simpa only [Int.cast_mul, Int.cast_neg] using
      congrArg (fun z : ℤ => (z : F)) (scalarSign_eData i j hij r s)
  have htwo : (scalarSign i (flatToGlobal j r) : F) *
      (if r = .inr 0 ∧ s = .inr 1 then 1 else 0) =
      (if r = .inr 0 ∧ s = .inr 1 then 1 else 0) *
        (scalarSign i (flatToGlobal j s) : F) := by
    simpa only [Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_zero] using
      congrArg (fun z : ℤ => (z : F)) (scalarSign_eTwo i j r s)
  by_cases hrs : r = s
  · subst s
    linear_combination t * he + t ^ 2 * htwo
  · simp only [if_neg hrs]
    linear_combination t * he + t ^ 2 * htwo


lemma pinned_scalar_positive_swap (P : Parameters) (i j : Fin 4)
    (hij : cartanAbs i j = 1) (t : ExtensionField P) :
    (pinnedRankOneMaps P).hom i (-1) * positiveRoot P j t =
      positiveRoot P j (-t) * (pinnedRankOneMaps P).hom i (-1) := by
  apply Subtype.ext
  apply Units.ext
  change (ambientHom i (-1)).val *
      RootPairing.SimpleGeckGroup.positiveMatrix (typeDRootPairing_baseEquiv 2 j) t =
    RootPairing.SimpleGeckGroup.positiveMatrix (typeDRootPairing_baseEquiv 2 j) (-t) *
      (ambientHom i (-1)).val
  rw [ambientHom_neg_one]
  exact scalarMatrix_positive_swap i j hij t

end Triality.Standard.OddFundamentalCentralizer.RankOne
