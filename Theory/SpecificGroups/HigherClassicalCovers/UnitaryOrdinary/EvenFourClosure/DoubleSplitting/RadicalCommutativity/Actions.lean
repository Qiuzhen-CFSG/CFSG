module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting.RadicalCommutativity.Coordinates
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Realizing the torus and Levi actions downstairs

The extra torus matrix is `diag(1,c,c⁻¹,1)` for a nonzero fixed-field scalar.
It belongs to the original standard special unitary group and realizes the
specified congruence on every Hermitian unipotent. The existing SL₂ Levi lifts
realize all determinant-one congruences. Commutator pairings in any central
extension are invariant under these literal conjugations.

Source: the plane-parabolic calculation for Aschbacher–Smith I.1.3–4,
printed pp.407–408, and GLS3 §6.1.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical
open Representation.OrthogonalFourMinus
open scoped commutatorElement IsMulCommutative

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting.RadicalCommutativity

variable (F : Type*) [Field F] [Finite F] [CharP F 2]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "K" => FixedBy.subfield F σ
local notation "H" => hermitianMatrices F σ
local notation "G" => SU F (form F σ hσ)

/-- The exhaustive radical parametrization in the original SU₄ group. -/
def unipotentMap : Multiplicative H →* G :=
  (localFactor F (form F σ hσ)).subtype.comp
    ((radical F σ hσ).subtype.comp (unipotent F σ hσ))

@[simp] theorem unipotentMap_apply (X : H) :
    unipotentMap F σ hσ (.ofAdd X) = unipotentSU F σ hσ X := rfl

/-- The ambient diagonal matrix for the extra plane torus. -/
def torusDiagonal (c : K) : Matrix (Fin 4) (Fin 4) F :=
  diagonal ![1,(c : F),(c : F)⁻¹,1]

omit [Finite F] [CharP F 2] in
/-- The marked two-by-two torus congruence, as a plain matrix identity. -/
theorem torus_congruence (c : K) (X : Mat F) :
    torusMatrix F σ c * X * adjoint σ (torusMatrix F σ c) =
      !![X 0 0,(c : F) * X 0 1;(c : F) * X 1 0,(c : F) * c * X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMatrix, adjoint, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, mul_assoc, mul_comm]

omit [Finite F] [CharP F 2] in
/-- Multiplication of the plain ambient matrices realizes that congruence. -/
theorem torusDiagonal_unipotent (c : K) (hc : c ≠ 0) (X : Mat F) :
    torusDiagonal F σ c * unipotentMatrix F X =
      unipotentMatrix F (torusMatrix F σ c * X * adjoint σ (torusMatrix F σ c)) *
        torusDiagonal F σ c := by
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  rw [torus_congruence]
  ext i j
  simp only [torusDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [unipotentMatrix, hcF, mul_assoc, mul_comm, mul_left_comm]

/-- A full-parabolic element whose determinant on the marked plane is `c`. -/
def torusSU (c : K) (hc : c ≠ 0) : G := by
  let D := torusDiagonal F σ c
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  have hd : D.det = 1 := by simp [D, torusDiagonal, Matrix.det_diagonal, Fin.prod_univ_succ, hcF]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero D (by rw [hd]; exact one_ne_zero), ?_, Units.ext hd⟩
  change (form F σ hσ).conjTranspose D * gram F * D = gram F
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [D, torusDiagonal, form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_succ, hcF]

omit [Finite F] [CharP F 2] in
@[simp] theorem torusSU_val (c : K) (hc : c ≠ 0) :
    (torusSU F σ hσ c hc).val.val = torusDiagonal F σ c := rfl

omit [CharP F 2] in
/-- The torus element lies in the full stabilizer of the marked plane. -/
theorem torusSU_mem_plane (c : K) (hc : c ≠ 0) :
    torusSU F σ hσ c hc ∈ planeParabolicSU F (form F σ hσ) := by
  rw [mem_planeParabolicSU]
  simp [torusSU_val, torusDiagonal]

/-- Literal conjugation by the extra torus in the original SU₄ carrier. -/
theorem torusSU_conj (c : K) (hc : c ≠ 0) (X : H) :
    torusSU F σ hσ c hc * unipotentMap F σ hσ (.ofAdd X) * (torusSU F σ hσ c hc)⁻¹ =
      unipotentMap F σ hσ (.ofAdd (action F σ hσ (torusMatrix F σ c) X)) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  apply Units.ext
  change torusDiagonal F σ c * unipotentMatrix F X.val =
    unipotentMatrix F (torusMatrix F σ c * X.val * adjoint σ (torusMatrix F σ c)) *
      torusDiagonal F σ c
  exact torusDiagonal_unipotent F σ c hc X.val

/-- The published SL₂ Levi realizes every determinant-one congruence. -/
theorem leviSU_conj (A : SpecialLinearGroup (Fin 2) F) (X : H) :
    UnitaryFourPlaneRadical.leviSU F σ hσ A * unipotentMap F σ hσ (.ofAdd X) *
      (UnitaryFourPlaneRadical.leviSU F σ hσ A)⁻¹ =
        unipotentMap F σ hσ (.ofAdd (action F σ hσ A.val X)) := by
  have he := unipotentSU_conj F σ hσ (UnitaryFourPlaneRadical.levi F σ hσ A) X
  rw [factorRestriction_levi] at he
  have hA : hermitianCongruence F σ hσ A X = action F σ hσ A.val X := rfl
  rw [hA] at he
  change UnitaryFourPlaneRadical.leviSU F σ hσ A * unipotentSU F σ hσ X *
    (UnitaryFourPlaneRadical.leviSU F σ hσ A)⁻¹ = _ at he
  simpa only [unipotentMap_apply] using he

/-- Commutator pairings through a central extension are invariant under each
realized ambient conjugation, with the original quotient map retained. -/
theorem pairing_invariant {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f)
    (B : H →+ H →+ Additive (Subgroup.center E))
    (hB : ∀ (X Y : H) (a b : E), f a = unipotentMap F σ hσ (.ofAdd X) →
      f b = unipotentMap F σ hσ (.ofAdd Y) → ((B X Y).toMul : E) = ⁅a,b⁆)
    (T : H → H) (g : G)
    (hg : ∀ X, g * unipotentMap F σ hσ (.ofAdd X) * g⁻¹ =
      unipotentMap F σ hσ (.ofAdd (T X))) (X Y : H) : B (T X) (T Y) = B X Y := by
  obtain ⟨e, he⟩ := hf g
  obtain ⟨a, ha⟩ := hf (unipotentMap F σ hσ (.ofAdd X))
  obtain ⟨b, hb⟩ := hf (unipotentMap F σ hσ (.ofAdd Y))
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [hB (T X) (T Y) (e * a * e⁻¹) (e * b * e⁻¹)
    (by rw [map_mul, map_mul, map_inv, he, ha, hg])
    (by rw [map_mul, map_mul, map_inv, he, hb, hg]),
    ← conjugate_commutatorElement, ← hB X Y a b ha hb]
  rw [Subgroup.mem_center_iff.mp (B X Y).toMul.property e]
  simp [mul_assoc]

/-- Every lift of any two Hermitian unipotents commutes when the fixed field
contains a scalar different from zero and one. No kernel-order bound is used. -/
theorem commute_unipotent_lifts {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (c : K) (hc : c ≠ 0) (hc1 : c ≠ 1)
    (X Y : H) {a b : E}
    (ha : f a = unipotentMap F σ hσ (.ofAdd X))
    (hb : f b = unipotentMap F σ hσ (.ofAdd Y)) : Commute a b := by
  obtain ⟨B, hB⟩ := CentralExtension.exists_lift_commutator_pairing f hf hk
    (unipotentMap F σ hσ)
  have hT (U V : H) : B (action F σ hσ (torusMatrix F σ c) U)
      (action F σ hσ (torusMatrix F σ c) V) = B U V :=
    pairing_invariant F σ hσ f hf B hB _ (torusSU F σ hσ c hc)
      (torusSU_conj F σ hσ c hc) U V
  have hL (A : SpecialLinearGroup (Fin 2) F) (U V : H) :
      B (action F σ hσ A.val U) (action F σ hσ A.val V) = B U V :=
    pairing_invariant F σ hσ f hf B hB _ (UnitaryFourPlaneRadical.leviSU F σ hσ A)
      (leviSU_conj F σ hσ A) U V
  have hz := invariant_pairing_zero F σ hσ B c hc1 hT hL X Y
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← hB X Y a b ha hb, hz]
  rfl

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting.RadicalCommutativity
