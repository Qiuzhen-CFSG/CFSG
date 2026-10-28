module

public import Theory.GroupTheory.BinaryMatrixSylowExponent
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Theory.SpecificGroups.PSU3.UniversalCover.Kernel

/-!
# Binary low-dimensional projective Sylow exponents

The actual special-linear and special-unitary carriers embed in matrices.
Their literal central projections therefore transport the fourth-power
bound to PSL in dimensions at most four and to ternary PSU, for every
Hermitian form. No Sylow model or order-recognition premise is needed.

Source: Aschbacher–Smith F.6.18, printed p.310; the nilpotent matrix
argument is isolated in BinaryMatrixSylowExponent.
-/

public section
open scoped MatrixGroups
namespace Theory.ClassicalSmallSylow
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem binary_psl_small_dimension_sylow_pow_four {n : ℕ} [NeZero n] (hn : n ≤ 4)
    (P : Sylow 2 PSL(n,F)) (x : P) : x ^ 4 = 1 :=
  Theory.GroupTheory.small_char_two_quotient_sylow_pow_four hn
    Matrix.SpecialLinearGroup.coeMonoidHom Matrix.SpecialLinearGroup.coeMonoidHom_injective
    (QuotientGroup.mk' (Subgroup.center SL(n,F))) (QuotientGroup.mk'_surjective _) P x

theorem binary_psu_three_sylow_pow_four
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (P : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) (x : P) : x ^ 4 = 1 := by
  let ρ : J.specialSubgroup →* Matrix (Fin 3) (Fin 3) F :=
    (Units.coeHom _).comp J.specialSubgroup.subtype
  have hρ : Function.Injective ρ := Units.val_injective.comp J.specialSubgroup.subtype_injective
  exact Theory.GroupTheory.small_char_two_quotient_sylow_pow_four (by decide : 3 ≤ 4)
    ρ hρ J.specialToProjective J.specialToProjective_surjective P x
end Theory.ClassicalSmallSylow
