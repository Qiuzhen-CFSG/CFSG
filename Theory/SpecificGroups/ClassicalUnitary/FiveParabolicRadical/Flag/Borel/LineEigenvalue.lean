module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Split
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourScalarKernel

/-!
# The projective line character on the residual

Every matrix in the line radical--SU₃ subgroup fixes the marked line
pointwise. A special-unitary lift of its projective image can therefore act
on that line only by a fifth root of unity. The proof uses the exact kernel
of SU₅ to its projective image, with no replacement by a larger scalar group.
This detects plane-Levi torus elements outside the line residual.

Source: Aschbacher--Smith F.1.3 and F.1.12(7), printed pp.260 and 263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.Flag.Borel
open LineCore.Parabolic
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

/-- An eigenvalue on the marked line of an actual residual lift is a fifth root. -/
theorem residual_line_eigenvalue_fifth (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x ^ 4) (A : J.specialSubgroup) (a : F)
    (ha : linearAction J A ![1,1,0,0,0] = a • ![1,1,0,0,0])
    (hA : project J A ∈ (radicalLeviSubgroup J hJ).map (lineParabolic J).subtype) :
    a ^ 5 = 1 := by
  obtain ⟨g, ⟨x, rfl⟩, he⟩ := hA
  let B := toSU J hJ x.left * leviSU J hJ x.right
  have hB : project J B = project J A := by
    rw [map_mul]
    exact he
  have hk : A * B⁻¹ ∈ (project J).ker := by
    change project J (A * B⁻¹) = 1
    rw [map_mul, map_inv, hB, mul_inv_cancel]
  obtain ⟨l, hl⟩ := (scalarToKernel_bijective J hconj).surjective ⟨A * B⁻¹, hk⟩
  have hl' : (scalarToKernel J hconj l).val * B = A := by
    have hh := congrArg Subtype.val hl
    rw [hh, mul_assoc, inv_mul_cancel, mul_one]
  have hfix : linearAction J B ![1,1,0,0,0] = ![1,1,0,0,0] := by
    change linearAction J (toSU J hJ x.left * leviSU J hJ x.right) _ = _
    rw [map_mul]
    change linearAction J (toSU J hJ x.left)
      (linearAction J (leviSU J hJ x.right) ![1,1,0,0,0]) = _
    rw [leviSU_fixes_line J hJ x.right _ (by simp [line])]
    exact toSU_fixes_line J hJ x.left _ (by simp [line])
  have hact : linearAction J A ![1,1,0,0,0] = (l.val : F) • ![1,1,0,0,0] := by
    rw [← hl', map_mul]
    change linearAction J (scalarToKernel J hconj l).val (linearAction J B _) = _
    rw [hfix]
    exact Matrix.diagonal_const_mulVec _ _
  have heq : a = (l.val : F) := by
    have hh := congrFun (ha.symm.trans hact) 0
    simpa using hh
  rw [heq]
  exact (mem_rootsOfUnity' 5 l.val).mp l.property
end Theory.SpecificGroups.UnitaryFive.Flag.Borel
