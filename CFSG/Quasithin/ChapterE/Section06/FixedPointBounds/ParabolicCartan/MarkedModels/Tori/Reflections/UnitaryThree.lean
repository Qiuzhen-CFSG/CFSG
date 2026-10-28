module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.UnitaryThree
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# Reflection of the fixed-field unitary torus

The Hermitian Weyl matrix interchanges the two isotropic coordinates and
inverts the specified diag(a,1,a⁻¹) torus for fixed-field units a. This is
not an assertion about the full quadratic-field torus. The original
root–torus Borel is a product of the named root and torus images; its
matrix products have zero (2,0) entry, excluding the Weyl element even
modulo projective scalars. The proof retains the stored Hermitian form
and its actual fixed field.

Source: Aschbacher--Smith E.6.27, printed p.257, with the marked Borel
models from E.2.2. These witnesses feed the same chosen cyclic subgroup
and Hall-subgroup lifting in the original parabolic consumer.
-/
public section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
variable {E : Type*} [Field E]

private theorem unitaryReflection_intertwine (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (a : (unitaryFixedField J)ˣ) :
    hermitianWeylPSU J hJ * (psu3Torus J hJ a : ProjectiveSpecialUnitaryMatrixGroup J) =
      (psu3Torus J hJ a⁻¹ : ProjectiveSpecialUnitaryMatrixGroup J) * hermitianWeylPSU J hJ := by
  apply Subtype.ext
  change ProjGenLinGroup.mk hermitianWeylGL *
      ProjGenLinGroup.mk (hermitianTorusGL J (unitaryFixedUnits J a⁻¹)) =
    ProjGenLinGroup.mk (hermitianTorusGL J (unitaryFixedUnits J (a⁻¹)⁻¹)) *
      ProjGenLinGroup.mk hermitianWeylGL
  rw [← map_mul,← map_mul]
  apply congrArg ProjGenLinGroup.mk
  apply Units.ext
  change hermitianWeylMatrix * hermitianTorusMatrix J (unitaryFixedUnits J a⁻¹) =
    hermitianTorusMatrix J (unitaryFixedUnits J (a⁻¹)⁻¹) * hermitianWeylMatrix
  rw [unitaryFixedTorus_matrix,unitaryFixedTorus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylMatrix,Matrix.mul_diagonal,Matrix.diagonal_mul]

private theorem unitaryReflection_not_mem [Finite E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    hermitianWeylPSU J hJ ∉ psu3Borel J hJ := by
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let U := (hermitianUnipotentPSU J hJ).range
  let T := (hermitianTorusPSU J hJ).range
  have hn : T ≤ normalizer (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rintro _ ⟨a,rfl⟩
    apply mem_normalizer_fintype
    rintro _ ⟨z,rfl⟩
    refine ⟨hermitianTorusAction J a z,?_⟩
    rw [hermitianTorusPSU_mul_unipotent,mul_assoc,mul_inv_cancel,mul_one]
  intro hw
  have hh : hermitianWeylPSU J hJ ∈ (U:Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (T:Set _) := by
    rw [← coe_mul_of_right_le_normalizer_left U T hn]
    exact hw
  obtain ⟨u,⟨z,rfl⟩,t,⟨a,rfl⟩,he⟩ := hh
  have hp : ProjGenLinGroup.mk (hermitianUnipotentGL J z * hermitianTorusGL J a) =
      ProjGenLinGroup.mk hermitianWeylGL := by
    simpa only [map_mul,Subgroup.coe_mul,hermitianUnipotentPSU_val,
      hermitianTorusPSU_val,hermitianWeylPSU_val] using congrArg Subtype.val he
  obtain ⟨c,hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have hh := congrArg (fun A : GL (Fin 3) E => A.val 2 0) hc
  simp [GeneralLinearGroup.coe_scalar,hermitianWeylGL,hermitianWeylMatrix,
    hermitianUnipotentGL,hermitianUnipotentMatrix,hermitianTorusGL,
    hermitianTorusMatrix,Matrix.mul_apply,Fin.sum_univ_three] at hh

theorem exists_psu3Torus_reflection [Finite E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    ∃ w : ProjectiveSpecialUnitaryMatrixGroup J, w ∉ psu3Borel J hJ ∧
      ∀ a : (unitaryFixedField J)ˣ,
        w * (psu3Torus J hJ a : ProjectiveSpecialUnitaryMatrixGroup J) * w⁻¹ =
          (psu3Torus J hJ a : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ := by
  refine ⟨hermitianWeylPSU J hJ,unitaryReflection_not_mem J hJ,?_⟩
  intro a
  rw [unitaryReflection_intertwine,mul_inv_cancel_right]
  exact congrArg Subtype.val (map_inv (psu3Torus J hJ) a)
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
