module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
/-!
# The marked long root in the unitary point residual

The Hermitian diagonal long-root matrix fixes the first isotropic vector.
The first-column and last-row equations of that vector stabilizer show
that it commutes with the whole point residual. This identifies the long
root used in the orthogonal short-centralizer quotient with a root to
which the ambient right-center centralizer theorem applies.

Source: Aschbacher–Smith F.4.42, printed p.295 of `refs/quasithin.pdf`.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
/-- The original long-root matrix is central in the full point residual. -/
theorem longMark_mem_point_center : (longMark F σ hσ).val.val ∈
    (center (UnitaryFourPointLocal.localSU F (form F σ hσ))).map
      (UnitaryFourPointLocal.localSU F (form F σ hσ)).subtype := by
  have hz : (longMark F σ hσ).val.val ∈ UnitaryFourPointLocal.localSU F (form F σ hσ) := by
    rw [UnitaryFourPointLocal.mem_localSU]
    exact ⟨rfl,rfl,rfl,rfl⟩
  refine ⟨⟨_,hz⟩,mem_center_iff.mpr ?_,rfl⟩
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have hg := (UnitaryFourPointLocal.mem_localSU F _ g.val).mp g.property
  have hl := UnitaryFourPointLocal.last_row F σ hσ g.val g.property
  change g.val.val.val * (unipotentSU F σ hσ (longParameter F σ)).val.val =
    (unipotentSU F σ hσ (longParameter F σ)).val.val * g.val.val.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentSU, unipotentMatrix, longParameter, Matrix.mul_apply,
      Fin.sum_univ_succ, hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,
      hl.2.1,hl.2.2.1,hl.2.2.2,add_comm]
end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
