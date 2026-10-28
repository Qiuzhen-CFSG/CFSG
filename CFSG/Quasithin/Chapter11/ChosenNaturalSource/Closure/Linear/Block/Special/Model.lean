module

public import Theory.SpecificGroups.PSL3.PointRadicalGeneration

/-!
# The common fixed space of the marked point radical

Two coordinate transvections force a common fixed vector onto the point.
Conjugation transports this calculation to any field line. Center.lean
applies it to the actual starred closure under the given SL₃ marking.
Source: Aschbacher--Smith 11.5.7, refs/quasithin.pdf, printed p.782.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
open Matrix.PSL3.PointRadicalGeneration
open Matrix.PSL3.RootPlaneGeometry Matrix.PSL3Even.UnipotentGeometry
variable {F : Type*} [Field F]

private theorem standard_radical_fixed (v : Fin 3 → F)
    (hv : ∀ a ∈ radical (standardPoint (F := F)), a.val *ᵥ v = v) :
    v ∈ standardPoint (F := F) := by
  have h1 := congrFun (hv (specialLinear F ⟨1,0,0⟩)
    (radical_standardPoint.ge ((mem_rootPlaneSL_point F _).mpr ⟨1,0,rfl⟩))) 0
  have h2 := congrFun (hv (specialLinear F ⟨0,0,1⟩)
    (radical_standardPoint.ge ((mem_rootPlaneSL_point F _).mpr ⟨0,1,rfl⟩))) 0
  change (matrix F _ *ᵥ v) 0 = v 0 at h1 h2
  simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
  exact (mem_standardPoint v).mpr ⟨h1, h2⟩

/-- A full point radical has exactly its marked point as common fixed space. -/
theorem radical_fixed (P : Submodule F (Fin 3 → F))
    (hP : Module.finrank F P = 1) (v : Fin 3 → F) :
    (∀ a ∈ radical P, a.val *ᵥ v = v) ↔ v ∈ P := by
  constructor
  · intro hv
    obtain ⟨s, hs⟩ := exists_standardPoint_conjugator P hP
    rw [← hs, mem_conjugatePoint]
    apply standard_radical_fixed
    intro a ha
    have hm : s⁻¹ * a * s ∈ radical P := by
      rw [← hs, ← radical_conjugate]
      exact ⟨a, ha, by simp⟩
    have hh := congrArg (fun w : Fin 3 → F => s • w) (hv _ hm)
    change s • ((s⁻¹ * a * s) • v) = s • v at hh
    change a • (s • v) = s • v
    simpa only [mul_smul, smul_inv_smul] using hh
  · exact fun hv a ha => ha.1 v hv

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
