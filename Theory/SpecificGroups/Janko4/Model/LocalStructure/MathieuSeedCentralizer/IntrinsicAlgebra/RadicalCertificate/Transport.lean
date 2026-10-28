module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Finite

/-!
# Basis transport after raw completeness

This is the final linear-algebra assembly with raw completeness still an
explicit input. The owner must certify that input before exposing the requested
basis depending only on the kernel-range hypothesis. Every basis vector here
has underlying matrix exactly `ambientRadicalForm i`.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra

/-- The literal forms as elements of the actual intrinsic radical space. -/
def radicalFormVector (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin)
    (i : Fin 10) : radicalForms :=
  ⟨ambientRadicalForm i, ambientRadicalForm_mem_radicalForms hK i⟩

theorem radicalFormVector_linearIndependent
    (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin) :
    LinearIndependent (ZMod 2) (radicalFormVector hK) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hm := congrArg (fun R : radicalForms => (R : BinaryMatrix)) hc
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, radicalFormVector] at hm
  exact (Fintype.linearIndependent_iff.mp ambientRadicalForm_linearIndependent) c hm i

private theorem radicalFormVector_spanning
    (hcomplete : rawRadicalForms ≤ rawRadicalSpan)
    (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin) :
    ⊤ ≤ Submodule.span (ZMod 2) (Set.range (radicalFormVector hK)) := by
  intro R _
  have hR : (R : BinaryMatrix) ∈ rawRadicalForms := by
    rw [← radicalForms_eq_rawRadicalForms hK]
    exact R.property
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp (hcomplete hR)
  have he : ∑ i : Fin 10, c i • radicalFormVector hK i = R := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, radicalFormVector] using hc
  rw [← he]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Conditional assembly only: `hcomplete` is the still-required finite
elimination certificate, separate from the kernel geometry supplied by `hK`. -/
noncomputable def radicalBasisOfRawCompleteness
    (hcomplete : rawRadicalForms ≤ rawRadicalSpan)
    (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin) :
    Module.Basis (Fin 10) (ZMod 2) radicalForms :=
  Module.Basis.mk (radicalFormVector_linearIndependent hK)
    (radicalFormVector_spanning hcomplete hK)

theorem radicalBasisOfRawCompleteness_apply
    (hcomplete : rawRadicalForms ≤ rawRadicalSpan)
    (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin) (i : Fin 10) :
    (radicalBasisOfRawCompleteness hcomplete hK i : BinaryMatrix) = ambientRadicalForm i := by
  rw [radicalBasisOfRawCompleteness, Module.Basis.mk_apply]
  simp only [radicalFormVector]

theorem finrank_radicalForms_of_rawCompleteness
    (hcomplete : rawRadicalForms ≤ rawRadicalSpan)
    (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin) :
    Module.finrank (ZMod 2) radicalForms = 10 := by
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis (radicalBasisOfRawCompleteness hcomplete hK)

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
