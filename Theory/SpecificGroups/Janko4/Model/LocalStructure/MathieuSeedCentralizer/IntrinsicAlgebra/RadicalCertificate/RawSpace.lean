module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Data

/-!
# Transport from columns to the intrinsic radical condition

The finite calculation uses multiplication by the saved kernel columns. If
those columns span the actual displacement kernel, annihilating that matrix
is exactly the radical condition in `Defs`. This uses no independence or
completeness assumption about the ten candidate forms.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra

/-- The raw radical condition, on the original ambient exterior space. -/
def rawRadicalForms : Submodule (ZMod 2) BinaryMatrix where
  carrier := {R | R ∈ ambientForms ∧ R * kernelColumns = 0}
  zero_mem' := ⟨ambientForms.zero_mem, by simp⟩
  add_mem' := by
    rintro R S ⟨hR, hRK⟩ ⟨hS, hSK⟩
    exact ⟨ambientForms.add_mem hR hS, by rw [Matrix.add_mul, hRK, hSK, add_zero]⟩
  smul_mem' := by
    rintro a R ⟨hR, hRK⟩
    exact ⟨ambientForms.smul_mem a hR, by rw [Matrix.smul_mul, hRK, smul_zero]⟩

theorem mem_rawRadicalForms (R : BinaryMatrix) :
    R ∈ rawRadicalForms ↔ R ∈ ambientForms ∧ R * kernelColumns = 0 := Iff.rfl

/-- The right-radical convention in `Defs` agrees exactly with the raw
column-multiplication convention. -/
theorem annihilates_kernel_iff (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin)
    (R : BinaryMatrix) :
    (∀ v ∈ kernelSpace, R *ᵥ v = 0) ↔ R * kernelColumns = 0 := by
  rw [hK]
  constructor
  · intro h
    apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    exact h _ ⟨v, rfl⟩
  · intro h v hv
    obtain ⟨w, rfl⟩ := hv
    change R *ᵥ (kernelColumns *ᵥ w) = 0
    rw [Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]

theorem mem_radicalForms_iff_raw (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin)
    (R : BinaryMatrix) :
    R ∈ radicalForms ↔ R ∈ ambientForms ∧ R * kernelColumns = 0 := by
  rw [mem_radicalForms, annihilates_kernel_iff hK]

theorem radicalForms_eq_rawRadicalForms
    (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin) :
    radicalForms = rawRadicalForms := by
  ext R
  exact mem_radicalForms_iff_raw hK R

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
