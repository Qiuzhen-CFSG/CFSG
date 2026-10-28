module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.Transport
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.CosetSeparation.Rows

/-!
# Separation of the 126 actual Borel right cosets

The literal upper-root-and-full-torus Borel lies in the subgroup of matrices
whose last row is supported on its last coordinate. Its last diagonal entry
is nonzero, so left multiplication by a Borel element scales the last row.
The checked projective row separation therefore distinguishes the fixed
126 right cosets. Writing `rᵢ = (rᵢ rⱼ⁻¹) rⱼ` avoids evaluating matrix inverses.

`certificate_of_generation` supplies this separation proof to the actual
canonical transport certificate. Full generation remains the explicit premise
owned by the independent generation task and discharged by the parent group
certificate assembly; no coset-cardinality premise is needed here.

Source data: `Coordinates/source/upper_group_data.json`. Mathematical use:
Guralnick–Malle, Proposition 4.3, p.10, and Aschbacher–Smith K.2, p.453.
-/

public noncomputable section

open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.InvolutionConjugateBounds.Five.Embedding
open HermitianForm.OddPrimeSylow.NormalizedOuter
open HermitianForm.BorelTorus
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup

private theorem bottom_mul (g h : standardGroup fieldForm)
    (h0 : g.val.val 2 0 = 0) (h1 : g.val.val 2 1 = 0) (j : Fin 3) :
    (g * h).val.val 2 j = g.val.val 2 2 * h.val.val 2 j := by
  change (g.val.val * h.val.val) 2 j = _
  simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1]

private theorem bottom_nonzero (g : standardGroup fieldForm)
    (h0 : g.val.val 2 0 = 0) (h1 : g.val.val 2 1 = 0) : g.val.val 2 2 ≠ 0 := by
  have h := bottom_mul g g⁻¹ h0 h1 2
  rw [mul_inv_cancel] at h
  exact left_ne_zero_of_mul_eq_one h.symm

private def bottomSubgroup : Subgroup (standardGroup fieldForm) where
  carrier := {g | g.val.val 2 0 = 0 ∧ g.val.val 2 1 = 0}
  one_mem' := by constructor <;> rfl
  mul_mem' := by
    intro g h hg hh
    constructor
    · rw [bottom_mul g h hg.1 hg.2, hh.1, mul_zero]
    · rw [bottom_mul g h hg.1 hg.2, hh.2, mul_zero]
  inv_mem' := by
    intro g hg
    have hc := bottom_nonzero g hg.1 hg.2
    have h0 := bottom_mul g g⁻¹ hg.1 hg.2 0
    have h1 := bottom_mul g g⁻¹ hg.1 hg.2 1
    rw [mul_inv_cancel] at h0 h1
    exact ⟨(mul_eq_zero.mp h0.symm).resolve_left hc,
      (mul_eq_zero.mp h1.symm).resolve_left hc⟩

private theorem borel_le_bottom : standardBorel fieldForm ≤ bottomSubgroup := by
  apply sup_le
  · rintro _ ⟨z, rfl⟩
    constructor <;> rfl
  · rintro _ ⟨k, rfl⟩
    constructor <;> rfl

private theorem borel_last_row (b : standardBorel fieldForm) (g : standardGroup fieldForm) :
    ∃ c : Field, c ≠ 0 ∧ ∀ j, ((b : standardGroup fieldForm) * g).val.val 2 j =
      c * g.val.val 2 j := by
  have hb := borel_le_bottom b.property
  exact ⟨b.val.val.val 2 2, bottom_nonzero b.val hb.1 hb.2,
    bottom_mul b.val g hb.1 hb.2⟩

/-- The 126 fixed actual representatives lie in distinct Borel right cosets. -/
theorem representatives_separate : ∀ i j,
    representative i * (representative j)⁻¹ ∈ standardBorel fieldForm → i = j := by
  intro i j h
  let b : standardBorel fieldForm := ⟨representative i * (representative j)⁻¹, h⟩
  obtain ⟨c, hc, hrow⟩ := borel_last_row b (representative j)
  apply rawRepresentative_last_row_separates i j c hc
  have he : (b : standardGroup fieldForm) * representative j = representative i := by
    dsimp only [b]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  intro k
  simpa only [he, representative_val] using hrow k

/-- The canonical certificate with separation discharged for the fixed elements.
The full-generation premise remains with the group-certificate assembly owner. -/
def certificate_of_generation
    (hgen : Subgroup.closure (Set.range generator) = ⊤) : GroupCertificate :=
  certificate representatives_separate hgen

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup
