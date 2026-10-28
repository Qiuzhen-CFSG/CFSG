module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCenterReduction
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalForm.Invariance

/-!
# The invariant-form certificate for the Lyons involution subgroup

The explicit form is preserved by both literal local generators because it is
preserved by the ambient matrix group. For T = (ab)^7, invariance and T² = I
give TᵀF = FT. Expanding preservation of uI + vT and evaluating entries (0,0)
and (0,1) gives u² + v² = 1 and 3(u² + v²) + 2uv = 3. A kernel check over
F₅ leaves exactly I, T, -I and -T. No determinant assumption is needed.

Source: R. A. Wilson et al., ATLAS LyG1-f5r111B0 and LyG1-max4W1;
original data and attribution are in `Atlas111Source/` and
`Atlas111InvolutionSource/`. Form candidates and their certificate generator
are retained in `Atlas111InvolutionLocalForm/source/`.
-/

namespace Lyons.SimplicityCertificate

open Atlas111LocalFormCertificate

private theorem scalar_expansion (F T : AtlasMatrix) (hT : T * T = 1)
    (hF : T.transpose * F * T = F) (u v : ZMod 5) :
    (u • (1 : AtlasMatrix) + v • T).transpose * F * (u • 1 + v • T) =
      (u*u + v*v) • F + (u*v + v*u) • (F*T) := by
  have hcomm : T.transpose * F = F * T := by
    have hh := congrArg (fun M : AtlasMatrix => M * T) hF
    simpa only [Matrix.mul_assoc, hT, mul_one] using hh
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
    add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul]
  rw [hF, hcomm]
  module

private theorem scalar_choices (u v : ZMod 5) (h : u*u + v*v = 1)
    (h' : (u*u + v*v)*3 + (u*v+v*u) = 3) :
    (u = 1 ∧ v = 0) ∨ (u = 0 ∧ v = 1) ∨
    (u = -1 ∧ v = 0) ∨ (u = 0 ∧ v = -1) := by
  revert h h'
  revert u v
  decide +kernel

private theorem four_choices (F T : AtlasMatrix) (hT : T * T = 1)
    (hF : T.transpose * F * T = F)
    (h00 : F 0 0 = 1) (h01 : F 0 1 = 3)
    (ht00 : (F*T) 0 0 = 0) (ht01 : (F*T) 0 1 = 1)
    (u v : ZMod 5)
    (h : (u • (1 : AtlasMatrix) + v • T).transpose * F * (u • 1 + v • T) = F) :
    u • (1 : AtlasMatrix) + v • T = 1 ∨
    u • (1 : AtlasMatrix) + v • T = T ∨
    u • (1 : AtlasMatrix) + v • T = -(1 : AtlasMatrix) ∨
    u • (1 : AtlasMatrix) + v • T = -T := by
  rw [scalar_expansion F T hT hF] at h
  have h0 := congrArg (fun M : AtlasMatrix => M 0 0) h
  have h1 := congrArg (fun M : AtlasMatrix => M 0 1) h
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    h00, ht00, mul_one, mul_zero, add_zero] at h0
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    h01, ht01, mul_one] at h1
  rcases scalar_choices u v h0 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [one_smul, zero_smul, zero_add, add_zero, neg_smul, or_true, true_or]

private theorem represented_square (g : LyonsGroup) (h : g ^ 2 = 1) :
    matrixRepresentation g * matrixRepresentation g = 1 := by
  rw [← map_mul, ← pow_two, h, map_one]

/-- The explicit invariant form restricts the local scalar commutant to four matrices. -/
public theorem involutionLocal_form_certificate : InvolutionLocalFormCertificate := by
  have hT := represented_square involutionLocalT involutionLocalT_sq
  exact ⟨formMatrix, ambient_preserves_form involutionLocalA,
    ambient_preserves_form involutionLocalB,
    four_choices formMatrix (matrixRepresentation involutionLocalT) hT
      (ambient_preserves_form involutionLocalT) form_00 form_01 form_t_00 form_t_01⟩

end Lyons.SimplicityCertificate
