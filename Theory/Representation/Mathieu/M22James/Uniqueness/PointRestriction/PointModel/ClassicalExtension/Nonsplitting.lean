module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.Layers
import Mathlib.Tactic.FinCases
/-!
# Nonsplitting over both the binary and four-element fields

A diagonal element has distinct weights on the first and third quotient
coordinates and fixes the middle coordinate of the first block. Its norm
annihilates the corresponding quotient plane, so equivariance forces every
binary-linear section to have zero middle coordinate on that plane. One root
element contradicts this. In particular no assumption of field-linearity of
the section, semisimplicity, or a group classification is required.

Source context: the natural-by-dual point restriction used in James (1973),
Lemma 8.3, and Aschbacher–Smith H.12.1, printed pp.393–394.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel.Reference
open Matrix
private def separatingTorus : SL :=
  ⟨diagonal ![QuadraticAlgebra.omega, 1, QuadraticAlgebra.omega ^ 2], by
    rw [Matrix.det_diagonal]
    decide +kernel⟩

private lemma separatingTorus_coupling : coupling separatingTorus = 0 := by decide +kernel

private lemma separatingTorus_quotient :
    ((separatingTorus⁻¹).val.transpose.map (fun x => x ^ 2)) = separatingTorus.val := by
  decide +kernel

private lemma separatingTorus_first (v : V) : (operator separatingTorus v).1 1 = v.1 1 := by
  rw [operator_apply, separatingTorus_coupling, Matrix.zero_mulVec, add_zero]
  simp [separatingTorus, Matrix.mulVec_diagonal]

private lemma separatingTorus_norm (w : W) (hw : w 1 = 0) :
    quotientRepresentation separatingTorus (quotientRepresentation separatingTorus w) +
      quotientRepresentation separatingTorus w + w = 0 := by
  have hq (v : W) : quotientRepresentation separatingTorus v =
      separatingTorus.val *ᵥ v := by
    rw [quotientRepresentation_apply, separatingTorus_quotient]
  simp only [hq]
  have hn : separatingTorus.val * separatingTorus.val + separatingTorus.val + 1 =
      diagonal (![0,1,0] : W) := by decide +kernel
  calc
    _ = (separatingTorus.val * separatingTorus.val + separatingTorus.val + 1) *ᵥ w := by
      rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
    _ = 0 := by
      rw [hn]
      funext i
      fin_cases i <;> simp [Matrix.mulVec_diagonal, hw]


private lemma root_coupling : coupling (Representation.SL3FourNaturalDual.root 1) =
    (!![0,1,0; 1,0,0; 0,0,0] : Matrix (Fin 3) (Fin 3) F) := by decide +kernel

private lemma root_first (v : V) :
    (operator (Representation.SL3FourNaturalDual.root 1) v).1 1 = v.1 1 + v.2 0 := by
  rw [operator_apply, root_coupling]
  simp [Representation.SL3FourNaturalDual.root, dotProduct, Fin.sum_univ_three]

private lemma root_quotient :
    quotientRepresentation (Representation.SL3FourNaturalDual.root 1) (![1,0,0] : W) =
      ![1,0,1] := by decide +kernel

/-- Even a binary-linear equivariant section of the quotient is impossible. -/
theorem no_binary_section (s : W →ₗ[ZMod 2] V)
    (hs : ∀ w, (s w).2 = w)
    (he : ∀ g w, s (quotientRepresentation g w) = operator g (s w)) : False := by
  have hz (w : W) (hw : w 1 = 0) : (s w).1 1 = 0 := by
    have ht (u : W) : (s (quotientRepresentation separatingTorus u)).1 1 = (s u).1 1 := by
      rw [he, separatingTorus_first]
    have hn := congrArg (fun v : V => v.1 1)
      (congrArg s (separatingTorus_norm w hw))
    simp only [map_add, map_zero, Prod.fst_add, Pi.add_apply, ht] at hn
    simpa only [CharTwo.add_self_eq_zero, zero_add, Prod.fst_zero, Pi.zero_apply] using hn
  have h := congrArg (fun v : V => v.1 1)
    (he (Representation.SL3FourNaturalDual.root 1) ![1,0,0])
  rw [root_quotient, root_first, hs, hz _ (by rfl), hz _ (by rfl)] at h
  exact zero_ne_one h

/-- In particular the extension does not split over the four-element field. -/
theorem no_field_section (s : W →ₗ[F] V)
    (hs : ∀ w, (s w).2 = w)
    (he : ∀ g w, s (quotientRepresentation g w) = operator g (s w)) : False :=
  no_binary_section (s.restrictScalars (ZMod 2)) hs he
/-- The binary quotient epimorphism has no section in the representation category. -/
theorem binaryQuotientProjection_not_split :
    ¬ ∃ s : binaryQuotientRepresentation.IntertwiningMap binaryRepresentation,
      Function.RightInverse s binaryQuotientProjection := by
  rintro ⟨s, hs⟩
  exact no_binary_section s.toLinearMap hs (fun g w =>
    LinearMap.congr_fun (s.isIntertwining' g) w)

/-- The field quotient epimorphism has no section in the representation category. -/
theorem quotientProjection_not_split :
    ¬ ∃ s : quotientRepresentation.IntertwiningMap representation,
      Function.RightInverse s quotientProjection := by
  rintro ⟨s, hs⟩
  exact no_field_section s.toLinearMap hs (fun g w =>
    LinearMap.congr_fun (s.isIntertwining' g) w)

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel.Reference
