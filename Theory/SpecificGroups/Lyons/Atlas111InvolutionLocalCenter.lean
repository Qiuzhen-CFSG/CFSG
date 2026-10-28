module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCenterReduction

/-!
# Assembly of the local center bound from matrix certificates

A central element commutes with both local generators. The commutant certificate
puts its matrix in the span of `1` and `t`. The invariant-form certificate cuts
this span down to `±1` and `±t`, and determinant one in odd dimension excludes
the negative choices. Faithfulness then gives the required group equality.

The two finite matrix certificates remain explicit hypotheses here; this module
does not yet assert the unconditional local center bound. The subgroup-membership
restriction is used to propagate preservation of the form.

Source: the concrete ATLAS representation and `LyG1-max4W1` subgroup program,
with attribution in `Atlas111Source/` and `Atlas111InvolutionSource/`.
-/

namespace Lyons.SimplicityCertificate

/-- The required local center bound follows from the two independent concrete
matrix certificates, without ambient simplicity, maximality, or an order premise. -/
public theorem involutionLocal_center_of_matrix_certificates
    (hcommutant : InvolutionLocalCommutantCertificate)
    (hform : InvolutionLocalFormCertificate)
    (z : involutionLocalSubgroup) (hz : z ∈ Subgroup.center involutionLocalSubgroup) :
    (z : LyonsGroup) = 1 ∨ (z : LyonsGroup) = involutionLocalT := by
  obtain ⟨u, v, heq⟩ := hcommutant (matrixRepresentation (z : LyonsGroup))
    (involutionLocal_center_matrix_commutes z hz _ involutionLocalA_mem)
    (involutionLocal_center_matrix_commutes z hz _ involutionLocalB_mem)
  obtain ⟨F, ha, hb, hfour⟩ := hform
  have hinv := involutionLocal_preserves_form F ha hb (z : LyonsGroup) z.property
  rw [heq] at hinv
  rcases hfour u v hinv with h | h | h | h
  · left
    apply matrixRepresentation_injective
    rw [heq, h, map_one]
  · exact Or.inr (matrixRepresentation_injective (heq.trans h))
  · have hne := matrixRepresentation_ne_neg (z : LyonsGroup) 1
    rw [map_one] at hne
    exact False.elim (hne (heq.trans h))
  · exact False.elim (matrixRepresentation_ne_neg (z : LyonsGroup) involutionLocalT
      (heq.trans h))

end Lyons.SimplicityCertificate
