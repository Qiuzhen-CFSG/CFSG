module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionCentralizerSetup
public import Theory.GroupTheory.MaximalCentralizerTransport

/-!
# Transfer of the ATLAS involution subgroup certificates

Write `H` for the subgroup given by `LyG1-max4W1`, `t = (ab)⁷`, and `w` for
the candidate transporter. If `H` is maximal, centralizes `t`, and `w⁻¹tw = a`,
then its conjugate is the proper centralizer of `a`. The center bound
`Z(H) ⊆ {1,t}` therefore gives the center bound needed for simplicity.

The theorems here discharge this transfer, keeping the finite word identities,
local maximality and local center bound as explicit certificate hypotheses.
None is inferred from the ATLAS subgroup label or the ambient group order.

Source: ATLAS of Finite Group Representations, Lyons entry and `LyG1-max4W1`,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Ly/ . Original subgroup words and
attribution are preserved in `Atlas111InvolutionSource/`.
-/

namespace Lyons.SimplicityCertificate

/-- Conjugation in the direction prescribed by the transporter certificate. -/
@[expose] public def involutionConjugation : LyonsGroup ≃* LyonsGroup :=
  MulAut.conj involutionTransporter⁻¹

/-- Maximality and the two word identities identify the actual centralizer. -/
public theorem involutionLocalSubgroup_map_eq_generatorCentralizer
    (hmax : IsCoatom involutionLocalSubgroup)
    (hcomm : involutionLocalB * involutionLocalT = involutionLocalT * involutionLocalB)
    (htransport : involutionTransporter⁻¹ * involutionLocalT * involutionTransporter =
      generatorA) :
    involutionLocalSubgroup.map involutionConjugation.toMonoidHom = generatorCentralizer := by
  apply Subgroup.map_eq_centralizer_of_isCoatom involutionConjugation
    involutionLocalSubgroup hmax (involutionLocalSubgroup_le_centralizer hcomm)
    (t := involutionLocalT) (a := generatorA) ?_ generatorCentralizer_ne_top
  simpa only [involutionConjugation, MulAut.conj_apply, inv_inv] using htransport

/-- Transfer local maximality to the centralizer of the first generator. -/
public theorem generatorCentralizer_isCoatom_of_local_certificates
    (hmax : IsCoatom involutionLocalSubgroup)
    (hcomm : involutionLocalB * involutionLocalT = involutionLocalT * involutionLocalB)
    (htransport : involutionTransporter⁻¹ * involutionLocalT * involutionTransporter =
      generatorA) : IsCoatom generatorCentralizer := by
  rw [← involutionLocalSubgroup_map_eq_generatorCentralizer hmax hcomm htransport]
  exact (OrderIso.isCoatom_iff involutionConjugation.mapSubgroup involutionLocalSubgroup).mpr hmax

/-- Transfer the local center bound to the exact subgroup used by the simplicity proof. -/
public theorem generatorCentralizer_center_of_local_certificates
    (hmax : IsCoatom involutionLocalSubgroup)
    (hcomm : involutionLocalB * involutionLocalT = involutionLocalT * involutionLocalB)
    (htransport : involutionTransporter⁻¹ * involutionLocalT * involutionTransporter =
      generatorA)
    (hcenter : ∀ z : involutionLocalSubgroup,
      z ∈ Subgroup.center involutionLocalSubgroup →
      (z : LyonsGroup) = 1 ∨ (z : LyonsGroup) = involutionLocalT) :
    ∀ z : generatorCentralizer, z ∈ Subgroup.center generatorCentralizer →
      (z : LyonsGroup) = 1 ∨ (z : LyonsGroup) = generatorA := by
  have h := Subgroup.center_bound_of_map_eq involutionConjugation
    involutionLocalSubgroup generatorCentralizer involutionLocalT
    (involutionLocalSubgroup_map_eq_generatorCentralizer hmax hcomm htransport) hcenter
  simpa only [involutionConjugation, MulAut.conj_apply, inv_inv, htransport] using h

end Lyons.SimplicityCertificate
