module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowData
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Reducing star-group involution coverage to the fixed Sylow candidate

The certified ambient order has exact two-part 1024. A certificate of that
order for the fixed word subgroup therefore promotes it to a Sylow subgroup.
Sylow conjugacy transfers a local involution-conjugacy certificate to the
whole star group. The subgroup order and local fusion remain independent
premises until their concrete certificates are supplied.

This is the Sylow theorem applied to the star action of the ATLAS
`J4G1-max1W1` generators; see `SylowData` for the explicit candidate.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.QuotientInvolutions
open Cardinality.QuotientCount.Image

/-- The fixed candidate is Sylow as soon as its proposed order is certified. -/
noncomputable def candidateSylow (hcard : Nat.card sylowCandidate = 1024) :
    Sylow 2 StarGroup := by
  have hp : IsPGroup 2 sylowCandidate := IsPGroup.of_card (n := 10) hcard
  have hind : ¬ 2 ∣ sylowCandidate.index := by
    have hi := sylowCandidate.card_mul_index
    rw [hcard, starGroup_order] at hi
    have he : sylowCandidate.index = 239085 := by omega
    rw [he]
    decide
  exact hp.toSylow hind

/-- Local fusion into the two marked words, with conjugators inside the star
group, suffices. This does not infer fusion from symmetric-group cycle shapes. -/
theorem star_coverage_of_sylow_certificates
    (hcard : Nat.card sylowCandidate = 1024)
    (hlocal : ∀ w : StarGroup, w ∈ sylowCandidate → orderOf w = 2 →
      ∃ g : StarGroup,
        starFirst = g * w * g⁻¹ ∨ (starFirst * starSecond)^7 = g * w * g⁻¹) :
    ∀ w : StarGroup, orderOf w = 2 → ∃ g : StarGroup,
      starFirst = g * w * g⁻¹ ∨ (starFirst * starSecond)^7 = g * w * g⁻¹ := by
  intro w hw
  let P := candidateSylow hcard
  obtain ⟨u, hu⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hw)
  obtain ⟨c, hc⟩ := isConj_iff.mp hu
  change (MulAut.conj c) w = (u : StarGroup) at hc
  have huOrder : orderOf (u : StarGroup) = 2 := by
    rw [← hc, MulEquiv.orderOf_eq, hw]
  obtain ⟨g, hg⟩ := hlocal u u.property huOrder
  refine ⟨g * c, ?_⟩
  simpa only [← hc, MulAut.conj_apply, mul_inv_rev, mul_assoc] using hg

end Janko4.Simplicity.Max1Fusion.QuotientInvolutions
