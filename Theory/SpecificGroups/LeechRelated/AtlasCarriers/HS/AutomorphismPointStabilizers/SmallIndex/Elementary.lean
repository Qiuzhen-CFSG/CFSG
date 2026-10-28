module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.CertificateData
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Certificate
public import Mathlib.GroupTheory.PGroup

/-!
# The order-eleven subgroup and its normalizing elements

The specified word has order eleven, and conjugation by the normalizer word
raises it to its ninth power. Both finite permutation identities are checked
by kernel reduction on all 100 letters. They prove that the candidate N
normalizes P. The already checked stabilizer chain gives |H1| = 443520.

These facts concern the explicit auxiliary stabilizer H1. They assert neither
its equality with the actual HS point stabilizer nor the remaining overgroup
classification. Source context: GLS3 Table 5.3m, printed p.274; the original
ATLAS HSG1-p100B0 permutations are retained with attribution in the carrier.
-/

public section
namespace Sporadic.LeechRelated.HS.SmallIndex
open Subgroup
set_option maxRecDepth 100000

private theorem elevenElement_pow : elevenElement ^ 11 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply OrderCertificate.allFin
  decide +kernel

/-- The specified word has order exactly eleven in the auxiliary stabilizer. -/
theorem elevenElement_order : orderOf elevenElement = 11 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply orderOf_eq_prime elevenElement_pow
  intro h
  have hx := congrArg (fun g : CertifiedStabilizer => (g : Equiv.Perm (Fin 100)) 1) h
  have hne : (elevenElement : Equiv.Perm (Fin 100)) 1 ≠ 1 := by decide +kernel
  exact hne hx

/-- The specified cyclic subgroup has order eleven. -/
theorem primeSubgroup_card : Nat.card primeSubgroup = 11 := by
  rw [primeSubgroup, Nat.card_zpowers, elevenElement_order]

/-- The cyclic subgroup used for the coset action is an eleven-group. -/
theorem primeSubgroup_isPGroup : IsPGroup 11 primeSubgroup := by
  apply IsPGroup.of_card (n := 1)
  simpa using primeSubgroup_card

/-- The explicit normalizing word acts by the ninth power on the eleven-cycle. -/
theorem normalizerElement_conj :
    normalizerElement * elevenElement * normalizerElement⁻¹ = elevenElement ^ 9 := by
  apply Subtype.ext
  apply Equiv.ext
  apply OrderCertificate.allFin
  decide +kernel

/-- Both generators of the normalizer candidate normalize the cyclic subgroup. -/
theorem normalizerCandidate_le_normalizer :
    normalizerCandidate ≤ normalizer (primeSubgroup : Set CertifiedStabilizer) := by
  refine sup_le primeSubgroup.le_normalizer (zpowers_le.mpr ?_)
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [primeSubgroup, MonoidHom.map_zpowers]
    apply zpowers_le.mpr
    change normalizerElement * elevenElement * normalizerElement⁻¹ ∈ zpowers elevenElement
    rw [normalizerElement_conj]
    exact pow_mem (mem_zpowers elevenElement) _
  · exact le_of_eq (card_map_of_injective (K := primeSubgroup)
      (f := (MulAut.conj normalizerElement : CertifiedStabilizer →* CertifiedStabilizer))
      (MulAut.conj normalizerElement).injective).symm

/-- The existing stabilizer chain gives the auxiliary stabilizer's order. -/
theorem certifiedStabilizer_card : Nat.card CertifiedStabilizer = 443520 := by
  have h := OrderCertificate.H0_card
  rw [OrderCertificate.card0] at h
  change 100 * Nat.card CertifiedStabilizer = 44352000 at h
  omega

end Sporadic.LeechRelated.HS.SmallIndex
