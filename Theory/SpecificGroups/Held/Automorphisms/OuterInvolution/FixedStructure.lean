module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Noninner
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.CentralKernel
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.FixedOrderBound
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.OrbitCover
public import Theory.GroupTheory.GeneralizedFitting.IndexTwoCover
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Assembly for the Held outer fixed subgroup's triple cover

The constructed subgroup is already proved perfect and proper in the literal
fixed subgroup. An actual A7 orbit image with central kernel of order three
then identifies its central quotient and gives order 7560. A bound of 15120
on the full fixed subgroup forces index two, hence relative normality.

The checked graph bound and orbit-action certificates discharge all inputs
in `Held.OuterInvolution.fixed_cover`. The generated candidate is the
commutator subgroup, and its central quotient is explicitly identified with A7.
Source: GLS3 Table 5.3p, outer 2C row, with pp.260–261's covering convention.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace Held.OuterInvolution.FixedStructure

private theorem a7_card : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem a7_center_eq_bot : center (alternatingGroup (Fin 7)) = ⊥ :=
  alternatingGroup.center_eq_bot (by simp)

/-- The actual orbit action followed by its image comparison with A7. -/
noncomputable def projection (e : orbitImage ≃* alternatingGroup (Fin 7)) :
    candidate →* alternatingGroup (Fin 7) := e.toMonoidHom.comp orbitAction.rangeRestrict

theorem projection_surjective (e : orbitImage ≃* alternatingGroup (Fin 7)) :
    Function.Surjective (projection e) :=
  e.surjective.comp orbitAction.rangeRestrict_surjective

theorem projection_ker (e : orbitImage ≃* alternatingGroup (Fin 7)) :
    (projection e).ker = orbitKernel := by
  ext x
  change e (orbitAction.rangeRestrict x) = 1 ↔ orbitAction x = 1
  rw [← e.map_one, e.injective.eq_iff]
  exact Subtype.ext_iff

/-- A central kernel is the full center because the actual quotient image is centerless. -/
theorem orbitKernel_eq_center (e : orbitImage ≃* alternatingGroup (Fin 7))
    (hcentral : orbitKernel ≤ center candidate) : orbitKernel = center candidate := by
  apply le_antisymm hcentral
  intro x hx
  rw [← projection_ker e]
  change projection e x = 1
  have hz : projection e x ∈ center (alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := projection_surjective e y
    simpa only [← map_mul] using congrArg (projection e) (Subgroup.mem_center_iff.mp hx z)
  simpa only [a7_center_eq_bot, Subgroup.mem_bot] using hz

/-- An isomorphism from the central quotient of the literal candidate to A7. -/
noncomputable def quotientCenterEquiv (e : orbitImage ≃* alternatingGroup (Fin 7))
    (hcentral : orbitKernel ≤ center candidate) :
    (candidate ⧸ center candidate) ≃* alternatingGroup (Fin 7) :=
  (QuotientGroup.quotientMulEquivOfEq (orbitKernel_eq_center e hcentral).symm).trans
    ((QuotientGroup.quotientKerEquivRange orbitAction).trans e)

theorem candidate_card (e : orbitImage ≃* alternatingGroup (Fin 7))
    (hk : Nat.card orbitKernel = 3) : Nat.card candidate = 7560 := by
  have hc := orbitKernel.card_mul_index
  rw [Subgroup.index_ker, Nat.card_congr e.toEquiv, a7_card, hk] at hc
  exact hc.symm

theorem candidate_index (hbound : Nat.card fixed ≤ 15120)
    (e : orbitImage ≃* alternatingGroup (Fin 7))
    (hk : Nat.card orbitKernel = 3) : candidate.index = 2 := by
  have hc := candidate.card_mul_index
  rw [candidate_card e hk] at hc
  have hi := candidate.one_lt_index_of_ne_top candidate_ne_top
  omega

/-- The convenient generated subgroup equals the canonical commutator once its index is known. -/
theorem candidate_eq_commutator_of_index_two (hi : candidate.index = 2) :
    candidate = commutator fixed := by
  let : candidate.Normal := Subgroup.normal_of_index_eq_two hi
  let : IsCyclic (fixed ⧸ candidate) := isCyclic_of_prime_card hi
  apply le_antisymm
  · rw [← candidate.commutator_eq_self]
    exact Subgroup.commutator_mono le_top le_top
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

/-- Assembly from a full fixed-subgroup bound and a concrete orbit-cover certificate. -/
theorem _root_.Held.OuterInvolution.fixed_cover_of_orbit
    (hbound : Nat.card fixed ≤ 15120)
    (e : orbitImage ≃* alternatingGroup (Fin 7))
    (hk : Nat.card orbitKernel = 3)
    (hcentral : orbitKernel ≤ center candidate) :
    HasQuasisimpleNormalOfIndexTwo action.fixedSubgroup 3 := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hq : IsQuasisimple candidate :=
    { simple := (quotientCenterEquiv e hcentral).isSimpleGroup }
  have hi := candidate_index hbound e hk
  have hz : Nat.card (center candidate) = 3 := by
    rw [← orbitKernel_eq_center e hcentral]
    exact hk
  exact ⟨candidate, Subgroup.normal_of_index_eq_two hi, hq, hi, hz⟩

/-- Assembly from the upper containment in the concrete orbit-kernel calculation. -/
theorem _root_.Held.OuterInvolution.fixed_cover_of_kernel_bound
    (hbound : Nat.card fixed ≤ 15120)
    (e : orbitImage ≃* alternatingGroup (Fin 7))
    (hkernel : orbitKernel ≤ zpowers centralGenerator) :
    HasQuasisimpleNormalOfIndexTwo action.fixedSubgroup 3 := by
  apply Held.OuterInvolution.fixed_cover_of_orbit hbound e
  · rw [orbitKernel_eq_centralZpowers hkernel]
    exact centralZpowers_card
  · exact hkernel.trans centralZpowers_le_center

private theorem orbitKernel_card_exact : Nat.card orbitKernel = 3 := by
  rw [orbitKernel_eq_centralZpowers_exact]
  exact centralZpowers_card

/-- The central quotient of the actual perfect subgroup is A7, through its orbit action. -/
noncomputable def candidateQuotientCenterEquiv :
    (candidate ⧸ center candidate) ≃* alternatingGroup (Fin 7) :=
  quotientCenterEquiv orbitImage_equiv_alternatingGroup
    (orbitKernel_le_centralZpowers.trans centralZpowers_le_center)

/-- The perfect triple cover has index two in the literal fixed subgroup. -/
theorem candidate_index_exact : candidate.index = 2 :=
  candidate_index fixed_card_le orbitImage_equiv_alternatingGroup orbitKernel_card_exact

/-- The constructed triple cover is the canonical commutator subgroup. -/
theorem candidate_eq_commutator : candidate = commutator fixed :=
  candidate_eq_commutator_of_index_two candidate_index_exact

/-- The fixed subgroup of the explicit Held outer involution contains its normal
quasisimple triple-A7 subgroup with index two, as in GLS3 Table 5.3p. -/
theorem _root_.Held.OuterInvolution.fixed_cover :
    HasQuasisimpleNormalOfIndexTwo action.fixedSubgroup 3 :=
  Held.OuterInvolution.fixed_cover_of_kernel_bound fixed_card_le
    orbitImage_equiv_alternatingGroup orbitKernel_le_centralZpowers

end Held.OuterInvolution.FixedStructure
