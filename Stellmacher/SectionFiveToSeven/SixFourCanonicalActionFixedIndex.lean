module
public import Stellmacher.SectionFiveToSeven.SixFourFixingFactor
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts

/-!
# Cardinal transport for the exact canonical fixed subgroup

A bound on the intersection of the Section Six module with the centralizer
of the full canonical barred critical preimage yields the corresponding
bound between the intrinsic critical fixed space and Sylow fixed space.
The intrinsic fixed subgroup maps exactly onto the stated ambient
intersection by the canonical fixed-vector equivalence. The entire Sylow
omega-center injects into the intrinsic Sylow-fixed subgroup. Cardinality
transport along these actual maps proves the numerical bound.

This is the action-presentation transfer used for the index-four (1.7)
argument in Stellmacher (9.3), Journal of Algebra 190 (1997), p.50,
`refs/files/stellmacher-n-group.pdf`. No nontriviality or native Baumann
identification is assumed by the transfer itself.
-/

namespace Stellmacher.SectionsFiveToSeven
open SevenSix
universe u

public theorem sixFour_canonical_action_fixed_index_le_four {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hbound : Nat.card (sectionSixV S P1 ⊓
      Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H) : Subgroup H) ≤
        4 * Nat.card (omegaOneCenter S)) :
    letI := sectionSixQuotientAction h
    Nat.card (FixedPoints.subgroup (sectionSixBarredCritical h) (sectionSixLocalV h)) ≤
      4 * Nat.card (FixedPoints.subgroup
        (sectionSixBarSylow h : Subgroup (SectionSixBarP1 h)) (sectionSixLocalV h)) := by
  classical
  let _ := sectionSixQuotientAction h
  let V := sectionSixLocalV h
  let f : V →* H := P1.subtype.comp V.subtype
  have hf : Function.Injective f := P1.subtype_injective.comp V.subtype_injective
  have hsetup := sectionSix_barred_action_setup h
  let FJ := FixedPoints.subgroup (sectionSixBarredCritical h) V
  let FS := FixedPoints.subgroup (sectionSixBarSylow h : Subgroup (SectionSixBarP1 h)) V
  have hFJ : FJ.map f = sectionSixV S P1 ⊓
      Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H) := by
    apply le_antisymm
    · rintro w ⟨v,hv,rfl⟩
      exact ⟨hsetup.localV_image ▸ Subgroup.mem_map_of_mem P1.subtype v.property,
        (hsetup.mem_fixedPoints_iff v).mp hv⟩
    · intro w hw
      obtain ⟨v,hv,hve⟩ := Subgroup.mem_map.mp (hsetup.localV_image.symm ▸ hw.1)
      let vector : V := ⟨v,hv⟩
      refine Subgroup.mem_map.mpr ⟨vector,?_,hve⟩
      apply (hsetup.mem_fixedPoints_iff vector).mpr
      change P1.subtype v ∈ _
      rw [hve]
      exact hw.2
  have hOFS : omegaOneCenter S ≤ FS.map f := by
    intro w hw
    have hwV : w ∈ sectionSixV S P1 := by
      apply Subgroup.subset_closure
      exact ⟨1,⟨w,hw⟩,by simp⟩
    obtain ⟨v,hv,hve⟩ := Subgroup.mem_map.mp (hsetup.localV_image.symm ▸ hwV)
    let vector : V := ⟨v,hv⟩
    refine Subgroup.mem_map.mpr ⟨vector,?_,hve⟩
    rw [FixedPoints.mem_subgroup]
    intro actor
    obtain ⟨a,ha,he⟩ := actor.property
    apply Subtype.ext
    change ((actor.val • vector : V) : P1) = v
    rw [← he,SectionTwo.quotientConjugationAction_smul_coe (sectionSixSylow h)
      (sectionSixQuotientMap h) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)]
    apply P1.subtype_injective
    change (a : H) * (v : H) * (a : H)⁻¹ = (v : H)
    change (v : H) = w at hve
    rw [hve]
    apply mul_inv_eq_iff_eq_mul.mpr
    have haS : (a : H) ∈ S := hsetup.sylow_image ▸ Subgroup.mem_map_of_mem P1.subtype ha
    exact Subgroup.mem_centralizer_iff.mp
      (((omegaOneCenter_le_centerAmbient S).trans (centerAmbient_le_centralizer S)) hw) a haS
  have h1 : Nat.card FJ = Nat.card (sectionSixV S P1 ⊓
      Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H) : Subgroup H) := by
    rw [← hFJ,Subgroup.card_map_of_injective hf]
  have h2 : Nat.card (omegaOneCenter S) ≤ Nat.card FS := by
    rw [← Subgroup.card_map_of_injective hf]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hOFS) (Subgroup.inclusion_injective hOFS)
  exact h1.le.trans (hbound.trans (Nat.mul_le_mul_left 4 h2))

end Stellmacher.SectionsFiveToSeven
