module
public import Stellmacher.SectionFiveToSeven.SixFourFixingFactor
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts

/-!
# Transporting a native fixed-space bound to the barred action

Suppose the canonical barred critical subgroup is nontrivial and the part
of the actual Section Six module centralized by B(S) has order at most
four times Ω₁(Z(S)). Then the fixed subgroup of barred oneJ has order at
most four times the quotient Sylow's fixed subgroup in the named module.

Injectively map the intrinsic module into the ambient group. A barred-J
fixed vector outside Ω₁(Z(S)) is centralized by B(S) by the exact (6.4)
fixing-factor theorem; vectors inside Ω₁(Z(S)) are already centralized by S.
Conversely the entire Sylow omega-center lifts to intrinsic Sylow-fixed
vectors through the canonical quotient action. These two inclusions and
injectivity transfer the numerical bound without identifying fixed groups
formed using different action instances.

This supplies the fixed-index input for the local (1.7) rank argument in
Stellmacher (9.3), Journal of Algebra 190 (1997), p.50,
`refs/files/stellmacher-n-group.pdf`. The statement retains the actual
canonical quotient action and the full barred critical subgroup.
-/

namespace Stellmacher.SectionsFiveToSeven
open SevenSix
universe u

public theorem sixFour_barred_fixed_index_le_four {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hJ : sectionSixBarredCritical h ≠ ⊥)
    (hbound : Nat.card (sectionSixV S P1 ⊓
      Subgroup.centralizer (baumannIn S : Set H) : Subgroup H) ≤
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
  have hFJ : FJ.map f ≤ sectionSixV S P1 ⊓ Subgroup.centralizer (baumannIn S : Set H) := by
    rintro w ⟨v,hv,rfl⟩
    refine ⟨hsetup.localV_image ▸ Subgroup.mem_map_of_mem P1.subtype v.property,?_⟩
    by_cases hz : f v ∈ omegaOneCenter S
    · exact ((omegaOneCenter_le_centerAmbient S).trans (centerAmbient_le_centralizer S)
        |>.trans (Subgroup.centralizer_le (show baumannIn S ≤ S from inf_le_left))) hz
    · have hp := (sixFour_canonical_fixing_factor h hJ v
        ((hsetup.mem_fixedPoints_iff v).mp hv) hz).1
      change f v ∈ Subgroup.centralizer (baumannIn S : Set H)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp (hp hb).2 (f v) (Set.mem_singleton _)).symm
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
  have h1 : Nat.card FJ ≤ Nat.card (sectionSixV S P1 ⊓
      Subgroup.centralizer (baumannIn S : Set H) : Subgroup H) := by
    rw [← Subgroup.card_map_of_injective hf]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hFJ) (Subgroup.inclusion_injective hFJ)
  have h2 : Nat.card (omegaOneCenter S) ≤ Nat.card FS := by
    rw [← Subgroup.card_map_of_injective hf]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hOFS) (Subgroup.inclusion_injective hOFS)
  exact h1.trans (hbound.trans (Nat.mul_le_mul_left 4 h2))

end Stellmacher.SectionsFiveToSeven
