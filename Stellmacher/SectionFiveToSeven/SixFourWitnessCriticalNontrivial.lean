module
public import Stellmacher.SectionFiveToSeven.SixFourWitnessFixedComparison

/-!
# A proper witness fixed subgroup forces nontrivial barred critical action

Let V be the actual Section Six module under Hypothesis Two and let w
be a faithful quotient-module witness on V. If w.oneJFixedPoints S is
properly smaller than V, the canonical barred critical subgroup is nontrivial.

The witness comparison identifies its fixed subgroup with the ambient
centralizer of the full canonical preimage, intersected with V. If the
canonical critical subgroup were trivial, every native vector would be
fixed. The native-to-ambient image and canonical action setup would then
put every V vector in that centralizer, contradicting properness.

This is the nontrivial-action prerequisite for the application of (6.4)
in Stellmacher (8.4), Journal of Algebra 190 (1997), pp.31–32 and38.
Source: refs/files/stellmacher-n-group.pdf and the canonical barred
fixed-point notation; no raw ambient offender equality is used.
-/

namespace Stellmacher.SectionsFiveToSeven
open Stellmacher.Later
universe u

public theorem sectionSix_barredCritical_ne_bot_of_witness_fixed_ne
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (V : Subgroup H) (hV : V = sectionSixV S P1)
    (w : QuotientModuleWitness P1 (P1 ⊓ Subgroup.centralizer (V : Set H)) V)
    (hfixed : w.oneJFixedPoints S ≠ V) : sectionSixBarredCritical h ≠ ⊥ := by
  intro hbot
  apply hfixed
  rw [sectionSix_witness_fixed_eq h V hV w]
  apply inf_eq_left.mpr
  intro v hv
  have hv' : v ∈ sectionSixV S P1 := hV ▸ hv
  obtain ⟨vn,hvn,rfl⟩ := Subgroup.mem_map.mp
    ((sectionSix_barred_action_setup h).localV_image.ge hv')
  apply ((sectionSix_barred_action_setup h).mem_fixedPoints_iff ⟨vn,hvn⟩).mp
  let _ := sectionSixQuotientAction h
  change (⟨vn,hvn⟩ : sectionSixLocalV h) ∈
    FixedPoints.subgroup (sectionSixBarredCritical h) (sectionSixLocalV h)
  rw [hbot]
  simp [FixedPoints.mem_subgroup]
end Stellmacher.SectionsFiveToSeven
