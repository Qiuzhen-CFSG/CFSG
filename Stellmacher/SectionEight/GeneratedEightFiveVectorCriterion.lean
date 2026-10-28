module

public import Stellmacher.SectionEight.GeneratedEightFiveVectorAmbient
public import Stellmacher.QuotientModuleWitnessInjectiveTransport

/-!
# The generated fixed-vector centralizer criterion

Transport the exact faithful initial-center witness along the join inclusion.
Its offender fixed subgroup maps to the ambient witness's fixed subgroup.
The ambient-backed (6.4) criterion then returns the vector to the next graph
center. Hypothesis Two stays on the original ambient group, and the original
graph and full-edge generation equation are unchanged.

This is the conditional vector criterion used in Stellmacher (8.4) and (8.5),
printed pp.39–40 of `refs/files/stellmacher-n-group.pdf`. It requires neither
fixed-subgroup normality nor (8.3).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem generated_eight_four_vector_centralizer_criterion
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set (P1 ⊔ P2 : Subgroup H)))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (v : (P1 ⊔ P2 : Subgroup H))
    (hv : v ∈ w.oneJFixedPoints (S.subgroupOf (P1 ⊔ P2)))
    (hgen : (GAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer ({v} : Set (P1 ⊔ P2 : Subgroup H))) ⊔
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
        GAt ctx.Γ ctx.criticalPath.firstStep) :
    v ∈ ZAt ctx.Γ ctx.criticalPath.firstStep := by
  obtain ⟨ambientWitness, hfixed⟩ := quotientModuleWitness_exists_map_fixed
    (P1 ⊔ P2).subtype (P1 ⊔ P2).subtype_injective
    (GAt ctx.Γ ctx.criticalPath.a) (ZAt ctx.Γ ctx.criticalPath.a)
    (S.subgroupOf (P1 ⊔ P2)) w
  rw [Subgroup.map_subgroupOf_eq_of_le
    (ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1.1.trans le_sup_left)] at hfixed
  exact generated_eight_four_vector_criterion_of_ambient_witness ctx hcenter w
    ambientWitness hfixed v hv hgen

end Stellmacher.SectionEight
