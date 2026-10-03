module

public import Stellmacher.SectionEight.GeneratedEightSixObstruction
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# The ambient obstruction from the neighbor quotient in (8.6)(c)

At critical distance greater than one, both neighbor centers lie in the
first-step two-core. Their join is therefore a two-group, and endpoint
noncommutation makes it nontrivial. A PSL₃(2) normalizer quotient for that
join gives a nonsolvable two-local subgroup in the original ambient group
via the injective inclusion of the generated group.

This consumes the final quotient assertion of (8.6)(c), not the admitted
numbered classification. Source: `refs/files/stellmacher-n-group.pdf`,
printed pp. 41 and 44–45.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

public theorem generated_eight_six_bad_local_of_neighbor_quotient
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hlength : 1 < ctx.criticalPath.length)
    (vertex : ctx.Γ.Vertex)
    (hneighbor : vertex ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (hmodel : QuotientIsModel
      (Subgroup.normalizer
        ((ZAt ctx.Γ vertex ⊔ ZAt ctx.Γ ctx.criticalPath.a :
          Subgroup (P1 ⊔ P2 : Subgroup H)) : Set (P1 ⊔ P2 : Subgroup H)))
      (Subgroup.centralizer
        ((ZAt ctx.Γ vertex ⊔ ZAt ctx.Γ ctx.criticalPath.a :
          Subgroup (P1 ⊔ P2 : Subgroup H)) : Set (P1 ⊔ P2 : Subgroup H))) L3Two) :
    ∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  have hcore : ZAt ctx.Γ vertex ⊔ ZAt ctx.Γ ctx.criticalPath.a ≤
      QAt ctx.Γ ctx.criticalPath.firstStep := by
    apply sup_le
    · apply SevenSix.critical_minimality ctx.Γ ctx.criticalPath
      rw [(SevenSix.adjacent_iff_distance_eq_one ctx.Γ).mp
        (ctx.Γ.adjacent_symm
          ((SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor))]
      exact hlength
    · apply SevenSix.critical_minimality ctx.Γ ctx.criticalPath
      rw [(SevenSix.adjacent_iff_distance_eq_one ctx.Γ).mp
        ctx.criticalPath.firstStep_adj]
      exact hlength
  have htwoCore : IsPGroup 2 (QAt ctx.Γ ctx.criticalPath.firstStep) := by
    change IsPGroup 2 (ctx.Γ.twoCoreAt ctx.criticalPath.firstStep)
    rw [ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  have hne : ZAt ctx.Γ vertex ⊔ ZAt ctx.Γ ctx.criticalPath.a ≠ ⊥ := by
    intro hbot
    have hcenter : ZAt ctx.Γ ctx.criticalPath.a = ⊥ :=
      bot_unique (le_sup_right.trans_eq hbot)
    apply ctx.commutator_ne
    change ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥
    simp [hcenter]
  exact ambient_bad_local_of_psl3_two_normalizer_quotient
    (P1 ⊔ P2).subtype (P1 ⊔ P2).subtype_injective _ hne
    (htwoCore.to_le hcore) hmodel

end Stellmacher.SectionEight
