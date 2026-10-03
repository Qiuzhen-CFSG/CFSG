module
public import Stellmacher.SectionEight.GeneratedEightSixHighCostObstruction
public import Stellmacher.SectionEight.GeneratedEightSixLargeIndexSetup
public import Stellmacher.SectionEight.GeneratedEightSixNoncontainmentSetup
public import Stellmacher.SectionEight.EightSixCommonStructure
public import Stellmacher.SectionEight.EightSixSmallIndexCaseA
public import Stellmacher.SectionEight.EightSixSelectedActorCostCases

/-!
# Reducing generated (8.6) to the actual cost-four configuration

For the generated Section Eight graph with central first-step center,
initial SL₂(2) quotient, critical distance two, and initial center of order
four, the prescribed predecessor and subgroup definitions yield either
complete case-A type data, an actual selected cost-four configuration,
or a nonsolvable two-local subgroup of the original ambient group.
The middle alternative retains its exact geometric extraction, actor
membership and core escape, minimality, edge generation, orbit containment,
and large-index inequality; it asserts no later classification model.

Construct the equation-one and elementary common structure. Index two of
the predecessor core part gives case A by the local small-index theorem.
Otherwise the proved noncontainment forces index at least four. The actual
minimal-actor extraction supplies the group and coatom. The selected orbit
lies in the initial core, so the proved cost dichotomy applies. Cost four
returns these same witnesses; high cost produces the ambient nonsolvable
two-local via the (c4) neighbor-normalizer theorem.

Source: Stellmacher (8.6), Journal of Algebra 190 (1997), printed pp.41–45,
the small-index case, selected-actor construction, and assertions (9)/(12).
This is a reduction for the Section Eleven N₂ argument. The remaining
cost-four normalizer obstruction is separate, and no full numbered (8.6)
or generated fixed-center normality result is assumed here.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem generated_eight_six_caseA_or_cost_four_or_bad_local
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (hT : IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a)) :
    EightSixCaseATypeData ctx.Γ ctx.criticalPath previous D L Q T ∨
      (∃ (E A0 : Subgroup (P1 ⊔ P2 : Subgroup H)) (actor : (P1 ⊔ P2 : Subgroup H)),
        Nonempty (SectionNine.NineThreeGeometricData ctx.Γ
          ctx.criticalPath.firstStep ctx.criticalPath.a
          (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor) ∧
        actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a ∧
        actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep ∧
        (∀ other : (P1 ⊔ P2 : Subgroup H),
          other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
          other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
          eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
            eightSixCommutatorCost ctx.Γ ctx.criticalPath other) ∧
        E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
          GAt ctx.Γ ctx.criticalPath.firstStep ∧
        conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
          QAt ctx.Γ ctx.criticalPath.a ∧
        4 * Nat.card
          ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D :
            Subgroup (P1 ⊔ P2 : Subgroup H)) ≤
          Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a :
            Subgroup (P1 ⊔ P2 : Subgroup H)) ∧
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4) ∨
      ∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  classical
  obtain ⟨data,hbase⟩ := eight_six_common_structure_local ctx.toLocalContext
    hcenter hquot hlength hcard previous hprev D L Q hD hL hQ
  by_cases hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2
  · exact Or.inl (eight_six_small_index_caseA_local ctx.toLocalContext hcenter
      hquot hlength hcard previous D L Q T hprev ⟨hD,hL,hQ,hT⟩ hbase hindex data)
  have hnot := generated_eight_six_predecessor_intersection_not_le_of_equation_one
    ctx hcenter hlength previous D L Q hprev.1 data hQ hbase.1
  have hlarge := (generated_eight_six_index_ge_four_of_not_le ctx previous D hnot hindex).2
  obtain ⟨actor,E,A0,ha,hout,hmin,hedge,_,⟨geom⟩⟩ :=
    generated_eight_six_minimal_actor_configuration ctx hlength previous D L Q
      hD hQ data hlarge (eightSixCommutatorCost ctx.Γ ctx.criticalPath)
  have hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a :=
    eight_six_selected_orbit_closure_le_initial_core ctx.toLocalContext hcenter
      hquot hlength hcard previous D hprev hD data.intersection_normal E A0
      geom.group_le (geom.coatom_eq ▸ inf_le_left) geom.coatom_card
      geom.coatom_commutator hlarge
  rcases eight_six_selected_actor_cost_cases ctx.toLocalContext hcenter hquot hlength
      hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin
    with hfour | hhigh
  · exact Or.inr (Or.inl ⟨E,A0,actor,⟨geom⟩,ha,hout,hmin,hedge,hcore,hlarge,hfour⟩)
  · exact Or.inr (Or.inr (generated_eight_six_high_cost_bad_local ctx hcenter hquot
      hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hQ))

end Stellmacher.SectionEight
