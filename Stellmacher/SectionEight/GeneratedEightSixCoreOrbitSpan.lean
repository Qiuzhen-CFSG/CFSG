module

public import Stellmacher.SectionEight.GeneratedEightSixCoreGenerationTools
public import Stellmacher.SectionEight.GeneratedEightSixNeighborGeneration

/-!
# The core-orbit span in Stellmacher (8.6)(1)

The conjugate closure of the first neighbor-module core part lies in the join
of the two selected neighbor-module core parts and D. The proof takes the
actual local graph context, and the generated adapter retains its original
public interface and graph. This local interface also serves the canonical
same-ambient (8.6) theorem without changing its group or graph.

The initial core normalizes each module part and D. Both selected neighbor
modules normalize their joined span by the core commutator bound. Their
proved cubic generation of the initial stabilizer makes that span invariant,
so it contains the entire required conjugate closure.

Source: Stellmacher, printed p.41, equation (1) in the proof of (8.6).
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_core_orbit_span_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup H)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (action : EightSixEquationOneActionData ctx.Γ ctx.criticalPath D L Q) :
    conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a) ≤
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔ D := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let initial := GAt graph path.a
  let core := QAt graph path.a
  let previousInter := VAt graph previous ⊓ core
  let firstInter := VAt graph path.firstStep ⊓ core
  let span := previousInter ⊔ firstInter ⊔ D
  have hlong : 1 < path.length := by dsimp [path]; omega
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  have hpreviousAction := eight_six_generation_neighbor_action ctx.sectionSeven
    graph path hlong previous hprev.1
  have hfirstAction := eight_six_generation_neighbor_action ctx.sectionSeven
    graph path hlong path.firstStep hfirst
  have hDnormal : initial ≤ Subgroup.normalizer (D : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer action.intersection_normal.1).mp
      action.intersection_normal.2
  have hcoreInitial : core ≤ initial := by
    change QAt graph path.a ≤ GAt graph path.a
    rw [QAt, q, graph.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le _
  have hcoreNormal : core ≤ Subgroup.normalizer (span : Set H) := by
    apply le_trans (le_inf ?_ (hcoreInitial.trans hDnormal))
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact (le_inf hpreviousAction.1 hfirstAction.1).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hspanCore : span ≤ core :=
    (eight_six_generation_lower_bound ctx.sectionSeven graph path hlong previous hprev.1
      D L Q hD hL hQ action).trans
      (eight_six_action_core_containments ctx.sectionSeven graph path previous hprev.1
        D L Q hD hL hQ action).2.1
  have hpreviousNormal : VAt graph previous ≤
      Subgroup.normalizer (span : Set H) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact (Subgroup.commutator_mono hspanCore le_rfl).trans
      (hpreviousAction.2.trans (le_sup_left.trans le_sup_left))
  have hfirstNormal : VAt graph path.firstStep ≤
      Subgroup.normalizer (span : Set H) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact (Subgroup.commutator_mono hspanCore le_rfl).trans
      (hfirstAction.2.trans (le_sup_right.trans le_sup_left))
  apply eight_six_conjugate_closure_le _ _ _ (le_sup_right.trans le_sup_left)
  change initial ≤ Subgroup.normalizer (span : Set H)
  have hgen : core ⊔ VAt graph path.firstStep ⊔ VAt graph previous = initial :=
    eight_six_neighbor_generation_local ctx hquot hlength previous hprev
  rw [← hgen]
  exact sup_le (sup_le hcoreNormal hfirstNormal) hpreviousNormal

public theorem generated_eight_six_core_orbit_span
    {H : Type u} [Group H] [Finite H] {S0 : Sylow 2 H}
    {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (_hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (_hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (action : EightSixEquationOneActionData ctx.Γ ctx.criticalPath D L Q) :
    conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a) ≤
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔ D := by
  exact eight_six_core_orbit_span_local ctx.toLocalContext hquot hlength
    previous hprev D L Q hD hL hQ action

end Stellmacher.SectionEight
