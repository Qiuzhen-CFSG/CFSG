module
public import Stellmacher.SectionEight.EightSixCostFourFaithfulWreath
public import Stellmacher.SectionEight.EightSixNextFilteredActionKernel

/-!
# The ordinary next quotient in the cost-four branch

The actual next stabilizer modulo its two-core is the regular wreath product
SL₂(2) wreath C₂. This is the unchanged ordinary quotient assertion in case B
of Stellmacher (8.6). The selected local hypotheses and cost-four condition
are retained; no quotient-action, kernel or full-image model is assumed.

The next quotient-module factory supplies the literal conjugation action on
Vnext/Znext. The selected actor outside the next core gives source (8), and
the actual filtration-kernel theorem identifies the action kernel exactly.
The faithful-image wreath theorem then applies. Composing its equivalence
with the action's range restriction gives a surjection with the prescribed
native two-core kernel, exactly the public QuotientIsModel predicate.

Source: Stellmacher, Journal of Algebra190 (1997), proof of (8.6), printed
p.44, the cost-four classification following bounded (1.6).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_cost_four_next_quotient
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4) :
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2TwoWreathC2 := by
  obtain ⟨hN,hW,action,hformula,hkernel,hgenerate⟩ :=
    eight_six_next_quotient_module_data_local ctx hcenter hlength hcard data.first_commutator
  have hres := eight_six_next_residual_core_commutator_le_v ctx hcenter hlength previous D L Q
    hprev.1 hD hL data (fun h => hout (h ha))
  have hker := eight_six_next_quotient_action_kernel ctx hcenter data.first_commutator hres
    hN action hformula hkernel
  obtain ⟨e⟩ := eight_six_cost_four_faithful_wreath ctx hcenter hquot hlength hcard previous
    D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
    hN hW action hformula hkernel hgenerate
  let f := e.toMonoidHom.comp action.rangeRestrict
  refine ⟨f,e.surjective.comp action.rangeRestrict_surjective,?_⟩
  have hkerf : f.ker = action.ker := by
    ext a
    change e (action.rangeRestrict a) = 1 ↔ action a = 1
    rw [← e.map_one,e.injective.eq_iff]
    exact Subtype.ext_iff
  rw [hkerf,hker]
  change pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep) =
    (ctx.Γ.twoCoreAt ctx.criticalPath.firstStep).subgroupOf _
  rw [ctx.Γ.twoCoreAt_def]
  exact (Subgroup.comap_map_eq_self_of_injective
    (GAt ctx.Γ ctx.criticalPath.firstStep).subtype_injective _).symm
end Stellmacher.SectionEight
