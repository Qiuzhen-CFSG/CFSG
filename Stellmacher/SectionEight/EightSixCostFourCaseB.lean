module
public import Stellmacher.SectionEight.EightSixCostFourNextQuotient
public import Stellmacher.SectionEight.EightSixCostFourSylowOrders
public import Stellmacher.SectionEight.EightSixCostFourInitialQuotientBound
public import Stellmacher.SectionEight.EightSixCostFourInitialResidualSpecial
public import Stellmacher.SectionEight.EightSixCostFourModuleQuaternion
public import Stellmacher.SectionEight.EightSixNextCoreFrattini
public import Stellmacher.SectionEight.EightSixDefs
public import Stellmacher.SectionEight.EightSixCostFourNormalizerWitness
/-!
# Complete cost-four case B of (8.6)

The original selected cost-four configuration gives every clause of
`LemmaEightSixAlternative.b` for the prescribed D, L, Q and three-Sylow T.
The assembly combines the actual Sylow order interval and next wreath
quotient; the initial residual core's special order-64 structure, quotient
bound and fixed-free T action; the quaternion module and next Frattini line;
and the canonical elementary order-16 subgroup normal in L with nonsolvable
ambient normalizer.

Each local producer receives the same original geometric data through the
context's local projection. The pair-to-residual-core identity identifies
the literal initial core for the b1 cardinality and fixed-free clauses;
no conclusion field or replacement action is assumed. This assembles
Stellmacher (8.6)(b), printed pp.41 and44.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_cost_four_case_b
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
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
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4)
    (T : Subgroup G) (hT : IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a)) :
    LemmaEightSixAlternative ctx previous D L Q T := by
  have hnormalizer := eight_six_cost_four_normalizer_witness ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hsylow := eight_six_cost_four_sylow_card_bounds ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hnext := eight_six_cost_four_next_quotient ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hbound := eight_six_cost_four_initial_quotient_bound ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hspecial := eight_six_cost_four_initial_residual_special ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hpairEq := eight_six_cost_four_initial_pair_eq_residual_core ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hquat := eight_six_cost_four_module_quaternion ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hbase := eight_six_common_structure_local ctx.toLocalContext hcenter hquot hlength hcard
    previous hprev D L Q hD hL hQ
  have hPhi := eight_six_next_core_frattini ctx.toLocalContext hcenter hlength hcard
    previous D L Q hprev.1 hD hL data hbase.2.2.2
  apply LemmaEightSixAlternative.b hsylow hquot hnext _ ⟨hquat.1,hPhi⟩ hnormalizer
  refine ⟨hbound,hspecial.2,?_⟩
  change (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) =
        twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) at hpairEq
  rw [←hpairEq]
  exact ⟨(eight_six_cost_four_initial_pair_card ctx.toLocalContext hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost).2.2.2.2,
    eight_six_cost_four_initial_pair_fixed_free ctx.toLocalContext hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost T hT⟩
end Stellmacher.SectionEight
