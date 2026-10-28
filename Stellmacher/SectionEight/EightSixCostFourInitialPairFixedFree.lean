module
public import Stellmacher.SectionEight.EightSixCostFourCoreQuotientCard
public import Stellmacher.SectionEight.EightSixFixedCoreSplitting
/-!
# The cost-four initial pair has no cubic fixed points

The join of the two neighboring module/core intersections has no nonidentity
fixed element under the actual initial Sylow three-subgroup. The full selected
cost-four configuration is retained, and the initial pair is not assumed to
be the residual two-core.

The pair lies in Q and meets D in precisely the initial center. The general
fixed-core theorem splits D as the direct product of C_Q(T) and that center.
Any T-fixed element of the pair belongs to both disjoint factors and hence
is the identity. This supplies the fixed-free cubic action for the elementary
sixteen construction in Stellmacher (8.6)(b3), printed p.44.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_cost_four_initial_pair_fixed_free
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
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4)
    (T : Subgroup G) (hT : IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a)) :
    ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)) ⊓
        Subgroup.centralizer (T : Set G) = ⊥ := by
  have hbase := eight_six_common_structure_local ctx hcenter hquot hlength hcard
    previous hprev D L Q hD hL hQ
  have hsplit := eight_six_fixed_core_splitting ctx hcenter hquot hcard previous
    hprev.1 D L Q hD hL hQ data hbase.2.2.2 T hT
  have hinter := (eight_six_cost_four_core_quotient_card ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin
    hQ hcost).2
  have hpairQ : (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ≤ Q :=
    data.core_generation ▸ le_sup_left
  have hfixedD : Q ⊓ Subgroup.centralizer (T : Set G) ≤ D :=
    hsplit.1 ▸ le_sup_left
  apply bot_unique
  intro x hx
  have hfixed : x ∈ Q ⊓ Subgroup.centralizer (T : Set G) := ⟨hpairQ hx.1,hx.2⟩
  have hxZ : x ∈ ZAt ctx.Γ ctx.criticalPath.a := by
    rw [←hinter]
    exact ⟨hx.1,hfixedD hfixed⟩
  exact Subgroup.disjoint_def.mp hsplit.2.1 hfixed hxZ
end Stellmacher.SectionEight
