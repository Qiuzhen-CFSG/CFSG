module
public import Stellmacher.SectionEight.EightSixCostFourFixedQuotient
public import Stellmacher.SectionEight.EightSixSelectedResidualDecomposition
public import Stellmacher.SectionEight.EightSixSelectedOrbitCardEight
/-!
The actual residual commutator Y=[Qnext,O²(E)] has order thirty-two in the
cost-four branch of Stellmacher (8.6), and its selected orbit U has index
four. Keep the actual selected geometry, equation-one packet, minimum and
cost branch, together with the prescribed two-core Q.

The literal quotient Vnext/C has order sixteen, where C is its residual
fixed subgroup. The normalized-product identity |Y||C|=2|Vnext| gives
|Y|=32 after cancelling the positive cardinal of C. The proved |U|=8
then gives the source's |Y/U|=4. This is the numerical conclusion of the
first paragraph after assertion (14), printed p.44. It uses no raw
recognition of the action on U.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_six_cost_four_residual_card
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
    Nat.card (⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆ : Subgroup G) = 32 ∧
      QuotientCardEq ⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆
        (conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E) 4 := by
  have hquotient := eight_six_cost_four_fixed_quotient_card ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hproduct := eight_six_selected_residual_card_mul_fixed ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hpositive : 0 < Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer (twoResidualIn E : Set G) : Subgroup G) := Nat.card_pos
  dsimp only [QuotientCardEq] at hquotient
  have hY : Nat.card (⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆ : Subgroup G) = 32 := by
    nlinarith
  refine ⟨hY,?_⟩
  have hU := eight_six_selected_orbit_card_eight ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  change Nat.card (⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆ : Subgroup G) =
    4 * Nat.card (conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E)
  rw [hY,hU]

end Stellmacher.SectionEight
