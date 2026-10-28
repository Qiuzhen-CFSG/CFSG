module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.RankOne
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries

/-!
# Families without an outer involution

The actual M₁₁ and Suzuki quotient models force every involutory
automorphism of a perfect central cover to be inner. These families cannot
occur for the chosen r outside C_G(L)L. The odd-core hypothesis needed by
the cover transport follows from (E1) and relative component subnormality.
No covering kernel is silently discarded.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.3, 16.1.4(4), 16.1.5(3), and the inspection in the proof of 16.4.9(1),
printed pp.1171–1172 and 1189.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases
open Subgroup Theory.GroupTheory OuterResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The component inherits trivial odd core from its involution centralizer. -/
theorem component_oddCore (hG : HasEvenTypeCentralizers G)
    (h : CentralComponentSetup T z L) : pPrimeCore 2 L = ⊥ := by
  have hcore := Subgroup.IsSubnormal.pPrimeCore_eq_bot (hG.oddCore z h.involution)
    (L.subgroupOf (involutionCentralizer z)) h.component.2.1
  have hmap := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe h.component.1)
  simpa only [hcore, Subgroup.map_bot] using hmap.symm

/-- No M₁₁ quotient admits the outer involution chosen in 16.4.9. -/
theorem no_m11 (hG : HasEvenTypeCentralizers G)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M11) : False := by
  let := h.component.quasisimple
  have ha := involutionAction_order h (disjoint_iff.mp (faithful h)) hr hr2
  exact action_not_inner L (h.sylow_normalizes (h.le_sylow hr)) hout
    (OtherPreliminaries.m11_quotient_involution
      (component_oddCore hG h.toCentralComponentSetup) e (involutionAction h hr) ha).1

/-- The Suzuki exclusion includes the possible exceptional central covers of Sz(8). -/
theorem no_suzuki (hG : HasEvenTypeCentralizers G)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  let := h.component.quasisimple
  have ha := involutionAction_order h (disjoint_iff.mp (faithful h)) hr hr2
  exact action_not_inner L (h.sylow_normalizes (h.le_sylow hr)) hout
    (LiePreliminaries.suzuki_involution_inner
      (component_oddCore hG h.toCentralComponentSetup) hm e (involutionAction h hr) ha)

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases
