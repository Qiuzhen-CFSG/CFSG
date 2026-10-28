module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.Planes
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.Contradiction

/-!
# The noncentral branch from actual local action data

The earlier quotient facts force choice (2) under [V,Y_L] = 1. The
orthogonal coordinate calculation gives the two plane normalizer bounds.
The extension calculation then proves V ≤ U_L C_WL(L), and the two actual
Y_C action possibilities contradict those bounds.

This module completes that conditional calculation. It does not yet claim
the source application of 15.3.23: the local Sylow comparison excluding
C.1.34(4), transport of all surviving full cases, and construction of the
natural moving quotient, radical involution and Y_C action alternatives
remain separate prerequisites. All of these must be discharged by the
final source assembly. No local Sylow is identified with S here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.23,
printed p.1128; C.1.34, pp.136–137; B.4.8, pp.91–92.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension

variable {G : Type*} [Group G] [Finite G]

/-- The first-page noncentrality calculation with every local representation
obligation explicit. The source application must construct q, l, and hcases. -/
theorem nontrivial_of_local_actions (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    [(actionKernel d c.L).Normal] [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (hN : overgroup d c.L ≤ normalizer (d.componentSpan c.L : Set G))
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hcoreR : c.L.pCoreIn 2 ≤ d.R)
    (hYL : YL d c.L ≠ ⊥)
    (he9 : Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* ComponentIntersection.ElementaryNine))
    (h7 : d.Y ⊓ centralizer (d.V : Set G) ≤ d.Y.pCoreIn 2 ∨
      Nat.card (d.Y ⧸ pCore 2 d.Y) = 27)
    (h7image : d.action.image d.Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hgen : d.Yplus = YL d c.L ⊔ YC d c.L)
    (hnormalizes : d.Yplus ≤ normalizer (c.L : Set G))
    {m : ℕ}
    (q : ModuleQuotient (moving (componentRepresentation d c.L hN
      (core_centralizes_span d c.L hcoreR (hR.le.trans inf_le_right)) e)).toRepresentation m)
    (l : c.L) (hlR : (l : G) ∈ d.R)
    (ht : e (QuotientGroup.mk l) ^ 2 = 1) (hne : e (QuotientGroup.mk l) ≠ 1)
    (hcases : CentralizerActionCases d c.L hN
      (core_centralizes_span d c.L hcoreR (hR.le.trans inf_le_right)) e) :
    ⁅d.V, YL d c.L⁆ ≠ ⊥ := by
  apply nontrivial_of_module_and_plane_actions d c.L hN e c.outside hR hcoreR q
    l hlR ht hne hnormalizes hcases
  exact centralizing_plane_actions d c.L hYL he9 h7 h7image hgen

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension

end
