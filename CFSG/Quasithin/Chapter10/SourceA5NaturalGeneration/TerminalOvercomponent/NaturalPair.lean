module

public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.CommonComponent
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverOrders

/-!
# The proper common component for the actual centerless natural A5 blocks

The source natural-block order formula gives order 960 for each block once
its intrinsic two-core is the natural module and its center is trivial.
Consequently two distinct such blocks have a strictly larger common
C-component. Its local Sylow statements retain the actual ambient Sylow
intersection and make no assertion that the common block Sylow is maximal
in the containing component.

Source: Aschbacher--Smith 10.2.3(4), printed p.747, using C.1.12.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
variable {G : Type*} [Group G] [Finite G]

private theorem centerless_natural_four_card {X : Type*} [Group X] [Finite X]
    (h : ChapterC.IsL2EvenBlock X 2) (hc : pCore 2 X = ChapterC.blockU X)
    (hz : center X = ⊥) : Nat.card X = 960 := by
  have hquot := h.center_quotient_card hc
  rw [card_eq_card_quotient_mul_card_subgroup (center X), hquot, hz, card_bot]
  norm_num

/-- The natural structure discharges the equal-order premise in the original
proper common-component construction. -/
theorem source_centerless_natural_pair_proper_common_component
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    (T : Sylow 2 G) {L K D : Subgroup G}
    (hL : L ∈ Chapter1.L G T) (hK : K ∈ Chapter1.L G T)
    (hDL : D ≤ L) (hmove : ⁅K, D⁆ = K) (hne : L ≠ K)
    (hLn : ChapterC.IsL2EvenBlock L 2) (hKn : ChapterC.IsL2EvenBlock K 2)
    (hLc : pCore 2 L = ChapterC.blockU L) (hKc : pCore 2 K = ChapterC.blockU K)
    (hLz : center L = ⊥) (hKz : center K = ⊥) :
    ∃ C : Subgroup G, C.IsCComponent ∧ L < C ∧ K < C ∧
      (∀ E : Subgroup G, E.IsCComponent → L ≤ E → E = C) ∧
      ∃ S : Sylow 2 C, (S : Subgroup C) = (T : Subgroup G).subgroupOf C ∧
        L.subgroupOf C ∈ ChapterA.Section03.localCComponents S ∧
        K.subgroupOf C ∈ ChapterA.Section03.localCComponents S := by
  exact source_natural_pair_proper_common_component hQ T hL hK hDL hmove hne
    ((centerless_natural_four_card hLn hLc hLz).trans
      (centerless_natural_four_card hKn hKc hKz).symm)

end CFSG.Quasithin.Chapter10
