module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NumericalGeometry
public import CFSG.Quasithin.ChapterG.Section10.FourDimensionalCenterBound

/-!
# Bounding the original tilded center in dimension four

The actual displaced center is the center modulo the marked point.
Transporting G.10's order-four bound through this equivalence bounds
Z(U)-tilde, without a choice of component or any action-kernel premise.
Source: Aschbacher--Smith 12.8.13(3) and14.3.14--15, pp.855,994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {C : GroupClass}
    {T : Sylow 2 G} {L M : Subgroup G}

/-- The order bound uses the literal displaced-center and tilded quotient maps. -/
theorem rankTwo_tilde_center_card_le_four_of_dimension_four
    (h : RankTwoHypothesis C T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) : Nat.card (F.tilde F.ZU) ≤ 4 := by
  have hZle : F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (F.X g) :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g))
  have hZH : F.ZU ≤ F.H := (map_subtype_le (center F.U)).trans F.U_le_H
  let ee := (rankTwo_terminal_center_equiv h F d hne g hgP hgH).symm.trans
    (F.terminalCenterTildeEquiv hZH)
  rw [← Nat.card_congr ee.toEquiv]
  exact (Nat.card_congr (subgroupOfEquivOfLe hZle).toEquiv).symm ▸
    hyp.smaller_card_le_four_of_dimension_four hd
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
