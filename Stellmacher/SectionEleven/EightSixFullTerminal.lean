module

public import Stellmacher.SectionEight.GeneratedEightSixClassification
public import Stellmacher.SectionEleven.MultipleEightSixTerminal
public import Stellmacher.SectionEleven.SL2EdgeIntersection
public import Stellmacher.SectionEleven.SylowTerminalEdgePair

/-!
# All three source-local types in the central Section Eight branch

The actual generated Section Eight classification gives the complete A, B,
or C data on the same graph and with the prescribed defining subgroups.
The existing case-A realization supplies the G2(2)' type. In the other cases,
the initial SL2(2) quotient makes the edge intersection a two-group, and the
native edge-pair theorem supplies its actual ambient Sylow and trivial join
core. The restriction equivalence identifies its order with the native S
used in the case data. Thus the B and C records retain every source field,
including the actual three-Sylow T and both approved quotient actions.

Source: Stellmacher (8.6), its following three type definitions, and the
Section Eleven assembly of Theorem 1. No all-two-local solvability hypothesis
is required to retain all three alternatives.
-/

namespace Stellmacher.SectionEleven
open Later SectionsFiveToSeven
universe u

private noncomputable def terminalTypeGraph
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2) (R : Sylow 2 H) :
    EmbeddedLocalTypeGraph H where
  K := (P1 ⊔ P2 : Subgroup H)
  embedding := (P1 ⊔ P2).subtype
  embedding_injective := (P1 ⊔ P2).subtype_injective
  sylowIntersection := R
  S := (S0 : Subgroup H).subgroupOf (P1 ⊔ P2)
  P1 := P1.subgroupOf (P1 ⊔ P2)
  P2 := P2.subgroupOf (P1 ⊔ P2)
  Γ := ctx.Γ
  criticalPath := ctx.criticalPath

public theorem multiple_eight_six_full_terminal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ ≠ ⊥)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    IsOfGTwoTwoDerivedType H ∨ IsOfOmegaSixMinusThreeType H ∨
      IsOfOmegaEightPlusThreeType H := by
  obtain ⟨previous,D,L,Q,T,hA | hB | hC⟩ :=
    SectionEight.generated_eight_six_type_classification (ctx.toSectionEightContext hcomm) hcenter
  · exact Or.inl (multiple_eight_six_of_caseA ctx previous D L Q T hA)
  · have htwo := edge_intersection_isPGroup_of_SL2 ctx.sectionSeven ctx.Γ
      ctx.criticalPath.firstStep_adj hB.initial_quotient
    obtain ⟨R,hintersection,hcore,hcard⟩ :=
      sylow_terminal_edge_pair ctx ctx.criticalPath.firstStep_adj htwo
    have hnative : Nat.card ((S0 : Subgroup H).subgroupOf (P1 ⊔ P2)) = Nat.card R :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe ctx.sylow_le_join).toEquiv).trans hcard.symm
    exact Or.inr (Or.inl ⟨{
      toEmbeddedLocalTypeGraph := terminalTypeGraph ctx R
      intersection_eq := hintersection
      join_twoCore_eq_bot := hcore
      sylow_card_eq := hnative
      aPrev := previous
      D := D
      L := L
      Q := Q
      T := T
      caseB := hB }⟩)
  · have htwo := edge_intersection_isPGroup_of_SL2 ctx.sectionSeven ctx.Γ
      ctx.criticalPath.firstStep_adj hC.initial_quotient
    obtain ⟨R,hintersection,hcore,hcard⟩ :=
      sylow_terminal_edge_pair ctx ctx.criticalPath.firstStep_adj htwo
    have hnative : Nat.card ((S0 : Subgroup H).subgroupOf (P1 ⊔ P2)) = Nat.card R :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe ctx.sylow_le_join).toEquiv).trans hcard.symm
    exact Or.inr (Or.inr ⟨{
      toEmbeddedLocalTypeGraph := terminalTypeGraph ctx R
      intersection_eq := hintersection
      join_twoCore_eq_bot := hcore
      sylow_card_eq := hnative
      aPrev := previous
      D := D
      L := L
      Q := Q
      T := T
      caseC := hC }⟩)

end Stellmacher.SectionEleven

