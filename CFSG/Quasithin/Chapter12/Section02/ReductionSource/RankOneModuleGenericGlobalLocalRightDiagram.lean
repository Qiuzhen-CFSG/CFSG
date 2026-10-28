module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightDiagram
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalRightBender

/-!
# Source right-factor selection in the original Chapter 12 setup

All normalized Bender and symplectic rows, and linear rows outside field
four, now construct the full right factor and local preparation. The only
remaining selection row is the genuine marked linear field-four source,
including its scalar cover. Its S-action and the independent original
uniqueness-over-L implication remain explicit in the final assembly route.

The global owner qt-d-1222-rankone-generic-global retains that field-four
step and actual completion recognition. The independent source uniqueness
producer is qt-d-1222-rankone-global-uniqueness. This reduction does not
identify the ambient group from a faithful local triple.
Source: Aschbacher--Smith 5.1.10--11,5.2.4--5, pp.634--635,649--650;
the Chapter 12 application is on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual Chapter 12 input supplies a normalized factor unless its
residual has the marked linear field-four diagram geometry. -/
theorem rankOne_rightFactor_or_four_linear_diagram
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    {A B : Subgroup G} (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G)) :
    (∃ R : Subgroup G, Global.RightFactor T L H A B R) ∨ Global.RightLinearFourDiagramSource T L H :=
  Global.source_rightFactor_or_four_linear_diagram
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hpar c hN

/-- The constructed factors discharge every other row of local preparation.
The uniqueness implication is exactly the original independent source input. -/
theorem rankOne_global_preparation_or_four_linear_diagram
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G)) :
    (∃ A B R : Subgroup G, Global.Preparation T L H A B R) ∨ Global.RightLinearFourDiagramSource T L H := by
  by_cases hs : Global.RightLinearFourDiagramSource T L H
  · exact Or.inr hs
  · apply Or.inl
    apply D.rankOne_global_preparation_of_rightFactor h hmany hn hpsl hH hpar hN hunique
    intro A B c
    exact (D.rankOne_rightFactor_or_four_linear_diagram h hmany hn hpsl hH hpar c hN).resolve_right hs

/-- Local preparation now needs only the remaining field-four selection,
with the source's original exclusion of the projective PSL₃(4) quotient. -/
theorem rankOne_global_preparation_of_four_linear_selection
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hnot : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hfour : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      Global.RightLinearFourDiagramSource T L H →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        ∃ R : Subgroup G, Global.RightFactor T L H A B R) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R := by
  rcases D.rankOne_global_preparation_or_four_linear_diagram h hmany hn hpsl hH hpar hN hunique with hp | hs
  · exact hp
  · exact D.rankOne_global_preparation_of_rightFactor h hmany hn hpsl hH hpar hN hunique (hfour hnot hs)

/-- The original projective exclusion leaves precisely a special-linear
field-four quotient in the only unresolved source selection row. -/
theorem rankOne_global_preparation_or_four_linear_cover
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hnot : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G)) :
    (∃ A B R : Subgroup G, Global.Preparation T L H A B R) ∨
      (Global.RightLinearFourDiagramSource T L H ∧
        Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) := by
  rcases D.rankOne_global_preparation_or_four_linear_diagram h hmany hn hpsl hH hpar hN hunique with hp | hs
  · exact Or.inl hp
  · exact Or.inr ⟨hs,Global.four_linear_diagram_residual_isSL D.sylow_normalizes_component hH.1.1.2 hnot hs⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
