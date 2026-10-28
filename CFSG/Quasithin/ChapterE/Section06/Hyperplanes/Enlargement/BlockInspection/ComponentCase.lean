module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.LocalFacts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ModelExclusions
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.LinearTwo
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.Normality
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.SymplecticParameters
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ThreeDimensional
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.SymplecticFour

/-!
# Ordinary component overgroups of the small blocks in E.6.23

First construct C_V(X) = A by restricting the component to a hypothetical
larger fixed-space centralizer and using E.6.22. Inspect the complete E.6.8
alternatives, excluding rank-one action, A₇, both triple covers, Suzuki, and
PSL₂(4). The remaining Borel models and the Sp₄(4) root action are precisely
the two explicit model-exclusion obligations below.

Once they are discharged, the actual binary derived symplectic equivalence
gives X ≃ A₆. Exact C.1.9 and a two-part argument establish normality of L
inside C_X(U). Thus every clause of ProperSixEnlargement is constructed.

The conditional assembly is exposed separately so that the two model
calculations can be checked in isolation. The final theorem below discharges
those obligations and proves `ProperComponentInspection` from the permitted
earlier source results. No orbit-containment assertion or block-persistence
conclusion is used here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
open ComponentBalance Components

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- Assemble all clauses of the ordinary-component inspection once the two
remaining, explicitly named intrinsic model exclusions have been proved. -/
theorem properComponentInspection_of_model_exclusions [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hchar : ∀ W : Subgroup G, IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    (h8 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G,
      CentralizerComponent A X →
        ComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X)
    (h18 : SevenExcluded M V) (h21 : OddCoreFree V) (h19 : BlockCommutationInput G)
    (hthree : ThreeDimensionalExclusion M V) (hfour : SymplecticFourExclusion M V) :
    ProperComponentInspection M V := by
  intro U hU hUh L hL he A hA hAU hc X hLX hX
  have hXe : ¬ X ≤ M := fun hh => he (hLX.le.trans hh)
  have hr := component_actionCorank_two h hchar hA.1 hc hX hXe
  have hfixed := component_fixedSpace_eq h hchar hA.1 hc hX hXe
  have hmodel : Chapter1.Section02.LocalModels.IsAlternating X 6 := by
    rcases remaining_alternatives h18 h21 hA hc hX hr (h8 A hA X hX) with b | ⟨n, b⟩
    · rcases borel_models_at_two b with hm | hm
      · exact (component_not_linearTwo h hUh hL hA hc hX hLX.le hfixed hm).elim
      · exact (hthree U hU hUh L hL he A hA hAU hc X hLX hX hfixed b hm).elim
    · rcases symplectic_parameters hr b with hn | ⟨hn, hp, ha⟩
      · subst n
        exact binary_symplectic_model b.model
      · subst n
        exact (hfour U hU hUh L hL he A hA hAU hc X hLX hX hfixed b hp ha).elim
  exact ⟨hLX, hX, hmodel, hfixed,
    smallBlock_normal_in_six_centralizer h19 h21 hU hL hLX.le hmodel⟩

/-- The ordinary-component inspection from the genuine E.6.1 boundary.

The two intrinsic model exclusions are discharged by their actual Borel and
symplectic root-action calculations; the conditional assembly above then
constructs the full `ProperSixEnlargement` record for every escaping small
block. -/
theorem properComponentInspection [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (_h15 : HypothesisE615 V)
    (hchar : ∀ W : Subgroup G, IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    (h8 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G,
      CentralizerComponent A X →
        ComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X)
    (h18 : SevenExcluded M V) (h21 : OddCoreFree V) (h19 : BlockCommutationInput G) :
    ProperComponentInspection M V := by
  exact properComponentInspection_of_model_exclusions h hchar h8 h18 h21 h19
    (threeDimensionalExclusion h) (symplecticFour_exclusion h)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
