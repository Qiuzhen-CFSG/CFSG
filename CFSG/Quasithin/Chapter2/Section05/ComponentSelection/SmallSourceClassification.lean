module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RankTwoBinarySource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallModelSource
/-! # The original small-component source classification
The actual 2.5.2 alternatives, followed by the unconditional field reduction
2.5.7, leave A₆, PSL₃(2), PSL₃(3), M₁₁, and the original prime linear family.
The model facts apply to the literal component and its original Sylow
intersection, proving assertions (1), (2: simplicity), and (3) of 2.5.8.
Source: Aschbacher--Smith, printed pp.552--556.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement ClassificationModels
open Chapter15.Section03.Candidates.ComponentStructure
open Chapter1.Section02.LocalModels ChapterA.Section02
variable {G : Type*} [Group G] [Finite G]
  {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The surviving source catalogue, with no field or exceptional-branch premise. -/
theorem MathieuSourceSetup.small_remaining_component
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = L ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel L) : IsSmallRemainingComponent L := by
  rcases MathieuSourceSetup.nonBender_model c hG localC129Input_knownSimple hempty hb
    with h | h | (h | h) | h
  · exact Or.inl (MathieuSourceSetup.derived_symplectic_binary_model c hG hempty hgen h)
  · exact Or.inr (Or.inl (MathieuSourceSetup.linear_cover_binary_model c hG hempty hgen h))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- Source 2.5.8(1),(2: simplicity),(3), on the original component and Sylow. -/
theorem MathieuSourceSetup.small_source_structure
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = L ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel L) :
    IsSmallRemainingComponent L ∧ IsSimpleGroup L ∧
      IsPGroup 2 (MulAut.Outer L) ∧
      SourceSylowTwoShape (((S : Subgroup H).map H.subtype).subgroupOf L) := by
  have hm := MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  exact ⟨hm, MathieuSourceSetup.component_simple c hG hempty hgen,
    MathieuSourceSetup.small_model_outer_and_sylow c hm⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
