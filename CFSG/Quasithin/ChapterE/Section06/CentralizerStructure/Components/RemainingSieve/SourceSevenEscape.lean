module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.AlternatingActions
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceLocal
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
/-!
# The original escaping-hyperplane input to E.6.18

For either A₇ or its perfect triple cover, the actual elementary V-action
fixes the component's original Sylow intersection. The intrinsic seven-letter
calculation bounds this image by four and gives fixed-point generation when it
has order four. Pulling the action lines back to V constructs an escaping
hyperplane containing U, and proves the full alternating E.6.8 alternative.

This specialized source consequence needs only Hypothesis E.6.1 and the actual
seven-model component. It is independent of the other E.6.8 rows and supplies
the exact SevenEscape input used by the original E.6.18 consumer.
Source: Aschbacher–Smith, E.6.8(4) and E.6.18, pp.248,252.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
open AlternatingActions Hyperplanes.ComponentBalance
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V U L : Subgroup G}

theorem source_sevenAlternatingAlternative
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) (hseven : IsSeven L) :
    AlternatingAlternative M V U L := by
  let _ := h.elementary
  have hn := component_normalized h hU hL
  let _ := range_elementary hn
  obtain ⟨S,hfix⟩ := exists_sylow_fixed_by_range h hU hL hn
  have hm : Chapter1.Section02.LocalModels.IsAlternating L 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover L 6 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover L 7 := hseven.imp_right Or.inr
  have hc : Nat.card (actionHom hn).range ≤ 4 ∧
      (Nat.card (actionHom hn).range = 4 →
        (⊤ : Subgroup L) ≤ ⨆ (a : (actionHom hn).range) (_ : a ≠ 1),
          fixedSubgroup (a : MulAut L)) := by
    rcases hseven with he | ⟨hq,⟨eZ⟩,⟨e⟩⟩
    · obtain ⟨e⟩ := he
      exact Seven.equiv_calculations e (actionHom hn).range S hfix
    · let _ := hq
      have hz : Nat.card (center L) = 3 := by
        rw [Nat.card_congr eZ.toEquiv, Nat.card_eq_fintype_card]
        decide
      exact Seven.cover_calculations e hz (actionHom hn).range S hfix
  exact alternating_of_image_calculations h (source_earlierLocalFacts h) hU hL hn hm hc.1 hc.2

theorem source_sevenEscape (h : HypothesisE61 K T M V) : SevenEscape M V := by
  intro U hU L hL hs
  obtain ⟨W,hUW,hWV,hcor,he⟩ := (source_sevenAlternatingAlternative h hU hL hs).escape
  exact ⟨W,⟨hWV,hcor⟩,hUW,he⟩
end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
