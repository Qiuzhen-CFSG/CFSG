/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechSmallShells.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechEightShellCount

/-!
The three small Leech shells and the eight norm-eight coordinate shapes.
The package assembles exhaustive family descriptions and their proved cardinalities.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

/-- The eight absolute-coordinate shapes of squared norm eight. -/
inductive NormEightTag where
  | A | B | C4 | D8 | E12 | F16 | G | H
  deriving DecidableEq, Repr

def normEightTagVectors : NormEightTag → Finset IntegerCoordinates
  | .A => axisEightVectors
  | .B => sixTwoFamily
  | .C4 => twoFourFamily 0 4
  | .D8 => twoFourFamily 8 2
  | .E12 => twoFourFamily 12 1
  | .F16 => twoFourFamily 16 0
  | .G => oddOneFiveVectors 2
  | .H => oddNoFiveVectors 5

def normEightTagCount : NormEightTag → ℕ
  | .A => 48
  | .B => 777216
  | .C4 => 170016
  | .D8 => 46632960
  | .E12 => 126615552
  | .F16 => 24870912
  | .G => 24870912
  | .H => 174096384

theorem normEightTag_card (t : NormEightTag) : (normEightTagVectors t).card = normEightTagCount t := by
  cases t
  · exact axisEightVectors_card
  · exact sixTwoFamily_card
  · exact pureFour_shape_counts.2
  · exact twoFour_shape_counts.2.2.2.1
  · exact twoFour_shape_counts.2.2.2.2.1
  · exact twoFour_shape_counts.2.2.2.2.2
  · exact odd_eight_shape_cards.2
  · exact odd_eight_shape_cards.1

theorem normEightTag_exhaustive (x : IntegerCoordinates) :
    (∃ t : NormEightTag, x ∈ normEightTagVectors t) ↔ x ∈ leech ∧ integerDot x x = 64 := by
  rw [← eightVectors_iff]
  constructor
  · rintro ⟨t,ht⟩
    cases t <;> simp only [normEightTagVectors] at ht
    all_goals simp only [eightVectors,evenEightVectors,twoFourEightVectors,oddEightVectors,
      Finset.mem_union]
    all_goals tauto
  · intro hx
    simp only [eightVectors,evenEightVectors,twoFourEightVectors,oddEightVectors,
      Finset.mem_union] at hx
    rcases hx with ((h | h) | ((h | h) | (h | h))) | (h | h)
    · exact ⟨.A,h⟩
    · exact ⟨.B,h⟩
    · exact ⟨.C4,h⟩
    · exact ⟨.D8,h⟩
    · exact ⟨.E12,h⟩
    · exact ⟨.F16,h⟩
    · exact ⟨.H,h⟩
    · exact ⟨.G,h⟩

structure SmallShellConstruction : Prop where
  minimal_count : Nat.card (LeechShell 4) = 196560
  six_count : Nat.card (LeechShell 6) = 16773120
  eight_count : Nat.card (LeechShell 8) = 398034000
  minimal_coordinates : ∀ x, x ∈ minimalVectors ↔ x ∈ leech ∧ integerDot x x = 32
  six_coordinates : ∀ x, x ∈ sixVectors ↔ x ∈ leech ∧ integerDot x x = 48
  eight_coordinates : ∀ x, x ∈ eightVectors ↔ x ∈ leech ∧ integerDot x x = 64
  two_four_recovery : ∀ k u x, x ∈ twoFourFamily k u ↔ x ∈ leech ∧ TwoFourShape x k u
  axis_recovery : ∀ x, x ∈ axisEightVectors ↔ AxisEightShape x
  six_two_recovery : ∀ x, x ∈ sixTwoFamily ↔ x ∈ leech ∧ SixTwoShape x
  tags_exhaustive : ∀ x, (∃ t, x ∈ normEightTagVectors t) ↔ x ∈ leech ∧ integerDot x x = 64
  tag_counts : ∀ t, (normEightTagVectors t).card = normEightTagCount t

theorem leech_small_shells_constructed : SmallShellConstruction where
  minimal_count := leech_minimal_shell_card
  six_count := leech_six_shell_card
  eight_count := leech_eight_shell_card
  minimal_coordinates := minimalVectors_iff
  six_coordinates := sixVectors_iff
  eight_coordinates := eightVectors_iff
  two_four_recovery := twoFourFamily_iff
  axis_recovery := axisEightVectors_iff
  six_two_recovery := sixTwoFamily_iff
  tags_exhaustive := normEightTag_exhaustive
  tag_counts := normEightTag_card

end Atlas.Lattices
