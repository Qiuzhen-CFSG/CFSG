/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechEightShellCount.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechEightProfiles

/-!
The squared-norm-eight Leech shell has 398034000 vectors.
Coordinate bounds separate the even families, and parity separates the even and odd contributions.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem twoFour_coordinate_bound (k u : ℕ) (x : IntegerCoordinates) (hx : x ∈ twoFourFamily k u)
    (i : Omega) : -4 ≤ x i ∧ x i ≤ 4 := by
  rcases (twoFourFamily_shape k u x hx).1 i with h | h | h | h | h <;> omega

theorem twoFourEight_bound (x : IntegerCoordinates) (hx : x ∈ twoFourEightVectors) (i : Omega) :
    -4 ≤ x i ∧ x i ≤ 4 := by
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hx with hx | hx
  · exact twoFour_coordinate_bound 0 4 x hx i
  · exact twoFour_coordinate_bound 8 2 x hx i
  · exact twoFour_coordinate_bound 12 1 x hx i
  · exact twoFour_coordinate_bound 16 0 x hx i

theorem axisEight_disjoint_of_bound (S : Finset IntegerCoordinates)
    (hb : ∀ x ∈ S, ∀ i, -6 ≤ x i ∧ x i ≤ 6) : Disjoint axisEightVectors S := by
  apply Finset.disjoint_left.mpr
  intro x hx hs
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  have hh := hb _ hs p.1
  simp only [eightAxisVector,coordinateVector,Pi.single_eq_same] at hh
  split_ifs at hh <;> omega

theorem sixTwo_disjoint_of_bound (S : Finset IntegerCoordinates)
    (hb : ∀ x ∈ S, ∀ i, -4 ≤ x i ∧ x i ≤ 4) : Disjoint sixTwoFamily S := by
  apply Finset.disjoint_left.mpr
  intro x hx hs
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  have hh := hb _ hs p.2.1.val
  simp only [sixTwoFamilyVector,sixTwoVector,ite_true,signedSupport,dif_pos p.2.1.prop] at hh
  split_ifs at hh <;> omega

theorem twoFourEight_card : twoFourEightVectors.card = 198289440 := by
  have hd : Disjoint (twoFourFamily 0 4 ∪ twoFourFamily 8 2)
      (twoFourFamily 12 1 ∪ twoFourFamily 16 0) := by
    simp only [Finset.disjoint_union_left,Finset.disjoint_union_right]
    exact ⟨⟨twoFourFamily_disjoint _ _ _ _ (Or.inl (by decide)),
      twoFourFamily_disjoint _ _ _ _ (Or.inl (by decide))⟩,
      ⟨twoFourFamily_disjoint _ _ _ _ (Or.inl (by decide)),
      twoFourFamily_disjoint _ _ _ _ (Or.inl (by decide))⟩⟩
  rw [twoFourEightVectors,Finset.card_union_of_disjoint hd,
    Finset.card_union_of_disjoint (twoFourFamily_disjoint 0 4 8 2 (Or.inl (by decide))),
    Finset.card_union_of_disjoint (twoFourFamily_disjoint 12 1 16 0 (Or.inl (by decide))),
    pureFour_shape_counts.2,twoFour_shape_counts.2.2.2.1,
    twoFour_shape_counts.2.2.2.2.1,twoFour_shape_counts.2.2.2.2.2]

theorem evenEightVectors_card : evenEightVectors.card = 199066704 := by
  have ha : Disjoint axisEightVectors sixTwoFamily := axisEight_disjoint_of_bound _ (by
    intro x hx i
    rcases (sixTwoFamily_shape x hx).1 i with h | h | h | h | h <;> omega)
  have hat : Disjoint axisEightVectors twoFourEightVectors := axisEight_disjoint_of_bound _ (by
    intro x hx i; have hh := twoFourEight_bound x hx i; omega)
  have hst := sixTwo_disjoint_of_bound twoFourEightVectors twoFourEight_bound
  rw [evenEightVectors,Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hat,hst⟩),
    Finset.card_union_of_disjoint ha,axisEightVectors_card,sixTwoFamily_card,twoFourEight_card]

def oddEightVectors := oddNoFiveVectors 5 ∪ oddOneFiveVectors 2
def eightVectors := evenEightVectors ∪ oddEightVectors

theorem oddEightVectors_card : oddEightVectors.card = 198967296 := by
  rw [oddEightVectors,Finset.card_union_of_disjoint (odd_shapes_disjoint 5 2),
    odd_eight_shape_cards.1,odd_eight_shape_cards.2]

theorem eightVectors_iff (x : IntegerCoordinates) :
    x ∈ eightVectors ↔ x ∈ leech ∧ integerDot x x = 64 := by
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hh := (even_eight_shell_iff x).mpr hx
      exact ⟨hh.1,hh.2.2⟩
    · have hh := (odd_eight_shell_iff x).mpr hx
      exact ⟨hh.1,hh.2.2⟩
  · rintro ⟨hx,hn⟩
    rcases leech_coordinate_parity x hx with hp | hp
    · exact Finset.mem_union_left _ ((even_eight_shell_iff x).mp ⟨hx,hp,hn⟩)
    · exact Finset.mem_union_right _ ((odd_eight_shell_iff x).mp ⟨hx,hp,hn⟩)

theorem eightVectors_card : eightVectors.card = 398034000 := by
  rw [eightVectors,Finset.card_union_of_disjoint (opposite_parity_disjoint evenEightVectors oddEightVectors
    (fun x hx => ((even_eight_shell_iff x).mpr hx).2.1)
    (fun x hx => ((odd_eight_shell_iff x).mpr hx).2.1)),evenEightVectors_card,oddEightVectors_card]

theorem leech_eight_shell_card : Nat.card (LeechShell 8) = 398034000 := by
  rw [Nat.card_congr (leechShellFinsetEquiv 8 eightVectors eightVectors_iff),
    Nat.card_eq_fintype_card,Fintype.card_coe,eightVectors_card]

theorem leech_short_shell_counts : Nat.card (LeechShell 4) = 196560 ∧
    Nat.card (LeechShell 6) = 16773120 ∧ Nat.card (LeechShell 8) = 398034000 :=
  ⟨leech_minimal_shell_card,leech_six_shell_card,leech_eight_shell_card⟩

theorem leech_eight_shell_factor : Nat.card (LeechShell 8) = 48 * 8292375 := by
  rw [leech_eight_shell_card]

end Atlas.Lattices
