/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechShortShellCounts.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechEvenShortShells
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechIsometries

/-!
Exact counts of the Leech shells of squared norms four and six.
Disjoint even and odd coordinate families exhaust each shell and give its cardinality.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem twoFourFamily_disjoint (k u l v : ℕ) (h : k ≠ l ∨ u ≠ v) :
    Disjoint (twoFourFamily k u) (twoFourFamily l v) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hp := twoFourFamily_shape k u x hx
  have hq := twoFourFamily_shape l v x hy
  rcases h with h | h
  · exact h (hp.2.1.symm.trans hq.2.1)
  · exact h (hp.2.2.symm.trans hq.2.2)

def evenMinimalVectors := twoFourFamily 0 2 ∪ twoFourFamily 8 0
def evenSixVectors := twoFourFamily 12 0 ∪ twoFourFamily 8 1
def oddSixVectors := oddNoFiveVectors 3 ∪ oddOneFiveVectors 0

theorem evenMinimalVectors_card : evenMinimalVectors.card = 98256 := by
  rw [evenMinimalVectors,Finset.card_union_of_disjoint
    (twoFourFamily_disjoint 0 2 8 0 (Or.inl (by decide))),pureFour_shape_counts.1,twoFour_shape_counts.1]

theorem evenSixVectors_card : evenSixVectors.card = 8384512 := by
  rw [evenSixVectors,Finset.card_union_of_disjoint
    (twoFourFamily_disjoint 12 0 8 1 (Or.inl (by decide))),
    twoFour_shape_counts.2.1,twoFour_shape_counts.2.2.1]

theorem oddSixVectors_card : oddSixVectors.card = 8388608 := by
  rw [oddSixVectors,Finset.card_union_of_disjoint (odd_shapes_disjoint 3 0),
    odd_six_shape_cards.1,odd_six_shape_cards.2]

theorem leech_coordinate_parity (x : IntegerCoordinates) (hx : x ∈ leech) :
    (∀ i, x i % 2 = 0) ∨ (∀ i, x i % 2 = 1) := by
  obtain ⟨m,(rfl | rfl),hp,_,_⟩ := (mem_leech x).mp hx
  · exact Or.inl hp
  · exact Or.inr hp

theorem opposite_parity_disjoint (E O : Finset IntegerCoordinates)
    (he : ∀ x ∈ E, ∀ i, x i % 2 = 0) (ho : ∀ x ∈ O, ∀ i, x i % 2 = 1) : Disjoint E O := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have h0 := he x hx ((0,0),0)
  have h1 := ho x hy ((0,0),0)
  omega

def minimalVectors := evenMinimalVectors ∪ oddNoFiveVectors 1
def sixVectors := evenSixVectors ∪ oddSixVectors

theorem minimalVectors_iff (x : IntegerCoordinates) :
    x ∈ minimalVectors ↔ x ∈ leech ∧ integerDot x x = 32 := by
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hh := (even_minimal_shell_iff x).mpr hx
      exact ⟨hh.1,hh.2.2⟩
    · have hh := (odd_minimal_shell_iff x).mpr hx
      exact ⟨hh.1,hh.2.2⟩
  · rintro ⟨hx,hn⟩
    rcases leech_coordinate_parity x hx with hp | hp
    · exact Finset.mem_union_left _ ((even_minimal_shell_iff x).mp ⟨hx,hp,hn⟩)
    · exact Finset.mem_union_right _ ((odd_minimal_shell_iff x).mp ⟨hx,hp,hn⟩)

theorem sixVectors_iff (x : IntegerCoordinates) :
    x ∈ sixVectors ↔ x ∈ leech ∧ integerDot x x = 48 := by
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hh := (even_six_shell_iff x).mpr hx
      exact ⟨hh.1,hh.2.2⟩
    · have hh := (odd_six_shell_iff x).mpr hx
      exact ⟨hh.1,hh.2.2⟩
  · rintro ⟨hx,hn⟩
    rcases leech_coordinate_parity x hx with hp | hp
    · exact Finset.mem_union_left _ ((even_six_shell_iff x).mp ⟨hx,hp,hn⟩)
    · exact Finset.mem_union_right _ ((odd_six_shell_iff x).mp ⟨hx,hp,hn⟩)

theorem minimalVectors_card : minimalVectors.card = 196560 := by
  rw [minimalVectors,Finset.card_union_of_disjoint (opposite_parity_disjoint evenMinimalVectors (oddNoFiveVectors 1)
    (fun x hx => ((even_minimal_shell_iff x).mpr hx).2.1)
    (fun x hx => ((odd_minimal_shell_iff x).mpr hx).2.1)),
    evenMinimalVectors_card,odd_minimal_shape_card]

theorem sixVectors_card : sixVectors.card = 16773120 := by
  rw [sixVectors,Finset.card_union_of_disjoint (opposite_parity_disjoint evenSixVectors oddSixVectors
    (fun x hx => ((even_six_shell_iff x).mpr hx).2.1)
    (fun x hx => ((odd_six_shell_iff x).mpr hx).2.1)),
    evenSixVectors_card,oddSixVectors_card]

def leechShellFinsetEquiv (r : ℤ) (S : Finset IntegerCoordinates)
    (h : ∀ x, x ∈ S ↔ x ∈ leech ∧ integerDot x x = 8 * r) : LeechShell r ≃ {x // x ∈ S} where
  toFun x := ⟨x.val.val,(h _).mpr ⟨x.val.prop,x.prop⟩⟩
  invFun x := ⟨⟨x.val,((h _).mp x.prop).1⟩,((h _).mp x.prop).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem leech_minimal_shell_card : Nat.card (LeechShell 4) = 196560 := by
  rw [Nat.card_congr (leechShellFinsetEquiv 4 minimalVectors minimalVectors_iff),
    Nat.card_eq_fintype_card,Fintype.card_coe,minimalVectors_card]

theorem leech_six_shell_card : Nat.card (LeechShell 6) = 16773120 := by
  rw [Nat.card_congr (leechShellFinsetEquiv 6 sixVectors sixVectors_iff),
    Nat.card_eq_fintype_card,Fintype.card_coe,sixVectors_card]

end Atlas.Lattices
