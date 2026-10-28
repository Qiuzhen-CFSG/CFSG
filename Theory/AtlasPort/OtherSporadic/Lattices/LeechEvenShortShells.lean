/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechEvenShortShells.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechPureFour

/-!
Exhaustion of the even Leech shells of squared norms four and six.
Halving the coordinates and applying the profile bounds recovers two-four family parameters.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem even_leech_half (x : IntegerCoordinates) (hx : x ∈ leech)
    (hp : ∀ i, x i % 2 = 0) :
    ∃ y : IntegerCoordinates, y ∈ evenHalfLattice ∧ x = (fun i => 2 * y i) := by
  obtain ⟨m,(rfl | rfl),hh,hc,hs⟩ := (mem_leech x).mp hx
  · have he := (even_congruences x).mpr ⟨hh,hc,by simpa using hs⟩
    obtain ⟨y,hy,hys,hxy⟩ := (mem_evenGolayLattice x).mp he
    exact ⟨y,⟨hy,hys⟩,funext hxy⟩
  · have hh := hh ((0,0),0)
    have hp := hp ((0,0),0)
    omega

theorem double_raw_norm (y : IntegerCoordinates) :
    integerDot (fun i => 2 * y i) (fun i => 2 * y i) = 4 * integerDot y y := by
  simp only [integerDot,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem half_without_large_coordinates (y : IntegerCoordinates) (hn : integerDot y y ≤ 16)
    (h3 : (evenMagnitudeSupport y 3).card = 0) (h4 : (evenMagnitudeSupport y 4).card = 0) (i : Omega) :
    y i = -2 ∨ y i = -1 ∨ y i = 0 ∨ y i = 1 ∨ y i = 2 := by
  have hb := even_small_coordinate y hn i
  have h3 : y i * y i ≠ 9 := by
    intro h
    have hm : i ∈ evenMagnitudeSupport y 3 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
    rw [Finset.card_eq_zero.mp h3] at hm
    exact Finset.notMem_empty _ hm
  have h4 : y i * y i ≠ 16 := by
    intro h
    have hm : i ∈ evenMagnitudeSupport y 4 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
    rw [Finset.card_eq_zero.mp h4] at hm
    exact Finset.notMem_empty _ hm
  have hcases : y i = -4 ∨ y i = -3 ∨ y i = -2 ∨ y i = -1 ∨ y i = 0 ∨
    y i = 1 ∨ y i = 2 ∨ y i = 3 ∨ y i = 4 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h <;> simp_all

theorem small_half_shape (y : IntegerCoordinates)
    (hb : ∀ i, y i = -2 ∨ y i = -1 ∨ y i = 0 ∨ y i = 1 ∨ y i = 2) :
    TwoFourShape (fun i => 2 * y i) (hammingNorm (integerReduction y))
      (evenMagnitudeSupport y 2).card := by
  refine ⟨?_,?_,?_⟩
  · intro i
    rcases hb i with h | h | h | h | h <;> simp [h]
  · congr 1
    ext i
    simp only [evenMagnitudeSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    change (2 * y i * (2 * y i) = 2 * 2) ↔ integerReduction y i ≠ 0
    rcases hb i with h | h | h | h | h <;> simp [integerReduction,h]
  · congr 1
    ext i
    simp only [evenMagnitudeSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor <;> intro h <;> nlinarith

theorem even_minimal_shell_iff (x : IntegerCoordinates) :
    (x ∈ leech ∧ (∀ i, x i % 2 = 0) ∧ integerDot x x = 32) ↔
      x ∈ twoFourFamily 0 2 ∪ twoFourFamily 8 0 := by
  constructor
  · rintro ⟨hx,hp,hn⟩
    obtain ⟨y,hy,he⟩ := even_leech_half x hx hp
    have hny : integerDot y y = 8 := by rw [he,double_raw_norm] at hn; omega
    rcases even_minimal_profiles y hy hny with ⟨hw,h2,h3,h4⟩ | ⟨hw,h2,h3,h4⟩
    · apply Finset.mem_union_left
      apply (twoFourFamily_iff _ _ _).mpr
      refine ⟨hx,?_⟩
      simpa only [he,hw,h2] using small_half_shape y
        (half_without_large_coordinates y (by omega) h3 h4)
    · apply Finset.mem_union_right
      apply (twoFourFamily_iff _ _ _).mpr
      refine ⟨hx,?_⟩
      simpa only [he,hw,h2] using small_half_shape y
        (half_without_large_coordinates y (by omega) h3 h4)
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simpa using twoFourFamily_properties 0 2 x hx
    · simpa using twoFourFamily_properties 8 0 x hx

theorem even_six_shell_iff (x : IntegerCoordinates) :
    (x ∈ leech ∧ (∀ i, x i % 2 = 0) ∧ integerDot x x = 48) ↔
      x ∈ twoFourFamily 12 0 ∪ twoFourFamily 8 1 := by
  constructor
  · rintro ⟨hx,hp,hn⟩
    obtain ⟨y,hy,he⟩ := even_leech_half x hx hp
    have hny : integerDot y y = 12 := by rw [he,double_raw_norm] at hn; omega
    rcases even_six_profiles y hy hny with ⟨hw,h2,h3,h4⟩ | ⟨hw,h2,h3,h4⟩
    · apply Finset.mem_union_right
      apply (twoFourFamily_iff _ _ _).mpr
      refine ⟨hx,?_⟩
      simpa only [he,hw,h2] using small_half_shape y
        (half_without_large_coordinates y (by omega) h3 h4)
    · apply Finset.mem_union_left
      apply (twoFourFamily_iff _ _ _).mpr
      refine ⟨hx,?_⟩
      simpa only [he,hw,h2] using small_half_shape y
        (half_without_large_coordinates y (by omega) h3 h4)
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simpa using twoFourFamily_properties 12 0 x hx
    · simpa using twoFourFamily_properties 8 1 x hx

end Atlas.Lattices
