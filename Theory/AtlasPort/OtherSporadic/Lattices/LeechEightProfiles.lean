/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechEightProfiles.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechAxisShell
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechSixTwoRecovery

/-!
Exhaustion of even Leech vectors of squared norm eight.
The half-coordinate profile splits into axis, six-two, and two-four cases.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem half_three_zero (y : IntegerCoordinates) (h : (evenMagnitudeSupport y 3).card = 0)
    (i : Omega) : y i * y i ≠ 9 := by
  intro he
  have hm : i ∈ evenMagnitudeSupport y 3 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  rw [Finset.card_eq_zero.mp h] at hm
  exact Finset.notMem_empty _ hm

theorem double_magnitude_support (y : IntegerCoordinates) (r : ℤ) :
    evenMagnitudeSupport (fun i => 2 * y i) (2 * r) = evenMagnitudeSupport y r := by
  ext i
  simp only [evenMagnitudeSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor <;> intro h <;> nlinarith

theorem half_axis_shape (y : IntegerCoordinates) (hn : integerDot y y ≤ 16)
    (hw : hammingNorm (integerReduction y) = 0)
    (h2 : (evenMagnitudeSupport y 2).card = 0) (h4 : (evenMagnitudeSupport y 4).card = 1) :
    AxisEightShape (fun i => 2 * y i) := by
  have hr : integerReduction y = 0 := hammingNorm_eq_zero.mp hw
  have h2 (i : Omega) : y i * y i ≠ 4 := by
    intro hh
    have hm : i ∈ evenMagnitudeSupport y 2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
    rw [Finset.card_eq_zero.mp h2] at hm
    exact Finset.notMem_empty _ hm
  constructor
  · intro i
    have hb := even_small_coordinate y hn i
    have hp : y i % 2 = 0 := by
      have hh := congrFun hr i
      change ((y i : ℤ) : Bit) = 0 at hh
      exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hh)
    have hc : y i = -4 ∨ y i = -2 ∨ y i = 0 ∨ y i = 2 ∨ y i = 4 := by omega
    rcases hc with h | h | h | h | h <;> have hh := h2 i <;> simp_all
  · change (evenMagnitudeSupport (fun i => 2 * y i) (2 * 4)).card = 1
    rw [double_magnitude_support]; exact h4

theorem half_sixTwo_shape (y : IntegerCoordinates) (hn : integerDot y y ≤ 16)
    (hw : hammingNorm (integerReduction y) = 8)
    (h2 : (evenMagnitudeSupport y 2).card = 0) (h3 : (evenMagnitudeSupport y 3).card = 1)
    (h4 : (evenMagnitudeSupport y 4).card = 0) : SixTwoShape (fun i => 2 * y i) := by
  have h24 (i : Omega) : y i * y i ≠ 4 ∧ y i * y i ≠ 16 := by
    constructor
    · intro hh
      have hm : i ∈ evenMagnitudeSupport y 2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
      rw [Finset.card_eq_zero.mp h2] at hm
      exact Finset.notMem_empty _ hm
    · intro hh
      have hm : i ∈ evenMagnitudeSupport y 4 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
      rw [Finset.card_eq_zero.mp h4] at hm
      exact Finset.notMem_empty _ hm
  refine ⟨?_,?_,?_⟩
  · intro i
    have hb := even_small_coordinate y hn i
    have hc : y i = -4 ∨ y i = -3 ∨ y i = -2 ∨ y i = -1 ∨ y i = 0 ∨
      y i = 1 ∨ y i = 2 ∨ y i = 3 ∨ y i = 4 := by omega
    have hh := h24 i
    rcases hc with h | h | h | h | h | h | h | h | h <;> simp_all
  · have he : halfResidue (fun i => 2 * y i) 0 = integerReduction y := by
      ext i; simp [halfResidue,integerReduction]
    rw [he]; exact hw
  · change (evenMagnitudeSupport (fun i => 2 * y i) (2 * 3)).card = 1
    rw [double_magnitude_support]; exact h3

def twoFourEightVectors := (twoFourFamily 0 4 ∪ twoFourFamily 8 2) ∪
  (twoFourFamily 12 1 ∪ twoFourFamily 16 0)
def evenEightVectors := (axisEightVectors ∪ sixTwoFamily) ∪ twoFourEightVectors

theorem even_eight_shell_iff (x : IntegerCoordinates) :
    (x ∈ leech ∧ (∀ i, x i % 2 = 0) ∧ integerDot x x = 64) ↔ x ∈ evenEightVectors := by
  constructor
  · rintro ⟨hx,hp,hn⟩
    obtain ⟨y,hy,he⟩ := even_leech_half x hx hp
    have hny : integerDot y y = 16 := by rw [he,double_raw_norm] at hn; omega
    rcases even_eight_profiles y hy hny with h | h | h | h | h | h
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply (axisEightVectors_iff x).mpr
      rw [he]
      exact half_axis_shape y (by omega) h.1 h.2.1 h.2.2.2
    · have hs := small_half_shape y (half_without_large_coordinates y (by omega) h.2.2.1 h.2.2.2)
      have hm : x ∈ twoFourFamily 0 4 := (twoFourFamily_iff _ _ _).mpr ⟨hx,by simpa only [he,h.1,h.2.1] using hs⟩
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply (sixTwoFamily_iff x).mpr
      refine ⟨hx,?_⟩
      rw [he]
      exact half_sixTwo_shape y (by omega) h.1 h.2.1 h.2.2.1 h.2.2.2
    · have hs := small_half_shape y (half_without_large_coordinates y (by omega) h.2.2.1 h.2.2.2)
      have hm : x ∈ twoFourFamily 8 2 := (twoFourFamily_iff _ _ _).mpr ⟨hx,by simpa only [he,h.1,h.2.1] using hs⟩
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
    · have hs := small_half_shape y (half_without_large_coordinates y (by omega) h.2.2.1 h.2.2.2)
      have hm : x ∈ twoFourFamily 12 1 := (twoFourFamily_iff _ _ _).mpr ⟨hx,by simpa only [he,h.1,h.2.1] using hs⟩
      exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ hm))
    · have hs := small_half_shape y (half_without_large_coordinates y (by omega) h.2.2.1 h.2.2.2)
      have hm : x ∈ twoFourFamily 16 0 := (twoFourFamily_iff _ _ _).mpr ⟨hx,by simpa only [he,h.1,h.2.1] using hs⟩
      exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ hm))
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
        refine ⟨eightAxisVector_mem p,?_,eightAxisVector_norm p⟩
        intro i
        rcases (eightAxisVector_shape p).1 i with h | h | h <;> omega
      · exact sixTwoFamily_properties x hx
    · rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hx with hx | hx
      · simpa using twoFourFamily_properties 0 4 x hx
      · simpa using twoFourFamily_properties 8 2 x hx
      · simpa using twoFourFamily_properties 12 1 x hx
      · simpa using twoFourFamily_properties 16 0 x hx

end Atlas.Lattices
