/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechEvenProfiles.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechOddShells
public import Theory.AtlasPort.OtherSporadic.Codes.GolayDistribution

/-!
Possible magnitude profiles of small even Leech vectors.
Norm equations and Golay weight restrictions limit the coordinate supports.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def evenMagnitudeSupport (y : IntegerCoordinates) (k : ℤ) : Finset Omega :=
  Finset.univ.filter (fun i => y i * y i = k * k)

theorem even_small_coordinate (y : IntegerCoordinates) (hn : integerDot y y ≤ 16)
    (i : Omega) : -4 ≤ y i ∧ y i ≤ 4 := by
  have hh : y i * y i ≤ integerDot y y :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (y j)) (Finset.mem_univ i)
  constructor <;> nlinarith

theorem even_norm_profile (y : IntegerCoordinates) (hn : integerDot y y ≤ 16) :
    integerDot y y = (hammingNorm (integerReduction y) : ℤ) +
      4 * ((evenMagnitudeSupport y 2).card : ℤ) +
      8 * ((evenMagnitudeSupport y 3).card : ℤ) +
      16 * ((evenMagnitudeSupport y 4).card : ℤ) := by
  have hh (i : Omega) : y i * y i =
      (if integerReduction y i = 0 then 0 else 1) +
      (if i ∈ evenMagnitudeSupport y 2 then 4 else 0) +
      (if i ∈ evenMagnitudeSupport y 3 then 8 else 0) +
      (if i ∈ evenMagnitudeSupport y 4 then 16 else 0) := by
    have hb := even_small_coordinate y hn i
    have he : y i = -4 ∨ y i = -3 ∨ y i = -2 ∨ y i = -1 ∨ y i = 0 ∨
      y i = 1 ∨ y i = 2 ∨ y i = 3 ∨ y i = 4 := by omega
    rcases he with h | h | h | h | h | h | h | h | h <;>
      simp [integerReduction,evenMagnitudeSupport,h] <;> decide
  simp only [integerDot,hh,Finset.sum_add_distrib]
  simp only [hammingNorm,evenMagnitudeSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  simp only [Finset.sum_ite,Finset.sum_const_zero,zero_add,Finset.sum_const,nsmul_eq_mul]
  ring

theorem evenHalf_zero_residue_norm (y : IntegerCoordinates) (hy : y ∈ evenHalfLattice)
    (hr : integerReduction y = 0) : 8 ∣ integerDot y y := by
  let x : IntegerCoordinates := fun i => 2 * y i
  have hx : x ∈ evenGolayLattice :=
    (mem_evenGolayLattice x).mpr ⟨y,hy.1,hy.2,fun _ => rfl⟩
  have hh : halfResidue x 0 = 0 := by
    have he : halfResidue x 0 = integerReduction y := by
      ext i; simp [halfResidue,integerReduction,x]
    exact he.trans hr
  have hn : integerDot x x = 4 * integerDot y y := by
    simp only [integerDot,x,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hd := zero_residue_norm_divisible x hx hh
  rw [hn] at hd
  omega

theorem even_three_support_le_weight (y : IntegerCoordinates) :
    (evenMagnitudeSupport y 3).card ≤ hammingNorm (integerReduction y) := by
  apply Finset.card_le_card
  intro i hi
  simp only [evenMagnitudeSupport,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  change i ∈ Finset.univ.filter (fun i => integerReduction y i ≠ 0)
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have h : y i = -3 ∨ y i = 3 := by
    have he : (y i - 3) * (y i + 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp he with h | h
    · right; omega
    · left; omega
  rcases h with h | h <;> simp [integerReduction,h] <;> decide

theorem even_minimal_profiles (y : IntegerCoordinates) (hy : y ∈ evenHalfLattice)
    (hn : integerDot y y = 8) :
    (hammingNorm (integerReduction y) = 0 ∧ (evenMagnitudeSupport y 2).card = 2 ∧
      (evenMagnitudeSupport y 3).card = 0 ∧ (evenMagnitudeSupport y 4).card = 0) ∨
    (hammingNorm (integerReduction y) = 8 ∧ (evenMagnitudeSupport y 2).card = 0 ∧
      (evenMagnitudeSupport y 3).card = 0 ∧ (evenMagnitudeSupport y 4).card = 0) := by
  have he := even_norm_profile y (by omega)
  have hw := golay_weights ⟨integerReduction y,hy.1⟩
  have hb := even_three_support_le_weight y
  simp only at hw
  rcases hw with hw | hw | hw | hw | hw <;> omega

theorem even_six_profiles (y : IntegerCoordinates) (hy : y ∈ evenHalfLattice)
    (hn : integerDot y y = 12) :
    (hammingNorm (integerReduction y) = 8 ∧ (evenMagnitudeSupport y 2).card = 1 ∧
      (evenMagnitudeSupport y 3).card = 0 ∧ (evenMagnitudeSupport y 4).card = 0) ∨
    (hammingNorm (integerReduction y) = 12 ∧ (evenMagnitudeSupport y 2).card = 0 ∧
      (evenMagnitudeSupport y 3).card = 0 ∧ (evenMagnitudeSupport y 4).card = 0) := by
  have he := even_norm_profile y (by omega)
  have hw := golay_weights ⟨integerReduction y,hy.1⟩
  have hz : hammingNorm (integerReduction y) ≠ 0 := by
    intro hz
    have hd := evenHalf_zero_residue_norm y hy (hammingNorm_eq_zero.mp hz)
    omega
  simp only at hw
  rcases hw with hw | hw | hw | hw | hw <;> omega

theorem even_eight_profiles (y : IntegerCoordinates) (hy : y ∈ evenHalfLattice)
    (hn : integerDot y y = 16) :
    (hammingNorm (integerReduction y) = 0 ∧ (evenMagnitudeSupport y 2).card = 0 ∧
      (evenMagnitudeSupport y 3).card = 0 ∧ (evenMagnitudeSupport y 4).card = 1) ∨
    (hammingNorm (integerReduction y) = 0 ∧ (evenMagnitudeSupport y 2).card = 4 ∧
      (evenMagnitudeSupport y 3).card = 0 ∧ (evenMagnitudeSupport y 4).card = 0) ∨
    (hammingNorm (integerReduction y) = 8 ∧ (evenMagnitudeSupport y 2).card = 0 ∧
      (evenMagnitudeSupport y 3).card = 1 ∧ (evenMagnitudeSupport y 4).card = 0) ∨
    (hammingNorm (integerReduction y) = 8 ∧ (evenMagnitudeSupport y 2).card = 2 ∧
      (evenMagnitudeSupport y 3).card = 0 ∧ (evenMagnitudeSupport y 4).card = 0) ∨
    (hammingNorm (integerReduction y) = 12 ∧ (evenMagnitudeSupport y 2).card = 1 ∧
      (evenMagnitudeSupport y 3).card = 0 ∧ (evenMagnitudeSupport y 4).card = 0) ∨
    (hammingNorm (integerReduction y) = 16 ∧ (evenMagnitudeSupport y 2).card = 0 ∧
      (evenMagnitudeSupport y 3).card = 0 ∧ (evenMagnitudeSupport y 4).card = 0) := by
  have he := even_norm_profile y (by omega)
  have hw := golay_weights ⟨integerReduction y,hy.1⟩
  have hb := even_three_support_le_weight y
  simp only at hw
  rcases hw with hw | hw | hw | hw | hw <;> omega

end Atlas.Lattices
