/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeMinimum
public import Mathlib.GroupTheory.Index

/-!
Coordinate projections and the hexacode weight distribution.
Minimum distance makes three-coordinate projections bijective; coordinate fiber
counts and the total weight determine the distribution.

Source: `Atlas/Codes/HexacodeCounting.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators
open Finset
noncomputable instance : Fintype hexacode := Fintype.ofFinite hexacode

theorem weight_le_of_zero_on_embedding {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [Zero A] [DecidableEq A] (e : κ ↪ ι) (w : ι → A) (hw : ∀ j, w (e j) = 0) :
    hammingNorm w ≤ Fintype.card ι - Fintype.card κ := by
  classical
  unfold hammingNorm
  calc
    _ ≤ #(univ \ univ.image e) := by
      apply card_le_card
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      simp only [mem_sdiff, mem_univ, mem_image, not_exists, true_and]
      rintro j rfl
      exact hi (hw j)
    _ = _ := by simp [card_sdiff, card_image_of_injective _ e.injective]

def hexProjection (e : Fin 3 ↪ HexIndex) : hexacode →ₗ[Bit] (Fin 3 → K) where
  toFun w j := w.val (e j)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem hexProjection_injective (e : Fin 3 ↪ HexIndex) : Function.Injective (hexProjection e) := by
  intro u v h
  have hz : ∀ j, (u.val - v.val) (e j) = 0 := by
    intro j
    exact sub_eq_zero.mpr (congrFun h j)
  have hb := weight_le_of_zero_on_embedding e (u.val - v.val) hz
  have hd := hexacode_minimum (u.val - v.val) (hexacode.sub_mem u.prop v.prop)
  have hzero : u.val - v.val = 0 := by
    by_contra hn
    have hm := hd hn
    norm_num [HexIndex] at hb
    omega
  exact Subtype.ext (sub_eq_zero.mp hzero)

theorem hexProjection_bijective (e : Fin 3 ↪ HexIndex) : Function.Bijective (hexProjection e) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨hexProjection_injective e, ?_⟩
  rw [hexacode_card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_fun, K, Letter, ZMod.card]

def hexCoordinate (i : HexIndex) : hexacode →ₗ[Bit] K where
  toFun w := w.val i
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem hexCoordinate_surjective (i : HexIndex) : Function.Surjective (hexCoordinate i) := by
  have hh : ∀ i : HexIndex, ∃ j k : Fin 6, hexGenerators j i = a ∧ hexGenerators k i = b := by decide
  obtain ⟨j, k, hj, hk⟩ := hh i
  intro u
  refine ⟨u.1 • hexBasis j + u.2 • hexBasis k, ?_⟩
  change u.1 • (hexBasis j : HexWord) i + u.2 • (hexBasis k : HexWord) i = u
  rw [hexBasis_coe, hexBasis_coe, hj, hk]
  ext <;> simp [a, b]

theorem hexCoordinate_fiber (i : HexIndex) (v : K) :
    #{w : hexacode | hexCoordinate i w = v} = 16 := by
  classical
  have he (u : K) : #{w : hexacode | hexCoordinate i w = u} =
      #{w : hexacode | hexCoordinate i w = v} :=
    AddMonoidHom.card_fiber_eq_of_mem_range (hexCoordinate i)
      (hexCoordinate_surjective i u) (hexCoordinate_surjective i v)
  have h := sum_card_fiberwise_eq_card_filter (univ : Finset hexacode) (univ : Finset K) (hexCoordinate i)
  simp only [he, sum_const, card_univ, smul_eq_mul, mem_univ, filter_true] at h
  have hc : Fintype.card hexacode = 64 := by simpa [Nat.card_eq_fintype_card] using hexacode_card
  norm_num [K, Letter, ZMod.card, hc] at h
  omega

noncomputable def hexWeightCount (k : ℕ) : ℕ := #{w : hexacode | hammingNorm w.val = k}

theorem hex_weights (w : hexacode) : hammingNorm w.val = 0 ∨ hammingNorm w.val = 4 ∨ hammingNorm w.val = 6 := by
  have hmax := hammingNorm_le_card_fintype (x := w.val)
  have hmin := hexacode_minimum w.val w.prop
  have heven := hexacode_even w.val w.prop
  have hz := hammingNorm_eq_zero (x := w.val)
  norm_num [HexIndex] at hmax
  obtain ⟨k, hk⟩ := heven
  by_cases h : w.val = 0
  · left; exact hz.mpr h
  · have := hmin h
    omega

theorem hexWeightCount_zero : hexWeightCount 0 = 1 := by
  classical
  have h : ∀ w : hexacode, hammingNorm w.val = 0 ↔ w = 0 := by
    intro w
    rw [hammingNorm_eq_zero]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have he : (univ.filter (fun w : hexacode => hammingNorm w.val = 0)) = ({0} : Finset hexacode) := by
    ext w
    simp [h]
  change _ = 1
  unfold hexWeightCount
  rw [he]
  rfl

theorem hex_weight_total : ∑ w : hexacode, hammingNorm w.val = 288 := by
  classical
  simp only [hammingNorm, card_filter]
  rw [sum_comm]
  have hf (i : HexIndex) : (∑ w : hexacode, if w.val i ≠ 0 then 1 else 0) = 48 := by
    rw [← card_filter]
    have h0 := hexCoordinate_fiber i 0
    have hc : Fintype.card hexacode = 64 := by simpa [Nat.card_eq_fintype_card] using hexacode_card
    change #{w : hexacode | ¬ hexCoordinate i w = 0} = _
    have h := card_filter_add_card_filter_not (s := univ) (fun w : hexacode => hexCoordinate i w = 0)
    rw [card_univ, hc, h0] at h
    omega
  simp only [ite_not] at hf
  simp [hf, HexIndex]

theorem hexacode_weight_distribution (k : ℕ) :
    hexWeightCount k = if k = 0 then 1 else if k = 4 then 45 else if k = 6 then 18 else 0 := by
  classical
  have ht : hexWeightCount 0 + hexWeightCount 4 + hexWeightCount 6 = 64 := by
    have he (w : hexacode) :
        (if hammingNorm w.val = 0 then 1 else 0) + (if hammingNorm w.val = 4 then 1 else 0) +
          (if hammingNorm w.val = 6 then 1 else 0) = 1 := by
      rcases hex_weights w with h | h | h <;> simp [h]
    have hs := congrArg (fun f : hexacode → ℕ => ∑ w, f w) (funext he)
    simp only [sum_add_distrib, ← card_filter, sum_const, card_univ, smul_eq_mul, mul_one] at hs
    change hexWeightCount 0 + hexWeightCount 4 + hexWeightCount 6 = Fintype.card hexacode at hs
    simpa only [← Nat.card_eq_fintype_card, hexacode_card] using hs
  have hm : 4 * hexWeightCount 4 + 6 * hexWeightCount 6 = 288 := by
    have he (w : hexacode) :
        4 * (if hammingNorm w.val = 4 then 1 else 0) +
          6 * (if hammingNorm w.val = 6 then 1 else 0) = hammingNorm w.val := by
      rcases hex_weights w with h | h | h <;> simp [h]
    have hs := congrArg (fun f : hexacode → ℕ => ∑ w, f w) (funext he)
    simp only [sum_add_distrib, ← mul_sum, ← card_filter] at hs
    change 4 * hexWeightCount 4 + 6 * hexWeightCount 6 = ∑ w : hexacode, hammingNorm w.val at hs
    rw [hex_weight_total] at hs
    exact hs
  rw [hexWeightCount_zero] at ht
  have h4 : hexWeightCount 4 = 45 := by omega
  have h6 : hexWeightCount 6 = 18 := by omega
  by_cases h0 : k = 0
  · subst k; simpa using hexWeightCount_zero
  by_cases hk4 : k = 4
  · subst k; simpa using h4
  by_cases hk6 : k = 6
  · subst k; simpa using h6
  have he : hexWeightCount k = 0 := by
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro w _ hw
    rcases hex_weights w with h | h | h <;> omega
  simp [h0, hk4, hk6, he]
end Atlas.Codes
