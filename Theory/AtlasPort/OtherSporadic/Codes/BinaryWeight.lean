/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.BinaryLift

/-!
Binary support, overlap and weights for the tetrad lift.
Coordinate identities relate addition to overlap, establishing the doubly-even
addition criterion and the weights of the lift maps.

Source: `Atlas/Codes/BinaryWeight.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

noncomputable def support {ι : Type*} [Fintype ι] (w : ι → Bit) : Finset ι :=
  Finset.univ.filter (fun i => w i ≠ 0)

noncomputable def overlap {ι : Type*} [Fintype ι] (u v : ι → Bit) : ℕ :=
  (Finset.univ.filter (fun i => u i ≠ 0 ∧ v i ≠ 0)).card

theorem overlap_eq_sum {ι : Type*} [Fintype ι] (u v : ι → Bit) :
    overlap u v = ∑ i, if u i ≠ 0 ∧ v i ≠ 0 then 1 else 0 := by
  classical
  simp only [overlap, Finset.card_filter]

theorem overlap_inter {ι : Type*} [Fintype ι] [DecidableEq ι] (u v : ι → Bit) :
    overlap u v = (support u ∩ support v).card := by
  simp only [overlap, support, ← Finset.filter_and]

theorem binaryDot_overlap {ι : Type*} [Fintype ι] (u v : ι → Bit) :
    binaryDot u v = (overlap u v : Bit) := by
  classical
  rw [overlap_eq_sum, binaryDot_apply, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : ∀ x y : Bit, x * y = ((if x ≠ 0 ∧ y ≠ 0 then 1 else 0 : ℕ) : Bit) := by decide
  exact h _ _

theorem binary_weight_add {ι : Type*} [Fintype ι] (u v : ι → Bit) :
    hammingNorm (u + v) + 2 * overlap u v = hammingNorm u + hammingNorm v := by
  classical
  have he : ∀ x y : Bit,
      (if x + y = 0 then 0 else 1 : ℕ) + 2 * (if x ≠ 0 ∧ y ≠ 0 then 1 else 0) =
        (if x = 0 then 0 else 1) + (if y = 0 then 0 else 1) := by decide
  have hs := congrArg (fun f : ι → ℕ => ∑ i, f i) (funext (fun i => he (u i) (v i)))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← hammingNorm_eq_sum,
    ← overlap_eq_sum] at hs
  exact hs

theorem doublyEven_add {ι : Type*} [Fintype ι] (u v : ι → Bit)
    (hu : 4 ∣ hammingNorm u) (hv : 4 ∣ hammingNorm v) (ho : binaryDot u v = 0) :
    4 ∣ hammingNorm (u + v) := by
  have he := binary_weight_add u v
  rw [binaryDot_overlap, ZMod.natCast_eq_zero_iff_even] at ho
  obtain ⟨a,ha⟩ := hu
  obtain ⟨b,hb⟩ := hv
  obtain ⟨c,hc⟩ := ho
  omega

theorem j_weight : ∀ u : K, hammingNorm (j u) = if u = 0 then 0 else 2 := by decide

theorem jWord_weight (h : HexWord) : hammingNorm (jWord h) = 2 * hammingNorm h := by
  rw [hammingNorm_prod, hammingNorm_eq_sum h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change hammingNorm (j (h i)) = _
  rw [j_weight]
  split_ifs <;> rfl

theorem rho_weight (r : Fin 6 → Bit) : hammingNorm (rho r) = 4 * hammingNorm r := by
  rw [hammingNorm_prod]
  have he : ∀ x : Bit, hammingNorm (fun _ : Fin 4 => x) = 4 * (if x = 0 then 0 else 1) := by decide
  simp only [rho, LinearMap.coe_mk, AddHom.coe_mk, he, ← Finset.mul_sum]
  rw [Equiv.sum_comp hexIndexEquiv (fun i : Fin 6 => if r i = 0 then 0 else 1)]
  rw [← hammingNorm_eq_sum]

end Atlas.Codes
