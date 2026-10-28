/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.BinaryCounting

/-!
Weight counts in odd Golay slices with fixed hexacode word.
An explicit mask translates parity parameters into odd words and converts
binary weight counts into the three possible Golay weights.

Source: `Atlas/Codes/GolayOddCounting.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

def oddMask (h : HexWord) (i : Fin 6) : Bit :=
  qK (h (hexIndexEquiv.symm i)) + if i = 5 then 1 else 0

theorem oddMask_parity (h : hexacode) : ∑ i, oddMask h.val i = 1 := by
  simp only [oddMask, Finset.sum_add_distrib]
  rw [Equiv.sum_comp hexIndexEquiv.symm (fun i : HexIndex => qK (h.val i))]
  change wordQ qK h.val + _ = 1
  rw [hexacode_isotropic h.val h.prop]
  simp

theorem odd_block_weight : ∀ (i : HexIndex) (u : K) (r : Bit),
    hammingNorm (j u + (fun _ => r) + fun k => eta (i,k)) =
      1 + 2 * (if r + qK u + (if hexIndexEquiv i = 5 then 1 else 0) = 0 then 0 else 1) := by
  decide

theorem odd_word_weight (h : hexacode) (r : P6) :
    hammingNorm (c0Encoder (h,r) + eta) = 6 + 2 * hammingNorm (r.val + oddMask h.val) := by
  rw [hammingNorm_prod]
  have he (i : HexIndex) :
      hammingNorm (fun k => (c0Encoder (h,r) + eta) (i,k)) =
        1 + 2 * (if (r.val + oddMask h.val) (hexIndexEquiv i) = 0 then 0 else 1) := by
    have ht := odd_block_weight i (h.val i) (r.val (hexIndexEquiv i))
    simp only [c0Encoder, jWord, rho, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.add_apply, oddMask, Equiv.symm_apply_apply, add_assoc] at ht ⊢
    exact ht
  simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one, ← Finset.mul_sum]
  rw [Equiv.sum_comp hexIndexEquiv
    (fun i : Fin 6 => if (r.val + oddMask h.val) i = 0 then 0 else 1)]
  rw [← hammingNorm_eq_sum]
  rfl

noncomputable def oddWordEquiv (h : hexacode) : P6 ≃ {s : Fin 6 → Bit // ∑ i, s i = 1} :=
  oddParityTranslation 5 (oddMask h.val) (oddMask_parity h)

theorem odd_word_count (h : hexacode) (m : ℕ) :
    Nat.card {r : P6 // hammingNorm (c0Encoder (h,r) + eta) = 6 + 2*m} =
      if (m : Bit) = 1 then (6 : ℕ).choose m else 0 := by
  let e : {r : P6 // hammingNorm (c0Encoder (h,r) + eta) = 6 + 2*m} ≃
      {s : {s : Fin 6 → Bit // ∑ i, s i = 1} // hammingNorm s.val = m} :=
    Equiv.subtypeEquiv (oddWordEquiv h) (by
      intro r
      rw [odd_word_weight]
      change 6 + 2 * hammingNorm (r.val + oddMask h.val) = 6 + 2*m ↔
        hammingNorm (r.val + oddMask h.val) = m
      omega)
  rw [Nat.card_congr e, odd_parity_weight_count]

theorem odd_word_counts (h : hexacode) :
    Nat.card {r : P6 // hammingNorm (c0Encoder (h,r) + eta) = 8} = 6 ∧
    Nat.card {r : P6 // hammingNorm (c0Encoder (h,r) + eta) = 12} = 20 ∧
    Nat.card {r : P6 // hammingNorm (c0Encoder (h,r) + eta) = 16} = 6 := by
  have h1 := odd_word_count h 1
  have h3 := odd_word_count h 3
  have h5 := odd_word_count h 5
  norm_num at h1 h3 h5
  exact ⟨h1,h3,h5⟩
end Atlas.Codes
