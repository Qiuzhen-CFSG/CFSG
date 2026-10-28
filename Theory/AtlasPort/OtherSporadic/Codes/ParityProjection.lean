/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.BinaryCounting

/-!
Projection fibers of the length-six parity code.
Surjectivity and equal-size fibers count prescribed weights on a coordinate subset.

Source: `Atlas/Codes/ParityProjection.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators
open Finset
noncomputable instance : Fintype P6 := Fintype.ofFinite P6

def parityProjection (e : Fin 2 ↪ Fin 6) : P6 →ₗ[Bit] (Fin 2 → Bit) where
  toFun r i := r.val (e i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem parityProjection_surjective (e : Fin 2 ↪ Fin 6) : Function.Surjective (parityProjection e) := by
  obtain ⟨l,hl0,hl1⟩ := Fin.exists_ne_and_ne_of_two_lt (e 0) (e 1) (by decide)
  have he : e 0 ≠ e 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (e.injective h)
  intro u
  let r : Fin 6 → Bit := Pi.single (e 0) (u 0) + Pi.single (e 1) (u 1) + Pi.single l (u 0 + u 1)
  have hr : r ∈ P6 := by
    apply (parityCode_mem 5 r).mpr
    simp [r, sum_add_distrib]
  refine ⟨⟨r,hr⟩, ?_⟩
  funext i
  fin_cases i <;> simp [parityProjection, r, he, he.symm, hl0.symm, hl1.symm]

theorem parityProjection_fiber (e : Fin 2 ↪ Fin 6) (v : Fin 2 → Bit) :
    #{r : P6 | parityProjection e r = v} = 8 := by
  classical
  have he (u : Fin 2 → Bit) : #{r : P6 | parityProjection e r = u} =
      #{r : P6 | parityProjection e r = v} :=
    AddMonoidHom.card_fiber_eq_of_mem_range (parityProjection e)
      (parityProjection_surjective e u) (parityProjection_surjective e v)
  have h := sum_card_fiberwise_eq_card_filter (univ : Finset P6)
    (univ : Finset (Fin 2 → Bit)) (parityProjection e)
  simp only [he, sum_const, card_univ, smul_eq_mul, mem_univ, filter_true] at h
  have hc : Fintype.card P6 = 32 := by simpa [Nat.card_eq_fintype_card] using parityCode_card 5
  norm_num [Fintype.card_fun, ZMod.card, hc] at h
  omega

theorem parityProjection_weight_count (e : Fin 2 ↪ Fin 6) (k : ℕ) :
    Nat.card {r : P6 // hammingNorm (parityProjection e r) = k} = 8 * (2 : ℕ).choose k := by
  classical
  have hs := sum_card_fiberwise_eq_card_filter (univ : Finset P6)
    (univ.filter (fun u : Fin 2 → Bit => hammingNorm u = k)) (parityProjection e)
  simp only [parityProjection_fiber, sum_const, smul_eq_mul, mem_filter, mem_univ, true_and] at hs
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← hs, mul_comm]
  congr 1
  have h := binary_weight_count 2 k
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using h
end Atlas.Codes
