/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.Alphabets
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Finite.Basic

/-!
The three-letter seed code, with its encoder, basis and eight words.
An explicit inverse proves the dimension, while coordinate quadratic identities
and half dimension prove self-duality.

Source: `Atlas/Codes/Trio.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators
abbrev TrioIndex := Fin 3
abbrev TrioWord := TrioIndex → L

def trioEncoder : (Fin 3 → Bit) →ₗ[Bit] TrioWord where
  toFun t := ![(t 1 + t 2, t 0), (t 0 + t 2, t 1), (t 0 + t 1, t 2)]
  map_add' := by intros; ext i <;> fin_cases i <;> simp <;> ring
  map_smul' := by intros; ext i <;> fin_cases i <;> simp [mul_add]

def trio : Submodule Bit TrioWord := trioEncoder.range

theorem trioEncoder_injective : Function.Injective trioEncoder := by
  intro t u h
  funext i
  have hi := congrArg (fun w : TrioWord => (w i).2) h
  fin_cases i <;> simpa [trioEncoder] using hi

noncomputable def trioEquiv : (Fin 3 → Bit) ≃ₗ[Bit] trio :=
  LinearEquiv.ofInjective trioEncoder trioEncoder_injective

def trioGenerators : Fin 3 → TrioWord := ![![spin, oneL, oneL], ![oneL, spin, oneL], ![oneL, oneL, spin]]

theorem trioEncoder_eq_sum (t : Fin 3 → Bit) :
    trioEncoder t = ∑ i, t i • trioGenerators i := by
  ext i <;> fin_cases i <;> simp [trioEncoder, trioGenerators, spin, oneL, Fin.sum_univ_succ]

theorem trio_generators_independent : LinearIndependent Bit trioGenerators := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  intro t u h
  apply trioEncoder_injective
  simpa only [trioEncoder_eq_sum, Fintype.linearCombination_apply] using h

theorem trio_span : Submodule.span Bit (Set.range trioGenerators) = trio := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    rw [trioEncoder_eq_sum]
    simp
  · rintro _ ⟨t, rfl⟩
    rw [trioEncoder_eq_sum]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

def trioWords : Finset TrioWord :=
  {0, ![spin, oneL, oneL], ![oneL, spin, oneL], ![oneL, oneL, spin],
    ![0, cospin, cospin], ![cospin, 0, cospin], ![cospin, cospin, 0], ![spin, spin, spin]}

theorem trio_words (w : TrioWord) : w ∈ trio ↔ w ∈ trioWords := by
  change (∃ t, trioEncoder t = w) ↔ _
  revert w
  decide

theorem trio_finrank : Module.finrank Bit trio = 3 := by
  rw [← trioEquiv.finrank_eq]
  simp

theorem trio_card : Nat.card trio = 8 := by
  rw [← Nat.card_congr trioEquiv.toEquiv]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

theorem trio_isotropic (w : TrioWord) (hw : w ∈ trio) : wordQ qL w = 0 := by
  obtain ⟨t, rfl⟩ := hw
  have h : ∀ t : Fin 3 → Bit, wordQ qL (trioEncoder t) = 0 := by decide
  exact h t

theorem trio_selfDual : trio = dual trio := by
  apply selfDual_of_half_dimension wordPolar wordPolar_nondegenerate
  · intro w hw u hu
    have h := wordQ_polar qL qL_polar u w
    rw [trio_isotropic _ (trio.add_mem hu hw), trio_isotropic _ hu, trio_isotropic _ hw] at h
    simpa using h.symm
  · rw [trio_finrank]
    simp [Letter, Module.finrank_pi_fintype, Module.finrank_prod]

def trioEuclideanWeight (w : TrioWord) : ℕ := ∑ i, euclideanWeight (w i)

theorem trio_hamming_counts (k : ℕ) :
    (trioWords.filter (fun w => hammingNorm w = k)).card =
      if k = 0 then 1 else if k = 2 then 3 else if k = 3 then 4 else 0 := by
  have h : ∀ w ∈ trioWords, hammingNorm w ≤ 3 := fun w _ => hammingNorm_le_card_fintype
  by_cases hk : k ≤ 3
  · interval_cases k <;> decide
  · have he : trioWords.filter (fun w => hammingNorm w = k) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw he
      have := h w hw
      omega
    rw [he]
    simp only [Finset.card_empty]
    split_ifs <;> omega

theorem trio_euclidean_counts (k : ℕ) :
    (trioWords.filter (fun w => trioEuclideanWeight w = k)).card =
      if k = 0 then 1 else if k = 4 then 6 else if k = 6 then 1 else 0 := by
  have h : ∀ w ∈ trioWords, trioEuclideanWeight w ≤ 6 := by decide
  by_cases hk : k ≤ 6
  · interval_cases k <;> decide
  · have he : trioWords.filter (fun w => trioEuclideanWeight w = k) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw he
      have := h w hw
      omega
    rw [he]
    simp only [Finset.card_empty]
    split_ifs <;> omega
end Atlas.Codes
