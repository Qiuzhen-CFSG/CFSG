/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Combinatorics/FiniteImageCapacity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite image capacity

Fiber cardinalities bound a finite image; equality forces each allowed fiber to reach its capacity.

Source: Gerald Höhn, ATLAS, `Atlas/Combinatorics/FiniteImageCapacity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.Combinatorics
open scoped BigOperators

/-- The cardinal of an actual fiber agrees with its finite filter. -/
theorem fiber_card_filter {A B : Type*} [Fintype A] [DecidableEq B] (f : A → B) (b : B) :
    Nat.card {a : A // f a=b} = (Finset.univ.filter (fun a => f a=b)).card := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_subtype _

/-- A uniform fiber capacity bounds the cardinality through the actual image. -/
theorem card_le_capacity_mul_image {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (n : ℕ) (hb : ∀ b, Nat.card {a : A // f a=b} ≤ n) :
    Nat.card A ≤ n*(Finset.univ.image f).card := by
  classical
  have h := Finset.card_le_mul_card_image (f := f) Finset.univ n
    (fun b _ => by rw [← fiber_card_filter]; exact hb b)
  simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using h

/-- Saturating a uniform image capacity forces equality in every occupied fiber. -/
theorem fiber_eq_capacity_of_saturation {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (n : ℕ) (hb : ∀ b, Nat.card {a : A // f a=b} ≤ n)
    (ht : Nat.card A = n*(Finset.univ.image f).card)
    (b : B) (hmem : b ∈ Finset.univ.image f) : Nat.card {a : A // f a=b} = n := by
  classical
  have hs : (∑ c ∈ Finset.univ.image f, Nat.card {a : A // f a=c}) =
      ∑ _c ∈ Finset.univ.image f, n := by
    simp_rw [fiber_card_filter]
    rw [← Finset.card_eq_sum_card_image]
    simp only [Finset.card_univ, Finset.sum_const, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    simpa only [mul_comm, Nat.cast_id] using ht
  exact (Finset.sum_eq_sum_iff_of_le (fun c _ => hb c)).mp hs b hmem

end Atlas.Combinatorics
