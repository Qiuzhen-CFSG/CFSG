/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/RankThreePrimitivity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.FiniteSuborbitPrimitivity
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Rank-three suborbits and primitivity

A block containing the base point is a union of stabilizer suborbits.
For three suborbits there are four possible sizes; excluding the two proper
nonsingleton sizes by divisibility proves primitivity.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/RankThreePrimitivity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream calculations.
-/

@[expose] public section

noncomputable section
namespace Atlas.GroupTheory
open MulAction
open scoped BigOperators

/-- There are only four suborbit sums containing a singleton base orbit. -/
theorem rankThree_suborbit_sum_cases (d : Fin 3 → ℕ) (h0 : d 0=1)
    (T : Finset (Fin 3)) (hT : 0 ∈ T) :
    (∑ i ∈ T,d i)=1 ∨ (∑ i ∈ T,d i)=1+d 1 ∨
      (∑ i ∈ T,d i)=1+d 2 ∨ (∑ i ∈ T,d i)=1+d 1+d 2 := by
  classical
  have he : (∑ i ∈ T,d i)=∑ i : Fin 3,if i ∈ T then d i else 0 := by simp
  rw [he,Fin.sum_univ_three]
  by_cases h1 : (1 : Fin 3) ∈ T <;> by_cases h2 : (2 : Fin 3) ∈ T <;>
    simp [hT,h1,h2,h0]

/-- Every block through a point in a three-suborbit action has one of these
four sizes, by the already proved general suborbit partition theorem. -/
theorem block_card_rankThree {G X : Type*} [Group G] [MulAction G X]
    [Finite X] (a : X) (f : X → Fin 3) (ha : f a=0)
    (htrans : ∀ x y, f x=f y → ∃ g : stabilizer G a, g • x=y)
    (d : Fin 3 → ℕ) (h0 : d 0=1)
    (hd : ∀ i, Nat.card {x : X // f x=i}=d i)
    (B : Set X) (haB : a ∈ B) (hB : IsBlock G B) :
    Nat.card B=1 ∨ Nat.card B=1+d 1 ∨ Nat.card B=1+d 2 ∨
      Nat.card B=1+d 1+d 2 := by
  obtain ⟨T,hT,hcard⟩ := block_card_suborbit_sum a f htrans d hd B haB hB
  rw [ha] at hT
  rw [hcard]
  exact rankThree_suborbit_sum_cases d h0 T hT

/-- Exact full suborbits of sizes 1,a,b imply primitivity when the two
proper nonsingleton sums fail the block-size divisibility test. -/
theorem primitive_of_rankThree_nondivisibility {G X : Type*}
    [Group G] [MulAction G X] [Finite X] [IsPretransitive G X]
    (a : X) (f : X → Fin 3) (ha : f a=0)
    (htrans : ∀ x y, f x=f y → ∃ g : stabilizer G a, g • x=y)
    (d : Fin 3 → ℕ) (h0 : d 0=1)
    (hd : ∀ i, Nat.card {x : X // f x=i}=d i)
    (hcard : Nat.card X=1+d 1+d 2)
    (hfirst : ¬(1+d 1) ∣ Nat.card X) (hsecond : ¬(1+d 2) ∣ Nat.card X) :
    IsPreprimitive G X := by
  apply primitive_of_suborbit_sums a f htrans d hd
  intro T hT hdiv
  rw [ha] at hT
  rcases rankThree_suborbit_sum_cases d h0 T hT with h | h | h | h
  · exact Or.inl h
  · exact False.elim (hfirst (h ▸ hdiv))
  · exact False.elim (hsecond (h ▸ hdiv))
  · exact Or.inr (h.trans hcard.symm)

end Atlas.GroupTheory
