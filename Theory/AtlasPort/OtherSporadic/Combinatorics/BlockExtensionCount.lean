/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Combinatorics/BlockExtensionCount.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

/-!
# One-point block extension counts

Double-count pairs of a containing block and a point outside a
prescribed subset to relate two consecutive replication numbers.

Source: Gerald Höhn, ATLAS, `Atlas/Combinatorics/BlockExtensionCount.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for the source computational interfaces.
-/

@[expose] public section

noncomputable section
namespace Atlas.Combinatorics
open scoped BigOperators

/-- Double-count the one-point extensions of a prescribed subset in uniform blocks. -/
theorem block_extension_count {V : Type*} [Fintype V] [DecidableEq V]
    (blocks : Finset (Finset V)) (k l : ℕ) (T : Finset V)
    (hs : ∀ B ∈ blocks, B.card = k)
    (he : ∀ x ∉ T, (blocks.filter (fun B => insert x T ⊆ B)).card = l) :
    (blocks.filter (fun B => T ⊆ B)).card * (k - T.card) =
      (Fintype.card V - T.card) * l := by
  classical
  let S := blocks.filter (fun B => T ⊆ B)
  let D := Finset.univ \ T
  have hd : D.card = Fintype.card V - T.card := by simp [D,Finset.card_sdiff]
  have hc (B : Finset V) (hB : B ∈ S) : (B ∩ D).card = k - T.card := by
    obtain ⟨hB,hTB⟩ := Finset.mem_filter.mp hB
    have hh : B ∩ D = B \ T := by ext x; simp [D]
    rw [hh,Finset.card_sdiff_of_subset hTB,hs B hB]
  have hj (x : V) (hx : x ∈ D) : (S.filter (fun B => x ∈ B)).card = l := by
    have hh : S.filter (fun B => x ∈ B) =
        blocks.filter (fun B => insert x T ⊆ B) := by
      ext B
      simp only [S,Finset.mem_filter,Finset.insert_subset_iff]
      tauto
    rw [hh]
    exact he x (Finset.mem_sdiff.mp hx).2
  have hi : (∑ B ∈ S, (B ∩ D).card) = D.card * l := by
    have hh (B : Finset V) : (B ∩ D).card = ∑ x ∈ D, if x ∈ B then 1 else 0 := by
      rw [← Finset.card_filter,Finset.filter_mem_eq_inter,Finset.inter_comm]
    simp_rw [hh]
    rw [Finset.sum_comm]
    have hsum (x : V) (hx : x ∈ D) : (∑ B ∈ S, if x ∈ B then 1 else 0) = l := by
      rw [← Finset.card_filter]
      exact hj x hx
    rw [Finset.sum_congr rfl hsum]
    simp
  rw [Finset.sum_congr rfl hc] at hi
  simpa only [Finset.sum_const,smul_eq_mul,hd] using hi

end Atlas.Combinatorics
