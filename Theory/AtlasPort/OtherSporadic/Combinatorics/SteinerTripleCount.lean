/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Combinatorics/SteinerTripleCount.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

/-!
# Triple replication in the Witt design

Double-count one-point extensions of a triple in a 4-(23,7,1) design.

Source: Gerald Höhn, ATLAS, `Atlas/Combinatorics/SteinerTripleCount.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies are exposed where the downstream stabilizer constructions use reduction.
-/

@[expose] public section

noncomputable section
namespace Atlas.Combinatorics
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Replication of a three-set in a 4-(23,7,1) system, by counting its
one-point extensions. This uses only the design axioms. -/
theorem steiner_four_triple_count {V : Type*} [Fintype V]
    (blocks : Finset (Finset V)) (hv : Fintype.card V = 23)
    (hs : ∀ B ∈ blocks, B.card = 7)
    (hu : ∀ T : Finset V, T.card = 4 → ∃! B, B ∈ blocks ∧ T ⊆ B)
    (T : Finset V) (hT : T.card = 3) :
    (blocks.filter (fun B => T ⊆ B)).card = 5 := by
  classical
  let S := blocks.filter (fun B => T ⊆ B)
  let D := Finset.univ \ T
  have hd : D.card = 20 := by simp [D,Finset.card_sdiff,hT,hv]
  have hc (B : Finset V) (hB : B ∈ S) : (B ∩ D).card = 4 := by
    obtain ⟨hB,hTB⟩ := Finset.mem_filter.mp hB
    have he : B ∩ D = B \ T := by ext x; simp [D]
    rw [he,Finset.card_sdiff_of_subset hTB,hs B hB,hT]
  have hj (j : V) (hj : j ∈ D) : (S.filter (fun B => j ∈ B)).card = 1 := by
    have hjT : j ∉ T := (Finset.mem_sdiff.mp hj).2
    obtain ⟨B,⟨hB,hTB⟩,huniq⟩ := hu (insert j T) (by rw [Finset.card_insert_of_notMem hjT,hT])
    have he : S.filter (fun C => j ∈ C) = {B} := by
      ext C
      simp only [Finset.mem_filter,Finset.mem_singleton,S]
      constructor
      · rintro ⟨⟨hC,hTC⟩,hjC⟩
        exact huniq C ⟨hC,Finset.insert_subset hjC hTC⟩
      · rintro rfl
        exact ⟨⟨hB,Finset.Subset.trans (Finset.subset_insert _ _) hTB⟩,
          hTB (Finset.mem_insert_self _ _)⟩
    rw [he]; rfl
  have he (B : Finset V) : (B ∩ D).card = ∑ j ∈ D, if j ∈ B then 1 else 0 := by
    rw [← Finset.card_filter,Finset.filter_mem_eq_inter,Finset.inter_comm]
  have hi : (∑ B ∈ S, (B ∩ D).card) = 20 := by
    simp_rw [he]
    rw [Finset.sum_comm]
    have hh (j : V) (hj' : j ∈ D) : (∑ B ∈ S, if j ∈ B then 1 else 0) = 1 := by
      rw [← Finset.card_filter]; exact hj j hj'
    rw [Finset.sum_congr rfl hh]
    simp [hd]
  rw [Finset.sum_congr rfl hc] at hi
  simp only [Finset.sum_const,smul_eq_mul] at hi
  change S.card = 5
  omega

end Atlas.Combinatorics
