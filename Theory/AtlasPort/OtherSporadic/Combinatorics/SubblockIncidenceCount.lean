/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Combinatorics/SubblockIncidenceCount.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

/-!
# Subblock incidence moments

Count pairs of a selected block and a marked k-subset in both orders.
Constant replication then evaluates the binomial intersection moment.

Source: Gerald Höhn, ATLAS, `Atlas/Combinatorics/SubblockIncidenceCount.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for the source computational interfaces.
-/

@[expose] public section

noncomputable section
namespace Atlas.Combinatorics
open scoped BigOperators

/-- Count incidences of selected blocks with k-subsets of a fixed marked set. -/
theorem subblock_incidence_sum {V : Type*} [DecidableEq V]
    (blocks : Finset (Finset V)) (O : Finset V) (k : ℕ) :
    (∑ B ∈ blocks, (B ∩ O).card.choose k) =
      ∑ U ∈ O.powersetCard k, (blocks.filter (fun B => U ⊆ B)).card := by
  classical
  have he (B : Finset V) : (B ∩ O).powersetCard k =
      (O.powersetCard k).filter (fun U => U ⊆ B) := by
    ext U
    simp only [Finset.mem_powersetCard,Finset.mem_filter,Finset.subset_inter_iff]
    tauto
  have hc (B : Finset V) : (B ∩ O).card.choose k =
      ∑ U ∈ O.powersetCard k, if U ⊆ B then 1 else 0 := by
    rw [← Finset.card_powersetCard,he,Finset.card_filter]
  simp_rw [hc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U _
  rw [Finset.card_filter]

/-- Constant replication turns the incidence identity into a numerical moment. -/
theorem subblock_incidence_count {V : Type*} [DecidableEq V]
    (blocks : Finset (Finset V)) (O : Finset V) (k l : ℕ)
    (h : ∀ U ∈ O.powersetCard k, (blocks.filter (fun B => U ⊆ B)).card = l) :
    (∑ B ∈ blocks, (B ∩ O).card.choose k) = O.card.choose k * l := by
  rw [subblock_incidence_sum,Finset.sum_congr rfl h]
  simp

end Atlas.Combinatorics
