module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Data

/-!
# From certified max2 edges to the labelled conjugacy cover

Induction over the checked earlier-parent relation propagates conjugacy from
each root to every node. A separate exclusion certificate must put every
square-one coordinate in a published list. Together these give the labelled
source forest needed by the local census, with all conjugators in the literal
source subgroup.

The equality helper explicitly checks the quotient image before invoking
first-row faithfulness. None of the edge or exclusion equations is assumed
implicitly. Source motivation: Aschbacher--Smith, refs/quasithin.pdf, printed
pp.64--65, A.6.1--4; concrete witness provenance is in
FiberCensus/source/README.md.
-/

set_option backward.isDefEq.respectTransparency true

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus
namespace Forest
open Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound

/-- A proposed edge is an equality in the literal source subgroup. -/
def Edge (k : Fin 11) (n : ℕ) : Prop :=
  (actorAt k n)⁻¹ * sourceElement (fiberIndex k) (maskAt k (parentAt k n)) *
      actorAt k n = sourceElement (fiberIndex k) (maskAt k n)

/-- Array positions and the published membership condition are equivalent. -/
theorem mem_masks_iff (k : Fin 11) (m : Fin 8192) :
    m ∈ masks k ↔ ∃ n : Fin (fiberBound k), maskAt k n.val = m := by
  rw [← nodes_masks k]
  constructor
  · intro hm
    obtain ⟨e, he, hm⟩ := List.mem_map.mp hm
    obtain ⟨n, hn, heq⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp he)
    refine ⟨⟨n, by simpa only [nodes_size] using hn⟩, ?_⟩
    simpa only [maskAt, Array.getElem?_eq_getElem hn, Option.getD_some, heq] using hm
  · rintro ⟨n, rfl⟩
    have hn : n.val < (nodes k).size := by simpa only [nodes_size] using n.isLt
    apply List.mem_map.mpr
    refine ⟨(nodes k)[n.val], Array.getElem_mem_toList hn, ?_⟩
    simp only [maskAt, Array.getElem?_eq_getElem hn, Option.getD_some]

/-- Only the prescribed lift survives in the actual row quotient. -/
theorem quotientMap_sourceElement (j : Fin 4) (m : Fin 8192) :
    quotientMap (sourceElement j m) = quotientMap (sourceLift j) := by
  rw [sourceElement, map_mul,
    map_kernelProduct_eq_one quotientMap quotientMap_seed m, one_mul]

/-- Quotient centralization and a row identity safely certify an edge. -/
theorem edge_of_quotient_commute_of_firstRow (hH : Nat.card H ≤ 21799895040)
    (k : Fin 11) (n : ℕ)
    (hq : Commute (quotientMap (sourceLift (fiberIndex k))) (quotientMap (actorAt k n)))
    (hr : KernelRows.firstRow
      ((actorAt k n)⁻¹ * sourceElement (fiberIndex k) (maskAt k (parentAt k n)) *
        actorAt k n) = KernelRows.firstRow (sourceElement (fiberIndex k) (maskAt k n))) :
    Edge k n := by
  apply KernelRows.eq_of_quotient_eq_of_firstRow hH
  · rw [map_mul, map_mul, map_inv, quotientMap_sourceElement, quotientMap_sourceElement,
      mul_assoc, hq.eq, inv_mul_cancel_left]
  · exact hr

/-- In fiber zero every actor automatically centralizes the quotient image. -/
theorem quotient_commute_of_fiber_zero (k : Fin 11) (n : ℕ) (hk : fiberIndex k = 0) :
    Commute (quotientMap (sourceLift (fiberIndex k))) (quotientMap (actorAt k n)) := by
  rw [hk]
  change Commute (quotientMap 1) _
  rw [map_one]
  exact Commute.one_left _

/-- Earlier parents make all listed nodes conjugate to their actual root. -/
theorem node_isConj_of_edges
    (he : ∀ (k : Fin 11) (n : Fin (fiberBound k)), n.val ≠ 0 → Edge k n.val)
    (k : Fin 11) (n : ℕ) (hn : n < fiberBound k) :
    IsConj (sourceRepresentative k) (sourceElement (fiberIndex k) (maskAt k n)) := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hz : n = 0
    · subst n
      rw [root_mask]
      exact IsConj.refl _
    · have hp := parent_lt k ⟨n, hn⟩ hz
      apply (ih (parentAt k n) hp (lt_trans hp hn)).trans
      apply isConj_iff.mpr
      refine ⟨(actorAt k n)⁻¹, ?_⟩
      simpa only [Edge, inv_inv] using he k ⟨n, hn⟩ hz

/-- The induction applies to the original public list, not a replacement label. -/
theorem listed_isConj_of_edges
    (he : ∀ (k : Fin 11) (n : Fin (fiberBound k)), n.val ≠ 0 → Edge k n.val)
    (k : Fin 11) (m : Fin 8192) (hm : m ∈ masks k) :
    IsConj (sourceRepresentative k) (sourceElement (fiberIndex k) m) := by
  obtain ⟨n, rfl⟩ := (mem_masks_iff k m).mp hm
  exact node_isConj_of_edges he k n.val n.isLt

end Forest

/-- Final assembly from independent edge equalities and square-one exclusion.
The two premises remain to be certified for the concrete matrices. -/
theorem source_forest_of_edges_and_coverage
    (he : ∀ (k : Fin 11) (n : Fin (fiberBound k)), n.val ≠ 0 → Forest.Edge k n.val)
    (hc : ∀ (j : Fin 4) (m : Fin 8192), (sourceElement j m) ^ 2 = 1 →
      ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k)
    (j : Fin 4) (m : Fin 8192) (hs : (sourceElement j m) ^ 2 = 1) :
    ∃ k : Fin 11, fiberIndex k = j ∧ m ∈ masks k ∧
      IsConj (sourceRepresentative k) (sourceElement j m) := by
  obtain ⟨k, hk, hm⟩ := hc j m hs
  refine ⟨k, hk, hm, ?_⟩
  rw [← hk]
  exact Forest.listed_isConj_of_edges he k m hm

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus
