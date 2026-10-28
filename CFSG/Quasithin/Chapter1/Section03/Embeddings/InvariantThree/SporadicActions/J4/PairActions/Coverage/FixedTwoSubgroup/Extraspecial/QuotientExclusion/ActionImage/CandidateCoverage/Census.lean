module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.CandidateCoverage.WordGeneration
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.CandidateCoverage.Data
public import Theory.GroupTheory.PGroup.NormalIndexTwoStep

/-!
# Descent through the full J₄ normal-subgroup family

Every nontrivial quotient of a finite two-group has a normal subgroup of
order two. Lift that subgroup to advance from a normal subgroup K to a normal
overgroup V with [V:K] = 2, and induct on [T:K]. Thus a family containing T
and closed under the relevant normal index-two steps contains every normal
subgroup of T of index at most 32. The normality is intrinsic to T.

The row comparisons and the starting row are proved here. The normal-step
closure and the 595 Frattini bounds remain explicit obligations. Small Frattini
rank is not a descent condition and discards no intermediate rows.

Source: `Subgroup.exists_normal_index_two_step`; the concrete words are from
`Candidates.Words`, in the context of Aschbacher–Smith printed p.511/PDF p.528.
-/

@[expose] public section
set_option maxRecDepth 10000

open Subgroup Janko4.OuterReduction.OddIndex
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ActionImageCandidates.Coverage

noncomputable def node (i : Fin 788) : Subgroup twoSubgroup :=
  Subgroup.closure (product '' {m | m ∈ censusMasks i})

noncomputable def ambientNode (i : Fin 788) : Subgroup Janko4.Model :=
  (node i).map twoSubgroup.subtype

theorem ambientNode_le (i : Fin 788) : ambientNode i ≤ twoSubgroup := map_subtype_le _

set_option maxHeartbeats 0 in
theorem candidate_masks : ∀ i : Fin 193,
    censusMasks (candidateRow i) = generatorMasks i := by decide +kernel

theorem candidate_node (i : Fin 193) : ambientNode (candidateRow i) = candidate i := by
  simp only [ambientNode, node, candidate_masks, candidate]

set_option maxHeartbeats 0 in
theorem rowClass_spec : ∀ i : Fin 788,
    (rowClass i).elim smallRow candidateRow = i := by decide +kernel

theorem node_zero : node 0 = ⊤ := by
  have he : censusMasks 0 = (List.finRange 21).map (fun i => 2 ^ i.val) := by decide +kernel
  have hr : product '' {m | m ∈ censusMasks 0} = Set.range generator := by
    rw [he]
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
      exact ⟨i, (product_singleton i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨2 ^ i.val, List.mem_map.mpr ⟨i, by simp, rfl⟩, product_singleton i⟩
  change Subgroup.closure _ = _
  rw [hr, closure_generator]

/-- All normal index-two steps which can occur within the bounded-index descent. -/
def NormalSteps : Prop :=
  ∀ i : Fin 788, (node i).Normal →
    ∀ K : Subgroup twoSubgroup, K.Normal → K ≤ node i →
      K.relIndex (node i) = 2 → K.index ≤ 32 → ∃ j : Fin 788, node j = K

/-- The rows outside the existing candidate list require actual Frattini bounds. -/
def SmallRows : Prop :=
  ∀ j : Fin 595, Nat.card (ambientNode (smallRow j) ⧸ frattini (ambientNode (smallRow j))) ≤ 32

/-- A normal subgroup of bounded index is reached by normal steps from the top. -/
theorem normal_coverage_of_steps (hstep : NormalSteps)
    (K : Subgroup twoSubgroup) (hK : K.Normal) (hindex : K.index ≤ 32) :
    ∃ i : Fin 788, node i = K := by
  generalize hn : K.index = n at *
  induction n using Nat.strong_induction_on generalizing K with
  | h n ih =>
    by_cases ht : K = ⊤
    · exact ⟨0, node_zero.trans ht.symm⟩
    let : K.Normal := hK
    obtain ⟨V, hVn, hKV, _, hrel⟩ :=
      exists_normal_index_two_step twoSubgroup twoSubgroup_isPGroup K ⊤
        (lt_top_iff_ne_top.mpr ht)
    have hm := relIndex_mul_index hKV
    rw [hrel, hn] at hm
    have hp : V.index ≠ 0 := V.index_ne_zero_of_finite
    have hlt : V.index < n := by omega
    obtain ⟨i, hi⟩ := ih V.index hlt V hVn rfl (by omega)
    subst V
    exact hstep i hVn K hK hKV hrel (by omega)

/-- Move the intrinsic normal-subgroup census back to the exact ambient carrier. -/
theorem ambient_coverage_of_steps (hstep : NormalSteps)
    (K : Subgroup Janko4.Model) (hKT : K ≤ twoSubgroup)
    (hKN : twoSubgroup ≤ normalizer (K : Set Janko4.Model))
    (hindex : K.relIndex twoSubgroup ≤ 32) :
    ∃ i : Fin 788, ambientNode i = K := by
  obtain ⟨i, hi⟩ := normal_coverage_of_steps hstep (K.subgroupOf twoSubgroup)
    ((normal_subgroupOf_iff_le_normalizer hKT).mpr hKN) hindex
  refine ⟨i, ?_⟩
  rw [ambientNode, hi, map_subgroupOf_eq_of_le hKT]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ActionImageCandidates.Coverage
