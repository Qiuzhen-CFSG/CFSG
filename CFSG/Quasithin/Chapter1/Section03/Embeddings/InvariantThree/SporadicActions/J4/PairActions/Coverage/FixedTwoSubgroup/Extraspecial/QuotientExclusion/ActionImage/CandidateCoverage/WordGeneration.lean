module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.Candidates
import Mathlib.Tactic.Group

/-!
# Generation by the twenty-one candidate words

Recover each of the original fifteen generators by multiplying the newly
introduced words. Cancellation alone proves that all twenty-one words generate
the specified two-subgroup; no matrix relations or GAP presentation are used.
A singleton bit mask evaluates to its designated generator.

Source: the explicit formulas in `Candidates.Words` and the certified
fifteen-generator theorem `OddIndex.twoSubgroup_eq_closure`.
-/

@[expose] public section

open Subgroup Janko4.OuterReduction.OddIndex

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ActionImageCandidates.Coverage

theorem closure_original : Subgroup.closure (Set.range original) = ⊤ := by
  apply Subgroup.map_injective twoSubgroup.subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp]
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact twoSubgroup_eq_closure.symm

theorem closure_generator : Subgroup.closure (Set.range generator) = ⊤ := by
  let H := Subgroup.closure (Set.range generator)
  have hc (i : Fin 21) : generator i ∈ H := Subgroup.subset_closure ⟨i, rfl⟩
  suffices horig : ∀ i, original i ∈ H by
    apply top_unique
    rw [← closure_original]
    exact (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact horig i)
  intro i
  rcases i with i | i
  · fin_cases i
    · exact hc 0
    · exact hc 6
    · have he : original (.inl 2) = generator 0 * generator 3 := by simp [generator]
      exact he.symm ▸ H.mul_mem (hc 0) (hc 3)
    · have he : original (.inl 3) = generator 0 * generator 3 * generator 9 := by simp [generator]
      exact he.symm ▸ H.mul_mem (H.mul_mem (hc 0) (hc 3)) (hc 9)
    · have he : original (.inl 4) = generator 3 * generator 6 * generator 11 := by simp [generator] ; group
      exact he.symm ▸ H.mul_mem (H.mul_mem (hc 3) (hc 6)) (hc 11)
    · have he : original (.inl 5) = generator 0 * generator 9 * generator 11 * generator 14 := by simp [generator]; group
      exact he.symm ▸ H.mul_mem (H.mul_mem (H.mul_mem (hc 0) (hc 9)) (hc 11)) (hc 14)
    · have he : original (.inl 6) = generator 0 * generator 3 * generator 6 * generator 14 * generator 16 := by simp [generator]; group
      exact he.symm ▸ H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hc 0) (hc 3)) (hc 6)) (hc 14)) (hc 16)
    · have he : original (.inl 7) = generator 14 * generator 16 * generator 20 := by simp [generator] ; group
      exact he.symm ▸ H.mul_mem (H.mul_mem (hc 14) (hc 16)) (hc 20)
    · have he : original (.inl 8) = generator 6 * generator 9 * generator 17 := by simp [generator] ; group
      exact he.symm ▸ H.mul_mem (H.mul_mem (hc 6) (hc 9)) (hc 17)
    · have he : original (.inl 9) = generator 0 * generator 14 * generator 17 * generator 18 := by simp [generator] ; group
      exact he.symm ▸ H.mul_mem (H.mul_mem (H.mul_mem (hc 0) (hc 14)) (hc 17)) (hc 18)
    · have he : original (.inl 10) = generator 6 * generator 9 * generator 11 * generator 16 * generator 17 * generator 19 := by simp [generator] ; group
      exact he.symm ▸ H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hc 6) (hc 9)) (hc 11)) (hc 16)) (hc 17)) (hc 19)
  · fin_cases i
    · have he : original (.inr 0) = generator 3 * generator 7 := by simp [generator] ; group
      exact he.symm ▸ H.mul_mem (hc 3) (hc 7)
    · exact hc 1
    · have he : original (.inr 2) = generator 0 * generator 3 * generator 5 := by simp [generator]
      exact he.symm ▸ H.mul_mem (H.mul_mem (hc 0) (hc 3)) (hc 5)
    · exact hc 2

theorem product_singleton (i : Fin 21) : product (2 ^ i.val) = generator i := by
  have hf : (List.finRange 21).filter (fun j => (2 ^ i.val).testBit j.val) = [i] := by
    fin_cases i <;> decide
  simp [product, hf]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ActionImageCandidates.Coverage
