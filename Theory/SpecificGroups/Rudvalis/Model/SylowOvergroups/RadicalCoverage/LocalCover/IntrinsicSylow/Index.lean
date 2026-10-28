module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.Comparison
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.CosetSteps
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.CosetSeparation
import Mathlib.Tactic.FinCases

/-!
# The fixed word subgroup has index twenty-one inside max4

The signed-generator transition identities cover max4 by 21 right cosets of
localP. An eight-point orbit of localP separates those cosets in the original
faithful degree-4060 action. Thus the intrinsic index is exactly 21, without
using any order calculation for max4 or the ambient Rudvalis model.

The preserved ATLAS words and their attribution are in
`SylowOvergroups.Definitions`; finite witnesses are retained in `source/`.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow

private def generator (i : Fin 2) : max4 :=
  ⟨mainLetter (i.castAdd 2), mainLetter_mem _⟩

private theorem generator_closure : Subgroup.closure (Set.range generator) = ⊤ := by
  have hle : max4 ≤ (Subgroup.closure (Set.range generator)).map max4.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ (rfl | h)
    · exact ⟨generator 0, Subgroup.subset_closure ⟨0, rfl⟩, rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp h
      exact ⟨generator 1, Subgroup.subset_closure ⟨1, rfl⟩, rfl⟩
  apply top_le_iff.mp
  intro x _
  obtain ⟨y, hy, hxy⟩ := hle x.property
  exact (Subtype.ext hxy : y = x) ▸ hy

private def representative (r : Fin 21) : max4 :=
  ⟨mainWord (Cosets.repWord r), mainWord_mem _⟩

private def factorElement (i : Fin 4) (r : Fin 21) : localP.subgroupOf max4 :=
  ⟨⟨localWord (Cosets.factor i r), localP_le_max4 (localWord_mem _)⟩, localWord_mem _⟩

private theorem transition (i : Fin 4) (r : Fin 21) :
    representative r * ⟨mainLetter i, mainLetter_mem i⟩ =
      (factorElement i r : max4) * representative (Cosets.act i r) := by
  apply Subtype.ext
  apply Subtype.ext
  change permutation (mainWord (Cosets.repWord r) * mainLetter i) =
    permutation (localWord (Cosets.factor i r) * mainWord (Cosets.repWord (Cosets.act i r)))
  rw [map_mul, map_mul, mainWord_perm, mainLetter_perm, localWord_perm, mainWord_perm]
  exact Cosets.step i r

private def cover : Subgroup.GeneratorCosetCover
    (localP.subgroupOf max4) generator (Fin 21) where
  repr := representative
  initial := 0
  initial_eq := by apply Subtype.ext; rfl
  step r i := ⟨factorElement (i.castAdd 2) r, Cosets.act (i.castAdd 2) r,
    transition (i.castAdd 2) r⟩
  inv_step r i := by
    refine ⟨factorElement (Fin.natAdd 2 i) r, Cosets.act (Fin.natAdd 2 i) r, ?_⟩
    have hi : (generator i)⁻¹ = ⟨mainLetter (Fin.natAdd 2 i), mainLetter_mem _⟩ := by
      fin_cases i <;> rfl
    rw [hi]
    exact transition (Fin.natAdd 2 i) r

private theorem separation (i j : Fin 21)
    (h : representative i * (representative j)⁻¹ ∈ localP.subgroupOf max4) : i = j := by
  apply Cosets.separation
  have h' : mainWord (Cosets.repWord i) * (mainWord (Cosets.repWord j))⁻¹ ∈ localP := h
  have hm : permutation (mainWord (Cosets.repWord i) * (mainWord (Cosets.repWord j))⁻¹) ∈
      localP.map permutation := ⟨_, h', rfl⟩
  rw [map_localP, map_mul, map_inv, mainWord_perm, mainWord_perm] at hm
  exact hm

/-- Exact index in max4, not in the ambient Rudvalis model. -/
public theorem localP_intrinsic_index : (localP.subgroupOf max4).index = 21 := by
  apply Nat.le_antisymm
  · simpa using cover.index_le_card generator_closure
  · simpa using Subgroup.card_le_index_of_rightCoset_separation
      (localP.subgroupOf max4) representative separation

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow
