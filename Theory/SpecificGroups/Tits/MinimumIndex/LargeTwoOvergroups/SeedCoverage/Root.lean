module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Nodes

/-!
# The two generators at the root generate the marked Sylow subgroup

Explicit positive words in normal forms 4 and 1860 recover the eight Parrott
Sylow generators. Each equation is checked on the two distinguishing points.
Source: Parrott (1972), §5, p.683, and the saved `source/` witness data.
-/

namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration

set_option maxRecDepth 20000

private def originalIndices : Fin 8 → Fin 2048 := ![1, 2, 4, 16, 32, 128, 256, 1024]
private def rootWords : Fin 8 → List (Fin 2) :=
  ![[0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1],
    [1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1],
    [0],
    [0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0],
    [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1],
    [1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0],
    [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0]]

set_option maxHeartbeats 1600000 in
private theorem root_words (k : Fin 8) :
    evalWord (generator 0 0) (rootWords k) = element (originalIndices k) := by
  have hc : ∀ k : Fin 8,
      ((evalWord (fastGenerator 0 0) (rootWords k)) 0,
        (evalWord (fastGenerator 0 0) (rootWords k)) 930) =
      (perm (originalIndices k) 0, perm (originalIndices k) 930) := by decide +kernel
  have hf : pointHom (evalWord (generator 0 0) (rootWords k)) =
      evalWord (fastGenerator 0 0) (rootWords k) :=
    (pointHom_word (generator 0 0) (rootWords k)).trans
      (congrArg (fun f => evalWord f (rootWords k)) (funext (pointHom_generator 0 0)))
  apply point_pair_ext
  exact (congrArg (fun p : Equiv.Perm (Fin 1600) => (p 0, p 930)) hf).trans
    ((hc k).trans (congrArg (fun p : Equiv.Perm (Fin 1600) => (p 0, p 930))
      (pointHom_element (originalIndices k))).symm)

private theorem original_val :
    (fun k => (element (originalIndices k)).val) =
      ![atlas1600ParrottAssignment .s1, atlas1600ParrottAssignment .s2,
        atlas1600ParrottAssignment .s3, atlas1600ParrottAssignment .s4,
        atlas1600ParrottAssignment .s5, atlas1600ParrottAssignment .s6,
        atlas1600ParrottAssignment .s7, atlas1600ParrottAssignment .s8] := by
  funext k
  fin_cases k <;> simp [element, originalIndices, atlas1600SylowTwoNormalForm_eq]

public theorem root_eq_top : node 0 0 = ⊤ := by
  apply Subgroup.map_injective S.subtype_injective
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply le_antisymm (Subgroup.map_subtype_le _)
  have hmem (k : Fin 8) :
      (element (originalIndices k)).val ∈ (node 0 0).map S.subtype := by
    have hw : evalWord (generator 0 0) (rootWords k) ∈ node 0 0 :=
      evalWord_mem (generator 0 0) (Subgroup.closure (Set.range (generator 0 0)))
        (fun j => Subgroup.subset_closure (Set.mem_range_self j)) _
    exact Subgroup.mem_map_of_mem S.subtype ((root_words k) ▸ hw)
  change atlas1600SylowTwoSubgroup ≤ _
  rw [atlas1600SylowTwoSubgroup_eq, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hm : ∀ k, (![atlas1600ParrottAssignment .s1, atlas1600ParrottAssignment .s2,
        atlas1600ParrottAssignment .s3, atlas1600ParrottAssignment .s4,
        atlas1600ParrottAssignment .s5, atlas1600ParrottAssignment .s6,
        atlas1600ParrottAssignment .s7, atlas1600ParrottAssignment .s8] : Fin 8 → Atlas1600Group) k ∈
      (node 0 0).map S.subtype := by
    rw [← original_val]
    exact hmem
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hm 7
  · exact hm 6
  · exact hm 5
  · exact hm 4
  · exact hm 3
  · exact hm 2
  · exact hm 1
  · exact hm 0

end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
