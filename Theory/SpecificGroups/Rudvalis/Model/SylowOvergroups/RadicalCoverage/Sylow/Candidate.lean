module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions
public import Mathlib.Data.Fin.VecNotation

/-!
# A word-defined candidate for a Rudvalis Sylow two-subgroup

The fourteen generators below are words in the two preserved max4 generators.
Consequently the subgroup they generate lies in max4, on the original
ATLAS degree-4060 carrier. Their ordered binary products give candidate
normal forms; neither uniqueness nor completeness is asserted here.

GAP supplied the words and the prospective collection tables retained in
`source/witnesses.json`; `source/Generate.g` regenerates those untrusted data.
Only the subgroup membership arguments below are certified in this module.
The local order certificate must still prove that the subgroup has order
16384. No GAP order or normalizer output is used as a Lean proof.

Source: the ATLAS `RuG1-max4W1` program preserved in `SylowOvergroups/source/`,
with the permutation sources and inverse point-action convention documented in
`Model.PermutationData`. This local calculation supplies the Sylow containment
used in Aschbacher--Smith, printed p.511 (PDF p.528), citing [Asc86b];
GLS3 Table 5.3r, printed p.279, lists the structure motivating max4.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate

/-- Letters 0,1,2,3 mean x,y,x⁻¹,y⁻¹ for the exact ATLAS max4 words. -/
@[expose] public def candidateLetter (i : Fin 4) : Model :=
  ![max4Generators.1, max4Generators.2, max4Generators.1⁻¹, max4Generators.2⁻¹] i

/-- Fourteen explicit words, with the original multiplication order. -/
@[expose] public def candidateWords : Fin 14 → List (Fin 4) :=
  ![[2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3],
    [2, 3, 2, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 3, 2],
    [2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 2],
    [1, 2, 1, 2, 3, 2, 3, 2, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2],
    [3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 0, 3, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2],
    [2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 3],
    [1, 2, 1, 2, 3, 2, 3, 2, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 3, 2, 3, 3],
    [0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0],
    [1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3],
    [3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0],
    [1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3],
    [1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 3, 2, 3],
    [3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3]]

/-- The candidate generators as elements of the fixed Rudvalis model. -/
@[expose] public def candidateGenerator (i : Fin 14) : Model :=
  ((candidateWords i).map candidateLetter).prod

/-- The concrete subgroup whose local order remains to be certified. -/
@[expose] public def candidate : Subgroup Model :=
  Subgroup.closure (Set.range candidateGenerator)

private theorem candidateLetter_mem (i : Fin 4) : candidateLetter i ∈ max4 := by
  have hx : max4Generators.1 ∈ max4 :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : max4Generators.2 ∈ max4 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rcases i with ⟨i, hi⟩
  have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases he with rfl | rfl | rfl | rfl
  · exact hx
  · exact hy
  · exact max4.inv_mem hx
  · exact max4.inv_mem hy

/-- Every displayed generator is an actual element of max4. -/
public theorem candidateGenerator_mem_max4 (i : Fin 14) : candidateGenerator i ∈ max4 := by
  apply max4.list_prod_mem
  intro g hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
  exact candidateLetter_mem j

/-- The word-defined candidate lies in the exact fourth ATLAS subgroup. -/
public theorem candidate_le_max4 : candidate ≤ max4 := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, rfl⟩
  exact candidateGenerator_mem_max4 i

/-- The 16384 prospective normal forms, with generator 0 on the left. -/
@[expose] public def candidateNormalForm (n : Fin 16384) : Model :=
  (List.ofFn (fun i : Fin 14 => candidateGenerator i ^ (n.val / 2 ^ i.val % 2))).prod

/-- Each prospective normal form lies in the candidate subgroup. -/
public theorem candidateNormalForm_mem (n : Fin 16384) : candidateNormalForm n ∈ candidate := by
  apply candidate.list_prod_mem
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact candidate.pow_mem (Subgroup.subset_closure (Set.mem_range_self i)) _

end Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate
