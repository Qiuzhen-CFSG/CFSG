module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Representatives
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.CoreWitness
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Reduction

/-!
# The max3 six-point set in the literal Held action

The two local generators preserve the displayed six vertices. Hence the literal
max3 subgroup lies in their actual setwise stabilizer in Held. The reverse
inclusion is a separate finite geometric obligation; neither maximality nor an
order label is used to identify the stabilizer here.

Sources: ATLAS HeG1-p2058B0 and HeG1-max3W1; GLS3 Table 5.3p.
The vertex set was found by taking the smallest max3 orbit in GAP. Its invariance
is checked below on the actual Lean permutations, using zero-based vertices.
-/

public section
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
open Subgroup
open scoped Pointwise

/-- The six vertices of the max3 local action inside the degree-2058 carrier. -/
@[expose] def sextet : Finset (Fin 2058) := {480, 557, 719, 892, 1016, 1444}
/-- The actual setwise stabilizer in the full permutation group. -/
@[expose] def sextetPermutationStabilizer : Subgroup (Equiv.Perm (Fin 2058)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 2058)) (sextet : Set (Fin 2058))
/-- Its inverse image under Held's faithful permutation representation. -/
@[expose] def sextetStabilizer : Subgroup He :=
  sextetPermutationStabilizer.comap representation

theorem mem_sextetPermutationStabilizer_of_image (σ : Equiv.Perm (Fin 2058))
    (h : sextet.image σ = sextet) : σ ∈ sextetPermutationStabilizer := by
  change σ '' (sextet : Set (Fin 2058)) = (sextet : Set (Fin 2058))
  rw [← Finset.coe_image, h]

theorem a_mem_sextetStabilizer : a ∈ sextetStabilizer := by
  apply mem_sextetPermutationStabilizer_of_image
  decide +kernel

set_option maxRecDepth 4096 in
theorem localWord_mem_sextetStabilizer : localWord false ∈ sextetStabilizer := by
  apply mem_sextetPermutationStabilizer_of_image
  decide +kernel

/-- The direct inclusion follows from the two checked generator actions. -/
theorem localOvergroup_le_sextetStabilizer : localOvergroup false ≤ sextetStabilizer := by
  apply (closure_le _).mpr
  rintro g (rfl | rfl)
  · exact a_mem_sextetStabilizer
  · exact localWord_mem_sextetStabilizer

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
