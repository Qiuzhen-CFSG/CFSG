module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedSubgroup
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Relators
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Checked
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Shape
public import Theory.GroupTheory.GeneratorCosetCoverIndex

/-!
# Index of the marked subgroup in the concrete Held group

The ATLAS subgroup `M1 = ⟨a, a^(b²), a^(b⁻²)⟩` has index 2058 in the
exact degree-2058 permutation carrier. A checked coset-word certificate supplies
2058 representatives and all signed generator transitions. Word induction gives
a cover and hence the upper index bound; the already checked transitive action
then identifies this subgroup with the stabilizer of point 1205.

The certificate uses the seven source relators, the definitions of the marked
involutions, cyclic rotations, and seventeen further identities checked on all
2058 points. Every deduction is checked by the Lean kernel. Neither a group
order calculation nor injectivity of a presentation map is used.

Source: John Bray's ATLAS `Model/Source/HeG1-P1.M`, definition of `M1` and its
reported index; the literal permutations are `HeG1-p2058B0`. Reproducible
untrusted producers and the finite certificate are retained in `IndexBound/Source/`.
-/

namespace Held.Realization
open Subgroup.CosetWordCertificate IndexCertificate

/-- A checked cover by the 2058 right cosets of the literal marked subgroup. -/
public def markedSubgroupCosetCover :
    Subgroup.GeneratorCosetCover markedSubgroup IndexCertificate.generator (Fin 2058) := by
  exact coverOfFacts facts Fin.val 0 (definitions.repr_zero generator) dest output
    hshape (fun i a => all_hold valid _ (output_lt i a))

/-- The upper index bound uses the concrete generators only, with no extra hypotheses. -/
public theorem markedSubgroup_index_le : markedSubgroup.index ≤ 2058 := by
  simpa using markedSubgroupCosetCover.index_le_card IndexCertificate.generator_closure

/-- The literal ATLAS marked subgroup is the entire stabilizer of its fixed point. -/
public theorem markedSubgroup_eq_baseStabilizer : markedSubgroup = baseStabilizer :=
  markedSubgroup_eq_baseStabilizer_of_index_le markedSubgroup_index_le

/-- The reported ATLAS index, for the exact Held carrier. -/
public theorem markedSubgroup_index : markedSubgroup.index = 2058 := by
  rw [markedSubgroup_eq_baseStabilizer, baseStabilizer_index]

end Held.Realization
