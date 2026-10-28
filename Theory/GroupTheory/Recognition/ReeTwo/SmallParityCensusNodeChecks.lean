module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusWitnessActions
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusWitnessOutsideCoordinates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusWitnessOutsideQuotient
public import Theory.SpecificGroups.ReeTwo.TailQuotientOrder16Nodes
/-!
# Local exclusions for the Ree two parity census

The first fifteen nodes have order at least 1024: each non-top node contains
the order-64 tail and its quotient image contains a checked order-16 subgroup.
Short generator words certify both containments. The remaining nodes partition
into the nineteen existing candidates and the 97 proposed Frattini exclusions.
For the latter, the generator actions are certified in
`SmallParityCensusWitnessActions`. Nonmembership follows from the tail quotient
for 38 witnesses and fine coordinate invariants for the other 59. Together these
certificates show that every node of order less than 1024 has a Frattini
normalizer witness or is one of the nineteen candidates.

Source: the root words of `SmallParityCensusNodes` and the Shinoda (1975), (2.3)
coordinate quotient in `SylowTailQuotient`. Externally selected word identities
are checked by Lean's kernel.
-/

namespace ReeTwo.SylowModel
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration
private def largeGenerator (i : Fin 14) : Fin 11 → SylowModel :=
  ![![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![rootOne ^ 2 * root 0 * root 3, rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![root 3, rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9, root 9], ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9, root 9], ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9, root 9], ![rootOne ^ 3 * root 3 * root 4, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9, root 9], ![root 3, rootOne ^ 3, rootOne ^ 2, root 5 * root 8, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8, root 9, root 9], ![root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 3, rootOne ^ 2, root 5 * root 8, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8, root 9, root 9], ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 4 * root 9, root 6 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9, root 9], ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 3, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 4 * root 9, root 6 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9, root 9]] i
private theorem largeGenerator_mem_0 (j : Fin 11) :
    largeGenerator 0 j ∈ smallParityCensusNode 1 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))))))
private theorem largeGenerator_mem_1 (j : Fin 11) :
    largeGenerator 1 j ∈ smallParityCensusNode 2 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))))))
private theorem largeGenerator_mem_2 (j : Fin 11) :
    largeGenerator 2 j ∈ smallParityCensusNode 3 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))))))
private theorem largeGenerator_mem_3 (j : Fin 11) :
    largeGenerator 3 j ∈ smallParityCensusNode 4 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))))))
private theorem largeGenerator_mem_4 (j : Fin 11) :
    largeGenerator 4 j ∈ smallParityCensusNode 5 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))))))
private theorem largeGenerator_mem_5 (j : Fin 11) :
    largeGenerator 5 j ∈ smallParityCensusNode 6 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))))))
private theorem largeGenerator_mem_6 (j : Fin 11) :
    largeGenerator 6 j ∈ smallParityCensusNode 7 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
private theorem largeGenerator_mem_7 (j : Fin 11) :
    largeGenerator 7 j ∈ smallParityCensusNode 8 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
private theorem largeGenerator_mem_8 (j : Fin 11) :
    largeGenerator 8 j ∈ smallParityCensusNode 9 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
private theorem largeGenerator_mem_9 (j : Fin 11) :
    largeGenerator 9 j ∈ smallParityCensusNode 10 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
private theorem largeGenerator_mem_10 (j : Fin 11) :
    largeGenerator 10 j ∈ smallParityCensusNode 11 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
private theorem largeGenerator_mem_11 (j : Fin 11) :
    largeGenerator 11 j ∈ smallParityCensusNode 12 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
private theorem largeGenerator_mem_12 (j : Fin 11) :
    largeGenerator 12 j ∈ smallParityCensusNode 13 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
private theorem largeGenerator_mem_13 (j : Fin 11) :
    largeGenerator 13 j ∈ smallParityCensusNode 14 := by
  fin_cases j
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
private theorem largeGenerator_mem (i : Fin 14) (j : Fin 11) :
    largeGenerator i j ∈ smallParityCensusNode ⟨i.val + 1, by omega⟩ := by
  fin_cases i
  · exact largeGenerator_mem_0 j
  · exact largeGenerator_mem_1 j
  · exact largeGenerator_mem_2 j
  · exact largeGenerator_mem_3 j
  · exact largeGenerator_mem_4 j
  · exact largeGenerator_mem_5 j
  · exact largeGenerator_mem_6 j
  · exact largeGenerator_mem_7 j
  · exact largeGenerator_mem_8 j
  · exact largeGenerator_mem_9 j
  · exact largeGenerator_mem_10 j
  · exact largeGenerator_mem_11 j
  · exact largeGenerator_mem_12 j
  · exact largeGenerator_mem_13 j
private def tailWord (i : Fin 14) (k : Fin 6) : List (Fin 11) :=
  (![![[6, 8], [3, 3, 9, 10], [7], [4, 4, 10], [9, 10], [10]], ![[6, 8], [3, 3, 9, 10], [7], [4, 4, 10], [9, 10], [10]], ![[6, 8], [3, 3, 9, 10], [7], [4, 4, 10], [9, 10], [10]], ![[6, 8], [3, 3, 9, 10], [7], [4, 4, 10], [9, 10], [10]], ![[6, 8], [0, 0, 3, 3], [7], [0, 0, 8], [0, 0], [10]], ![[6, 8], [3, 3, 9, 10], [7], [4, 4, 10], [9, 10], [10]], ![[5, 7], [2, 2, 8, 9], [6], [3, 3, 9], [8, 9], [9]], ![[5, 7], [2, 2, 8, 9], [6], [3, 3, 9], [8, 9], [9]], ![[5, 7], [2, 2, 8, 9], [6], [3, 3, 9], [8, 9], [9]], ![[5, 7], [2, 2, 8, 9], [6], [3, 3, 9], [8, 9], [9]], ![[5, 7], [3, 8], [6, 7, 9], [4, 4, 9], [8], [9]], ![[5, 7], [3, 8], [6, 7, 9], [4, 4, 9], [8], [9]], ![[5, 9], [1, 2, 4, 1], [6, 9], [7, 8], [8, 9], [9]], ![[5, 9], [3, 3, 4, 5], [6, 9], [7, 8], [8, 9], [9]]]) i k
private def quotientNode (i : Fin 14) : Fin 27 :=
  ![5, 5, 17, 17, 7, 7, 23, 24, 26, 25, 19, 11, 22, 14] i
private def quotientWord (i : Fin 14) (k : Fin 4) : List (Fin 11) :=
  (![![[0, 2], [3, 4], [2], []], ![[0, 2], [3, 4], [2], []], ![[1, 0, 1], [0, 2], [2], []], ![[0, 0, 1], [1, 2], [2], []], ![[0, 3], [0, 4], [0], [2]], ![[0, 2, 1], [0, 0, 0, 1], [0, 2, 1, 3], [2]], ![[2, 3], [0], [], []], ![[2, 3], [0, 1], [], []], ![[2, 3], [0, 0, 0], [], []], ![[2, 3], [2, 0], [], []], ![[0, 4], [0], [1], []], ![[0], [1], [], []], ![[0, 1, 2], [0, 1, 2, 3], [1, 2], []], ![[1, 0, 2], [1, 2], [], []]]) i k
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem tailWord_valid : ∀ i k,
    evalWord (largeGenerator i) (tailWord i k) = root ⟨k.val + 4, by omega⟩ := by
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem quotientWord_valid : ∀ i k,
    evalWord (TailQuotient.projection ∘ largeGenerator i) (quotientWord i k) =
      TailQuotient.Order16Nodes.generator (quotientNode i) k := by
  intro i k
  apply TailQuotient.coordinateCode_injective
  exact (by decide +kernel : ∀ i k,
    TailQuotient.coordinateCode (evalWord (TailQuotient.projection ∘ largeGenerator i)
      (quotientWord i k)) =
    TailQuotient.coordinateCode (TailQuotient.Order16Nodes.generator (quotientNode i) k)) i k

private theorem large_tail_le (i : Fin 14) :
    tailSubgroup ≤ smallParityCensusNode ⟨i.val + 1, by omega⟩ := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨j, hj, rfl⟩
  change 4 ≤ j.val at hj
  let k : Fin 6 := ⟨j.val - 4, by omega⟩
  have he : (⟨k.val + 4, by omega⟩ : CoreRoot) = j := by
    apply Fin.ext
    dsimp [k]
    omega
  rw [← he, ← tailWord_valid i k]
  exact evalWord_mem _ _ (largeGenerator_mem i) _

private theorem large_quotient_le (i : Fin 14) :
    TailQuotient.Order16Nodes.node (quotientNode i) ≤
      (smallParityCensusNode ⟨i.val + 1, by omega⟩).map TailQuotient.projection := by
  rw [TailQuotient.Order16Nodes.node_eq_closure]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  rw [← quotientWord_valid i k]
  exact evalWord_mem _ _
    (fun j => Subgroup.mem_map_of_mem _ (largeGenerator_mem i j)) _

private theorem large_card_bound (i : Fin 14) :
    1024 ≤ Nat.card (smallParityCensusNode ⟨i.val + 1, by omega⟩) := by
  let U := smallParityCensusNode ⟨i.val + 1, by omega⟩
  have hq : 16 ≤ Nat.card (U.map TailQuotient.projection) := by
    rw [← TailQuotient.Order16Nodes.node_card (quotientNode i)]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion (large_quotient_le i))
      (Subgroup.inclusion_injective _)
  have hi := U.index_map_eq TailQuotient.projection_surjective
    (TailQuotient.ker_projection ▸ large_tail_le i)
  have h1 := (U.map TailQuotient.projection).index_mul_card
  rw [hi, TailQuotient.card] at h1
  have h2 := U.index_mul_card
  rw [card] at h2
  have hindex : U.index ≤ 4 := by nlinarith
  change 1024 ≤ Nat.card U
  nlinarith

/-- The first fifteen nodes cannot occur under the strict order-1024 bound. -/
public theorem smallParityCensusNode_large_card (i : Fin 131) (hi : i.val < 15) :
    1024 ≤ Nat.card (smallParityCensusNode i) := by
  by_cases h0 : i.val = 0
  · have he : i = 0 := Fin.ext h0
    rw [he, smallParityCensusNode_zero, Nat.card_congr (Subgroup.topEquiv).toEquiv, card]
    decide
  · let j : Fin 14 := ⟨i.val - 1, by omega⟩
    have he : (⟨j.val + 1, by omega⟩ : Fin 131) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    exact he ▸ large_card_bound j

/-- Every node is large, an existing candidate, or one of the 97 witness positions. -/
public theorem smallParityCensusNode_index_cases (i : Fin 131) :
    i.val < 15 ∨ (∃ j : Fin 19, i = smallParityCandidateCensusIndex j) ∨
      ∃ k : Fin 97, i = smallParityCensusWitnessIndex k := by
  exact (by decide +kernel : ∀ i : Fin 131,
    i.val < 15 ∨ (∃ j : Fin 19, i = smallParityCandidateCensusIndex j) ∨
      ∃ k : Fin 97, i = smallParityCensusWitnessIndex k) i

/-- The size and action certificates reduce all local checks to witness nonmembership. -/
public theorem smallParityCensusNode_checks_of_witness_nonmembership
    (hout : ∀ k : Fin 97,
      smallParityCensusWitness k ∉ smallParityCensusNode (smallParityCensusWitnessIndex k))
    (i : Fin 131) (hcard : Nat.card (smallParityCensusNode i) < 1024) :
    (smallParityCensusNode i).HasFrattiniNormalizerWitness ∨
      ∃ j : Fin 19, smallParityCensusNode i = smallParityCandidate j := by
  rcases smallParityCensusNode_index_cases i with hi | ⟨j, rfl⟩ | ⟨k, rfl⟩
  · exact (Nat.not_lt_of_ge (smallParityCensusNode_large_card i hi) hcard).elim
  · exact Or.inr ⟨j, smallParityCensusNode_candidate j⟩
  · exact Or.inl (smallParityCensusWitness_of_not_mem k (hout k))

/-- All 97 certified Frattini witnesses lie outside their corresponding nodes. -/
public theorem smallParityCensusWitness_not_mem (k : Fin 97) :
    smallParityCensusWitness k ∉ smallParityCensusNode (smallParityCensusWitnessIndex k) := by
  by_cases hk : k.val ∈ ({0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    21, 22, 38, 40, 41, 44, 45, 46, 48, 49, 52, 53, 67, 68, 69, 70, 71, 72, 88, 89} : Finset ℕ)
  · exact smallParityCensusWitness_not_mem_of_quotient k hk
  · exact smallParityCensusWitness_not_mem_of_fine_coordinates k hk

/-- A census node of order less than 1024 either has an outside Frattini
normalizer witness or equals one of the nineteen candidates. -/
public theorem smallParityCensusNode_checks
    (i : Fin 131) (hcard : Nat.card (smallParityCensusNode i) < 1024) :
    (smallParityCensusNode i).HasFrattiniNormalizerWitness ∨
      ∃ j : Fin 19, smallParityCensusNode i = smallParityCandidate j := by
  exact smallParityCensusNode_checks_of_witness_nonmembership
    smallParityCensusWitness_not_mem i hcard

end ReeTwo.SylowModel
