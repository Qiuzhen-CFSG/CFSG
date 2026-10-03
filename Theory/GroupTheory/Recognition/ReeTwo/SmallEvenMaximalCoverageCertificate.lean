module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenBinaryGenerators
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationLower
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpper

/-!
# Complete binary branch coverage for the small even descent nodes

Every maximal subgroup of each of the 600 parents lies in the core-character
kernel, has an outside centralizer witness, or equals one of the 3617 recorded
edges. The lower and upper finite classifications give this trichotomy for all
parents. Choosing the Frattini-basis generating families then makes every
nonzero binary Schreier branch maximal, yielding the coverage certificate with
the original node and edge numbering.

Source: Shinoda (1975), (2.3), pp. 81–82; the checked finite classifications in
`SmallEvenMaximalClassificationLower` and `SmallEvenMaximalClassificationUpper`,
and the Burnside basis construction in `SmallEvenBinaryGenerators`.
-/

namespace ReeTwo.SylowModel

/-- The maximal-subgroup trichotomy for all 600 original descent nodes. -/
public theorem smallEvenDescentNode_maximal_classification
    (i : Fin 600) (H : Subgroup SylowModel) (hH : H ⋖ smallEvenDescentNode i) :
    H ≤ coreCharacter.ker ∨
      (∃ c, c ∈ Subgroup.centralizer (H : Set SylowModel) ∧ c ∉ H) ∨
      (∃ e : Fin 3617, H = SmallEvenDescentEdges.edge e) := by
  by_cases hi : i.val < 300
  · exact smallEvenMaximalClassification_lower i hi H hH
  · exact smallEvenDescentNode_maximal_classification_upper i (by omega) H hH

/-- Every nonzero binary branch is discharged by the checked maximal-subgroup
classification, for a generating family of each of the 600 parents. -/
public theorem smallEvenMaximalCoverageCertificate :
    SmallEvenMaximalCoverageCertificate := by
  apply SmallEvenMaximalCoverageCertificate.mk
  intro i
  obtain ⟨n, generators, hgen, hbranches⟩ :=
    smallEvenDescentNode_exists_binarySchreier_generators i
  refine ⟨n, generators, hgen, ?_⟩
  intro σ j hj
  exact smallEvenDescentNode_maximal_classification i _ (hbranches σ j hj)

end ReeTwo.SylowModel
