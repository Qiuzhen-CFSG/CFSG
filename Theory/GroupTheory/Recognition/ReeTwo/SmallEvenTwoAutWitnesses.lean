module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutData
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutCertificatesA
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutCertificatesB

/-!
# Normalizer p-core witnesses for small even Ree two candidates

The selected root-word representatives are proper subgroups of the Ree two
Sylow model, and the two checked certificate batches show that their full
automorphism groups are 2-groups.  The finite normalizer condition then gives
the required p-core witnesses.

The representatives use the root convention of Shinoda (1975), (2.3),
pp. 81--82, as fixed in `SmallEvenCandidates`.
-/

namespace ReeTwo.SylowModel

/- The certificate modules import the data layer, so this file is the first
   layer at which both batches can be assembled without a cyclic import. -/

/-- Every selected candidate has a normalizer p-core witness. -/
public theorem smallEvenTwoAut_witnesses :
    ∀ i : Fin 59, i ∈ smallEvenTwoAutIndices →
      (smallEvenCandidate i).HasPCoreNormalizerWitness 2 := by
  intro i hi
  have hAut : IsPGroup 2 (MulAut (smallEvenCandidate i)) := by
    by_cases hA : i ∈ smallEvenTwoAutIndicesA
    · exact smallEvenTwoAutA i hA
    · have hsub : i ∈ smallEvenTwoAutBIndices := by
        simp only [smallEvenTwoAutIndices, smallEvenTwoAutIndicesA,
          smallEvenTwoAutBIndices, Finset.mem_insert, Finset.mem_singleton] at hi hA ⊢
        omega
      exact smallEvenTwoAutB_isPGroup_mulAut i hsub
  exact Subgroup.hasPCoreNormalizerWitness_of_isPGroup_mulAut
    (IsPGroup.of_card (n := 12) card) (smallEvenCandidate i)
    (smallEvenCandidate_ne_top i) hAut

/- The conditional interface is retained for callers that provide a different
   certificate family. -/
public theorem smallEvenTwoAut_witnesses_of_aut_certificates
    (hAut : ∀ i : Fin 59, i ∈ smallEvenTwoAutIndices →
      IsPGroup 2 (MulAut (smallEvenCandidate i))) :
    ∀ i : Fin 59, i ∈ smallEvenTwoAutIndices →
      (smallEvenCandidate i).HasPCoreNormalizerWitness 2 := by
  intro i hi
  exact Subgroup.hasPCoreNormalizerWitness_of_isPGroup_mulAut
    (IsPGroup.of_card (n := 12) card) (smallEvenCandidate i)
    (smallEvenCandidate_ne_top i) (hAut i hi)

end ReeTwo.SylowModel
