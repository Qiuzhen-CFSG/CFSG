module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodePartition
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenLargeNodes
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeTwelve
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesLower
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpper

/-!
# Finite filtering certificates for the small even descent nodes

The first eleven entries have order at least 1024. The original 59 candidates
occur at their checked indices, and the remaining 530 entries have outside
Frattini normalizer witnesses. This module assembles the size bounds, the
separate node twelve certificate, and the lower and upper witness batches
without changing any node or candidate. The resulting three-way filter is
unconditional and independent of the maximal-subgroup descent coverage.

Source: the Shinoda (1975), (2.3), pp. 81–82 root words fixed in
`SmallEvenDescentNodes`. Square-word certificates are justified abstractly
in `FrattiniNormalizerWordCertificates`; external calculations are not proofs.
-/

namespace ReeTwo.SylowModel

/-- The initial node contains the embedded order-1024 core. -/
public theorem smallEvenDescentNode_zero_large :
    1024 ≤ Nat.card (smallEvenDescentNode 0) := by
  rw [smallEvenDescentNode_zero, ← Core.card]
  let f : Core → character.ker := fun x =>
    ⟨SemidirectProduct.inl x, show parity 1 = 1 from map_one parity⟩
  apply Nat.card_le_card_of_injective f
  intro x y h
  exact SemidirectProduct.inl_injective (congrArg Subtype.val h)

/-- The requested three-way filter follows from the ten nonzero large-node
bounds and the outside witnesses on the complement of the survivor indices. -/
public theorem smallEvenNodeCertificates_of_large_of_witnesses
    (hlarge : ∀ i : Fin 600, 0 < i.val → i.val < 11 →
      1024 ≤ Nat.card (smallEvenDescentNode i))
    (hwitness : ∀ i : Fin 600, i ∈ smallEvenWitnessIndices →
      (smallEvenDescentNode i).HasFrattiniNormalizerWitness) :
    ∀ i : Fin 600,
      1024 ≤ Nat.card (smallEvenDescentNode i) ∨
      (smallEvenDescentNode i).HasFrattiniNormalizerWitness ∨
      ∃ j : Fin 59, smallEvenDescentNode i = smallEvenCandidate j := by
  intro i
  by_cases hz : i = 0
  · subst i
    exact Or.inl smallEvenDescentNode_zero_large
  by_cases hl : i.val < 11
  · exact Or.inl (hlarge i (Nat.pos_of_ne_zero (fun h => hz (Fin.ext h))) hl)
  by_cases hc : ∃ j : Fin 59, i = smallEvenCandidateNode j
  · obtain ⟨j, rfl⟩ := hc
    exact Or.inr (Or.inr ⟨j, smallEvenDescentNode_candidate j⟩)
  · exact Or.inr (Or.inl (hwitness i ((mem_smallEvenWitnessIndices i).mpr
      ⟨Nat.le_of_not_gt hl, fun j hj => hc ⟨j, hj⟩⟩)))

/-- With all eleven size bounds proved, only the remaining outside witnesses
are needed to complete the finite node filter. Node twelve is already certified. -/
public theorem smallEvenNodeCertificates_of_witnesses
    (hwitness : ∀ i : Fin 600, i ∈ smallEvenWitnessIndices → i ≠ 12 →
      (smallEvenDescentNode i).HasFrattiniNormalizerWitness) :
    ∀ i : Fin 600,
      1024 ≤ Nat.card (smallEvenDescentNode i) ∨
      (smallEvenDescentNode i).HasFrattiniNormalizerWitness ∨
      ∃ j : Fin 59, smallEvenDescentNode i = smallEvenCandidate j := by
  apply smallEvenNodeCertificates_of_large_of_witnesses SmallEvenLargeNodes.nonzero_large
  intro i hi
  by_cases he : i = 12
  · subst i
    exact smallEvenDescentNode_twelve_witness
  · exact hwitness i hi he

/-- Every node outside the eleven large entries and the 59 survivor indices
has an outside Frattini normalizer witness. -/
public theorem smallEvenDescentNode_witness (i : Fin 600)
    (hi : i ∈ smallEvenWitnessIndices) :
    (smallEvenDescentNode i).HasFrattiniNormalizerWitness := by
  by_cases he : i = 12
  · subst i
    exact smallEvenDescentNode_twelve_witness
  by_cases hlt : i.val < 300
  · exact smallEvenDescentNode_witness_lower i hi hlt he
  · exact smallEvenDescentNode_upper_witness i hi (Nat.le_of_not_gt hlt)

/-- Every small even descent node is large, has an outside Frattini normalizer
witness, or is one of the original 59 candidates. -/
public theorem smallEvenNodeCertificates :
    ∀ i : Fin 600,
      1024 ≤ Nat.card (smallEvenDescentNode i) ∨
      (smallEvenDescentNode i).HasFrattiniNormalizerWitness ∨
      ∃ j : Fin 59, smallEvenDescentNode i = smallEvenCandidate j := by
  exact smallEvenNodeCertificates_of_large_of_witnesses
    SmallEvenLargeNodes.nonzero_large smallEvenDescentNode_witness

end ReeTwo.SylowModel
