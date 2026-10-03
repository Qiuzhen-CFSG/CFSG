module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesLowerA
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesLowerB
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesLowerC
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesLowerD
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesLowerE
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesLowerF
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesLowerG

/-!
# Outside Frattini witnesses for the lower small even nodes

The seven batches certify the 245 required nodes below index 300 other than
node twelve. A finite index check assembles them without altering the 600-node
family or the prescribed 59 candidates. Each batch proves nonmembership by a
right-invariant coordinate predicate and proves the Frattini action by products
of squares of the original generators.

Source: the fixed descent nodes and the Shinoda (1975), (2.3), root coordinates.
-/

namespace ReeTwo.SylowModel
open SmallEvenLower

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem covered : ∀ i : Fin 600, i ∈ smallEvenWitnessIndices →
    i.val < 300 → i ≠ 12 →
    i ∈ indicesA ∨ i ∈ indicesB ∨ i ∈ indicesC ∨ i ∈ indicesD ∨ i ∈ indicesE ∨ i ∈ indicesF ∨ i ∈ indicesG := by decide +kernel

/-- All 245 remaining witness nodes below index 300 have outside Frattini witnesses. -/
public theorem smallEvenDescentNode_witness_lower (i : Fin 600)
    (hi : i ∈ smallEvenWitnessIndices) (hlt : i.val < 300) (hne : i ≠ 12) :
    (smallEvenDescentNode i).HasFrattiniNormalizerWitness := by
  rcases covered i hi hlt hne with hA | hB | hC | hD | hE | hF | hG
  · exact witnessesA i hA
  · exact witnessesB i hB
  · exact witnessesC i hC
  · exact witnessesD i hD
  · exact witnessesE i hE
  · exact witnessesF i hF
  · exact witnessesG i hG
end ReeTwo.SylowModel
