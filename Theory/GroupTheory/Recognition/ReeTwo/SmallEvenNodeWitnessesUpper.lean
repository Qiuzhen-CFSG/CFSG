module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperBlock6
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperBlock7
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperBlock8
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperBlock9
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperBlock10
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperBlock11

/-!
# Outside Frattini witnesses for all upper small even descent nodes

The six checked blocks supply precisely the 284 required witnesses at indices
300 through 599. A finite index check combines them without changing any node
or any of the 59 prescribed candidates.

Source: the unchanged partition in `SmallEvenNodePartition`; the orbit and
square-word calculations in the imported certificate blocks.
-/

namespace ReeTwo.SylowModel

private def upperCertificates :
    List {i : Fin 600 // (smallEvenDescentNode i).HasFrattiniNormalizerWitness} :=
  UpperCertificate.block6 ++ UpperCertificate.block7 ++ UpperCertificate.block8 ++
    UpperCertificate.block9 ++ UpperCertificate.block10 ++ UpperCertificate.block11

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem upper_coverage : ∀ i : Fin 600,
    300 ≤ i.val → (∀ j : Fin 59, i ≠ smallEvenCandidateNode j) →
      i ∈ upperCertificates.map Subtype.val := by decide +kernel

/-- Every required node at index at least 300 has an outside Frattini normalizer witness. -/
public theorem smallEvenDescentNode_upper_witness (i : Fin 600)
    (hi : i ∈ smallEvenWitnessIndices) (hupper : 300 ≤ i.val) :
    (smallEvenDescentNode i).HasFrattiniNormalizerWitness := by
  obtain ⟨a, _, ha⟩ := List.mem_map.mp
    (upper_coverage i hupper ((mem_smallEvenWitnessIndices i).mp hi).2)
  exact ha ▸ a.property

end ReeTwo.SylowModel
