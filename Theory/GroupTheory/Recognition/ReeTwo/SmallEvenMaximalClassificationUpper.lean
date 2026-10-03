module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpper300
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperA
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperB
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperC

/-!
# Maximal-subgroup classification for small even descent nodes 300–599

Every maximal subgroup of an upper-range node is contained in the core, has
a centralizing element outside itself, or equals one of the recorded descent
edges. Splitting the node index at 301, 400, and 500 assembles the finite
certificates checked in the imported modules. All node and edge numbering
is preserved.

Source: Shinoda (1975), (2.3), pp. 81–82; the root-word conventions and input
provenance in `SmallEvenDescentEdgeData`, and the finite-certificate soundness
proof in `SmallEvenMaximalClassificationUpperSupport`.
-/

namespace ReeTwo.SylowModel

/-- The checked certificate classification covers all upper-range nodes. -/
public theorem SmallEvenUpperCertificates.classified300To599
    (i : Fin 600) (hlo : 300 ≤ i.val) (H : Subgroup SylowModel)
    (h : H ⋖ smallEvenDescentNode i) : SmallEvenUpperCertificates.Classified H := by
  by_cases h300 : i.val = 300
  · have hi : i = 300 := Fin.ext h300
    subst i
    exact SmallEvenUpperCertificates.classified300 H h
  by_cases h400 : i.val < 400
  · exact SmallEvenUpperCertificates.classified301To399 i (by omega) h400 H h
  by_cases h500 : i.val < 500
  · exact SmallEvenUpperCertificates.classified400To499 i (by omega) h500 H h
  exact SmallEvenUpperCertificates.classified500To599 i (by omega) H h

/-- Every maximal subgroup of a node numbered at least 300 lies in the core,
has an outside centralizer witness, or is one of the original 3617 edges. -/
public theorem smallEvenDescentNode_maximal_classification_upper
    (i : Fin 600) (hlo : 300 ≤ i.val) (H : Subgroup SylowModel)
    (h : H ⋖ smallEvenDescentNode i) :
    H ≤ coreCharacter.ker ∨
    (∃ c, c ∈ Subgroup.centralizer (H : Set SylowModel) ∧ c ∉ H) ∨
    (∃ e : Fin 3617, H = SmallEvenDescentEdges.edge e) :=
  SmallEvenUpperCertificates.classified300To599 i hlo H h

end ReeTwo.SylowModel
