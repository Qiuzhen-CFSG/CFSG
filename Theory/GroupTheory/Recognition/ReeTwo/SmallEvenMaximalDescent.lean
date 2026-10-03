module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentNodes
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalCoverageComplete
public import Theory.GroupTheory.SubgroupEnumerationDescending

/-!
# Maximal descent through the small even nodes

The finite descent certificate has two mathematical parts: each listed edge
is conjugate to a node, and every eligible maximal subgroup of a node occurs
among the listed edges. Together they give the maximal step required by the
small even Frattini census. The edge list and its two checks are separate
finite certificates; neither is inferred from the diagnostic GAP output.
The checked edge equations and binary Schreier coverage now discharge both
parts, giving unconditional descent for all 600 parents.

Source: the maximal-chain descent in `SubgroupEnumerationDescending` and the
root-word node family in `SmallEvenDescentNodes`.
-/

namespace ReeTwo.SylowModel
open Theory.GroupTheory.SubgroupEnumeration

/-- Sound edge equations and exhaustive eligible maximal-subgroup coverage
give the exact step used by the small even census. -/
public theorem smallEvenMaximalDescent_of_edge_certificates
    {n : Nat} (edge : Fin n → Subgroup SylowModel)
    (target : Fin n → Fin 600) (conjugator : Fin n → SylowModel)
    (hedge : ∀ e, (edge e).map (MulAut.conj (conjugator e)).toMonoidHom =
      smallEvenDescentNode (target e))
    (hcover : ∀ (i : Fin 600) (H : Subgroup SylowModel),
      H ⋖ smallEvenDescentNode i →
      Subgroup.centralizer (H : Set SylowModel) ≤ H →
      ¬ H ≤ coreCharacter.ker → ∃ e, H = edge e) :
    ∀ (i : Fin 600) (H : Subgroup SylowModel),
      H ⋖ smallEvenDescentNode i →
      Subgroup.centralizer (H : Set SylowModel) ≤ H →
      ¬ H ≤ coreCharacter.ker → Represented smallEvenDescentNode H := by
  intro i H hmax hcent hcore
  obtain ⟨e, rfl⟩ := hcover i H hmax hcent hcore
  exact ⟨target e, conjugator e, hedge e⟩

/-- Every centric maximal subgroup of any of the 600 nodes which is not
contained in the core-character kernel is conjugate to a node. This supplies
the maximal step of the small even census, including children of parents
subsequently excluded by Frattini witnesses. -/
public theorem smallEvenMaximalDescent
    (i : Fin 600) (H : Subgroup SylowModel)
    (hmax : H ⋖ smallEvenDescentNode i)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H)
    (hcore : ¬ H ≤ coreCharacter.ker) :
    Represented smallEvenDescentNode H :=
  smallEvenMaximalDescent_of_edge_certificates
    SmallEvenDescentEdges.edge SmallEvenDescentEdges.target
    SmallEvenDescentEdges.conjugator SmallEvenDescentEdges.edge_equations
    smallEvenMaximalCoverage i H hmax hcent hcore

end ReeTwo.SylowModel
