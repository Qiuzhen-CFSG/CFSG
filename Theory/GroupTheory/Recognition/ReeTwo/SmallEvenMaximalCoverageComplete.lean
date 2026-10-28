module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalCoverageCertificate

/-!
# Exhaustive eligible maximal-subgroup coverage for the small even nodes

Every centric maximal subgroup of any of the 600 descent nodes which is not
contained in the core-character kernel equals one of the 3617 checked edges.
The binary Schreier soundness theorem applied to the complete finite branch
certificate gives this result for every parent, including those subsequently
excluded by Frattini witnesses.

This extension keeps the certificate downstream of its interface in
`SmallEvenMaximalCoverage`, while exposing the unconditional coverage theorem.

Source: Shinoda (1975), (2.3), pp. 81–82, and the checked classifications assembled
in `SmallEvenMaximalCoverageCertificate`.
-/

namespace ReeTwo.SylowModel

/-- All eligible maximal subgroups of all 600 original parents occur in the
checked edge family, with the original node and edge numbering. -/
public theorem smallEvenMaximalCoverage
    (i : Fin 600) (H : Subgroup SylowModel)
    (hmax : H ⋖ smallEvenDescentNode i)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H)
    (hcore : ¬ H ≤ coreCharacter.ker) :
    ∃ e : Fin 3617, H = SmallEvenDescentEdges.edge e :=
  smallEvenMaximalCoverage_of_certificate smallEvenMaximalCoverageCertificate
    i H hmax hcent hcore

end ReeTwo.SylowModel
