module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024Representatives

/-!
# Remaining representatives for the order-1024 Ree two census

These fifteen subgroups are specified by generators over the six-root tail.
Together with the canonical core and the three exceptional representatives,
they are the proposed centric census. The indices here correspond, in order,
to diagnostic labels 9–18, 21, 22, 24, 26, and 27. Defining this family does
not assert exhaustiveness or any automorphism property; those are separate
mathematical obligations.

The generators use the root convention of Shinoda (1975), (2.3), pp. 81–82,
as verified in `ReeTwo.Sylow`. In particular `root 0` is Shinoda root 3.
Parity-kernel subgroups are retained in the list.
-/

namespace ReeTwo.SylowModel

/-- The fifteen remaining proposed representatives, generated over the tail. -/
@[expose] public def residualCandidate (i : Fin 15) : Subgroup SylowModel :=
  tailSubgroup ⊔ Subgroup.closure
    (![({root 3, root 2, root 0, rootOne ^ 2} : Set SylowModel),
      {root 3, root 2, root 1, rootOne ^ 2 * root 0},
      {root 3, root 2, root 0 * root 1, rootOne ^ 2 * root 1},
      {root 2 * root 3, root 1 * root 3, root 0, rootOne ^ 2},
      {root 2 * root 3, root 1, root 0, rootOne ^ 2},
      {root 2 * root 3, root 1 * root 3, root 0 * root 3, rootOne ^ 2 * root 3},
      {root 2 * root 3, root 1, root 0 * root 3, rootOne ^ 2 * root 3},
      {root 2 * root 3, root 1 * root 3, root 0 * root 3, rootOne ^ 2},
      {root 2 * root 3, root 1 * root 3, root 0, rootOne ^ 2 * root 3},
      {root 3, root 2, root 1, rootOne ^ 2},
      {root 2 * root 3, root 1 * root 3, rootOne * root 0},
      {root 2 * root 3, root 1 * root 3, rootOne * root 0 * root 3},
      {root 3, root 2, rootOne},
      {root 3, root 2, rootOne * root 0 * root 1},
      {root 2 * root 3, root 1, rootOne * root 0 * root 3}] i)

/-- The common tail is included by construction. -/
public theorem tailSubgroup_le_residualCandidate (i : Fin 15) :
    tailSubgroup ≤ residualCandidate i := le_sup_left

end ReeTwo.SylowModel
