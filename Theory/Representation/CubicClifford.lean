module

public import Theory.Representation.CubicClifford.Dimension
public import Theory.Representation.CubicClifford.TensorPair
public import Theory.Representation.CubicClifford.ActionTransfer
public import Theory.Representation.CubicClifford.Multiplicity

/-!
# Cubic Clifford multiplicities

The normal-cubic multiplicity dimension is two, even when only the quotient
by KX is a two-group and no complement is supplied. Tensor coordinates
turn a two-dimensional multiplicity space into an actual pair of K-modules.
The action-transfer lemmas pass the nontrivial cubic action to a nonzero
inertia block.

The multiplicity theorems construct the simple multiplicity representation
and the irreducible index-two inertia block from an actual constituent
occurrence. They prove that an extending constituent occurs twice, and that
two exchanged constituents each occur twice. These conditional results supply
the abstract representation argument in Aschbacher–Smith 13.8.21(1), printed
p.956; the concrete constituent and extension identifications belong to its
source-theorem assembly.
-/

namespace Representation.CubicClifford

/-- The dimension theorem in the commutator-generation form used for
binary chief factors. The normal subgroup K is required to act trivially. -/
public theorem finrank_eq_two_of_commutator_eq_top
    {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) H V)
    [IsIrreducible ρ] (K X : Subgroup H) [K.Normal] [X.Normal]
    (hX : Nat.card X = 3) (hK : K ≤ ρ.ker)
    (hQ : IsPGroup 2 (H ⧸ (K ⊔ X)))
    (hcomm : BinaryOffender.subspaceCommutator ρ ⊤ X = ⊤) :
    Module.finrank (ZMod 2) V = 2 := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  exact finrank_eq_two ρ K X hX hK hQ (not_le_ker_of_commutator_eq_top ρ X hcomm)

end Representation.CubicClifford
