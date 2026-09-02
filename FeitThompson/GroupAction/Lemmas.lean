module

public import FeitThompson.GroupAction.Defs
public import Theory.GroupAction.Lemmas

/-- Compatibility spelling for the fixed-point transport theorem. -/
public theorem fixedPointSubgroup_map_subtype_eq_inf
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (H : Subgroup G) [IsInvariant A G H] :
    (fixedPointSubgroup A H).map H.subtype = H ⊓ fixedPointSubgroup A G := by
  exact fixedPoints_subgroup_map_subtype_eq_inf H

/-- Compatibility spelling for triviality of a `p`-group action on a cyclic
group of order `p`. -/
public theorem actsTrivially_of_isPGroup_on_cyclic_prime_order
    {A G : Type*} [Group A] [Group G] [Finite G] [MulDistribMulAction A G]
    {p : ℕ} (hp : Nat.Prime p) (hA : IsPGroup p A) (hG_cyclic : IsCyclic G)
    (hG_card : Nat.card G = p) :
    ActsTrivially (A := A) (G := G) := by
  exact
    (isTrivialAction_of_isPGroup_on_cyclic_prime_order
      (G := G) (A := A) hp hA hG_cyclic hG_card).acts_trivially
