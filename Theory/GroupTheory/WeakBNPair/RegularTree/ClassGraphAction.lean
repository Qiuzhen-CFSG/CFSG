module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraph

/-!
# The original action on the raw class graph

An invariant relation and a graph action give an action by automorphisms on
the graph of classes. Neighbor lifting carries pointwise fixation of an
original neighborhood to pointwise fixation of the whole class neighborhood.
This uses the original action, without identifying fibers with kernel orbits.

Source application: DGS, *Groups and Graphs* (1985), (3.6), pp.77--78.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X V : Type*} [Group X] [MulAction X V]
variable {Γ : SimpleGraph V} {r : Setoid V} (hr : Invariant (X := X) r)
variable (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))

include hact in
/-- The original permutation of classes preserves raw adjacency. -/
theorem quotientAction_adj (g : X) {a b : Quotient r}
    (hab : (classGraph Γ r).Adj a b) :
    (classGraph Γ r).Adj (quotientAction r hr g a) (quotientAction r hr g b) := by
  obtain ⟨hne, u, v, rfl, rfl, huv⟩ := hab
  exact ⟨fun he => hne ((quotientAction r hr g).injective he),
    g • u, g • v, rfl, rfl, hact g huv⟩

include hact in
/-- Incidence is preserved in both directions by the literal class action. -/
theorem quotientAction_adj_iff (g : X) (a b : Quotient r) :
    (classGraph Γ r).Adj (quotientAction r hr g a) (quotientAction r hr g b) ↔
      (classGraph Γ r).Adj a b := by
  constructor
  · intro hh
    have hi := quotientAction_adj hr hact g⁻¹ hh
    simpa only [map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using hi
  · exact quotientAction_adj hr hact g

/-- Local lifting transports fixation of an entire original neighborhood to
fixation of the entire neighborhood of its class. -/
theorem quotientAction_fixes_neighbor (hlift : NeighborLifting Γ r)
    {g : X} {a : V} (hfix : ∀ b, Γ.Adj a b → g • b = b)
    {b : Quotient r} (hab : (classGraph Γ r).Adj (Quotient.mk r a) b) :
    quotientAction r hr g b = b := by
  obtain ⟨v, hv, rfl⟩ := classGraph_neighbor_lift hlift hab
  rw [quotientAction_mk, hfix v hv]

end Theory.GroupTheory.WeakBNPair.RegularTree
