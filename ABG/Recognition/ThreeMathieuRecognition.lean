module

public import ABG.Recognition.ThreeMathieuAction
public import Theory.Mathieu.M11.Recognition

/-!
# Recognition of Wong's order-7920 branch

A finite simple group with a semidihedral Sylow two-subgroup of order sixteen,
involution centralizers isomorphic to `GL₂(3)`, and order 7920 is isomorphic
to the concrete Mathieu group `M11`.

Wong's character argument constructs a faithful sharply four-transitive action
on eleven points. Recognition of this action uses its invariant Witt design
and the uniqueness of that design to identify the group with the automorphisms
of the repository's explicit Witt design.

Source: Wong (1964), Theorem 6(a), pp.107–108,
DOI 10.1017/S1446788700022771.
-/

namespace ABG

/-- Wong's order-7920 branch is the actual Mathieu group `M11`. -/
public theorem nonempty_mulEquiv_M11_of_card_eq_7920
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (hG : Nat.card G = 7920) :
    Nonempty (G ≃* Sporadic.Mathieu.M11) := by
  obtain ⟨action, hfaithful, hsharp⟩ :=
    exists_mathieu_sharply_four_transitive_action S hS hG hcard hC
  let := action
  let := hfaithful
  exact Sporadic.Mathieu.nonempty_mulEquiv_M11_of_sharplyMultiplyPretransitive hsharp

end ABG
