module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Elementary subgroups with trivial kernel in a cyclic image

An elementary abelian p-subgroup disjoint from the kernel of a homomorphism
to a cyclic group embeds in that cyclic group. Its cardinality equals its
exponent and hence divides p. This is the general cyclic-outer-quotient
estimate used in GLS, Volume 2, Theorem 26.24.
-/

namespace IsElementaryAbelian

/-- An elementary subgroup disjoint from a cyclic quotient's kernel has order
at most its exponent prime. -/
public theorem card_le_of_disjoint_cyclic_kernel
    {G H : Type*} [Group G] [Group H] [IsCyclic H]
    {p : ℕ} [Fact p.Prime] (D : Subgroup G) [IsElementaryAbelian p D]
    (f : G →* H) (hD : Disjoint D f.ker) : Nat.card D ≤ p := by
  have hi : Function.Injective (f.comp D.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hD x.property hx
  have : IsCyclic D := isCyclic_of_injective (f.comp D.subtype) hi
  have hd : Nat.card D ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p p D
  exact Nat.le_of_dvd (Fact.out : p.Prime).pos hd

end IsElementaryAbelian
