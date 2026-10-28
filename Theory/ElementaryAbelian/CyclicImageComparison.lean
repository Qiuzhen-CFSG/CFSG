module

public import Theory.ElementaryAbelian.CyclicKernel
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index

/-!
# Comparing an elementary image with a cyclic quotient

Two homomorphisms with equal kernels on an elementary subgroup have
isomorphic images there. If one target is cyclic, both images have order
at most the exponent prime. This allows a faithful action image to be
compared with an outer quotient without assuming either ambient kernel
is trivial.
-/

namespace IsElementaryAbelian

/-- Equality of the restricted kernels transfers the cyclic-image bound. -/
public theorem card_map_le_of_cyclic_kernel_comparison
    {G H K : Type*} [Group G] [Group H] [Group K] [IsCyclic K]
    {p : ℕ} [Fact p.Prime] (A : Subgroup G) [IsElementaryAbelian p A]
    (f : G →* H) (g : G →* K)
    (hker : ∀ a ∈ A, f a = 1 ↔ g a = 1) : Nat.card (A.map f) ≤ p := by
  let u := f.comp A.subtype
  let v := g.comp A.subtype
  have h : u.ker = v.ker := by
    ext a
    exact hker a a.property
  have hc : Nat.card (A.map f) = Nat.card (A.map g) := by
    have hu : u.range = A.map f := by rw [MonoidHom.range_comp, A.range_subtype]
    have hv : v.range = A.map g := by rw [MonoidHom.range_comp, A.range_subtype]
    rw [← hu, ← hv, ← Subgroup.index_ker, ← Subgroup.index_ker, h]
  rw [hc]
  let : IsElementaryAbelian p (A.map g) := IsElementaryAbelian.map g
  exact card_le_of_disjoint_cyclic_kernel (A.map g) (MonoidHom.id K) (by simp)

end IsElementaryAbelian
