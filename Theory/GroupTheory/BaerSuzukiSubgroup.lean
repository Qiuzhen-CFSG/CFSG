module

public import Theory.GroupTheory.BaerSuzuki

/-!
# Baer–Suzuki for subgroups

The element criterion implies the subgroup criterion: if every pair of
conjugates of a p-subgroup generates a p-group, apply the element criterion
to each element of that subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.1.2.
-/

namespace Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Subgroup form of the Baer–Suzuki criterion. -/
public theorem le_pCore_of_conjugate_sup_isPGroup
    (X : Subgroup G) (hX : IsPGroup p X)
    (hpair : ∀ g : G, IsPGroup p (X ⊔ X.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    X ≤ pCore p G := by
  intro x hx
  apply mem_pCore_of_conjugate_pairs_isPGroup x (hX.to_le (zpowers_le.mpr hx))
  intro g
  apply (hpair g).to_le
  rw [closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact (show X ≤ X ⊔ X.map (MulAut.conj g).toMonoidHom from le_sup_left) hx
  · exact (show X.map (MulAut.conj g).toMonoidHom ≤
        X ⊔ X.map (MulAut.conj g).toMonoidHom from le_sup_right)
      (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

/-- A p-subgroup outside the p-core has a conjugate with which it generates
a subgroup that is not a p-group. -/
public theorem le_pCore_or_exists_conjugate_sup_not_isPGroup
    (X : Subgroup G) (hX : IsPGroup p X) :
    X ≤ pCore p G ∨
      ∃ g : G, ¬ IsPGroup p (X ⊔ X.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  classical
  by_cases h : ∀ g : G, IsPGroup p (X ⊔ X.map (MulAut.conj g).toMonoidHom : Subgroup G)
  · exact Or.inl (le_pCore_of_conjugate_sup_isPGroup X hX h)
  · exact Or.inr (not_forall.mp h)

end Subgroup
