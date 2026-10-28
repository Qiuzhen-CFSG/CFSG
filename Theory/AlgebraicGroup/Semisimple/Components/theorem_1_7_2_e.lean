module

public import Theory.AlgebraicGroup.Semisimple.Components.FamilyRangeUnique

/-!
GLS3, Theorem 1.7.2(e): uniqueness of the simple components and the centre of
a semisimple component product.

The component ranges agree by the uniqueness theorem for finite commuting
simple factor families: a nontrivial mixed commutator produces a connected
normal subgroup in each simple factor and hence identifies the factors.  For
the centre formula, factor a central point through one family.  Pairwise
commutation and cancellation show that each factor is central in its own
component; conversely, the product of component-central factors commutes with
every component and therefore with the whole ambient group.
-/

universe u

namespace Theory.AlgebraicGroup

open scoped Pointwise

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option warningAsError false in
public theorem theorem_1_7_2_e
    {G : Variety k} [AlgebraicGroup G]
    {n m : ℕ} {components : Fin n → ClosedSubgroup G}
    {components' : Fin m → ClosedSubgroup G}
    (hfamily : IsSemisimpleComponentFamily components)
    (hfamily' : IsSemisimpleComponentFamily components') :
    Set.range components = Set.range components' ∧
      (∀ z : Variety.Point G,
        z ∈ Subgroup.center (Variety.Point G) ↔
          ∃ factors : Fin n → Variety.Point G,
            (∀ i, factors i ∈ components i ∧
              ∀ y, y ∈ components i → Commute (factors i) y) ∧
            z = (List.ofFn factors).prod) := by
  constructor
  · exact hfamily.range_eq hfamily'
  · intro z
    constructor
    · intro hz
      rcases hfamily.factorization z with ⟨factors, hfactors, hprod⟩
      refine ⟨factors, ?_, hprod⟩
      have hz' : (List.ofFn factors).prod ∈
          Subgroup.center (Variety.Point G) := by
        rw [← hprod]
        exact hz
      intro i
      refine ⟨hfactors i, ?_⟩
      exact IsSemisimpleComponentFamily.factors_mem_center_of_product_mem_center
        hfamily factors hfactors hz' i
    · rintro ⟨factors, hcenters, rfl⟩
      exact IsSemisimpleComponentFamily.product_mem_center
        hfamily factors hcenters

end Theory.AlgebraicGroup
