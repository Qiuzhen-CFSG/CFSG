module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Fixed points of unique ordered products

An endomorphism preserving each factor of an injective ordered product fixes
every coordinate of a fixed product. Neither commutativity of the factors
nor multiplicativity of the coordinate map is required. For twisted groups
the factors are the subgroups associated with positive projected root rays,
which can be nonabelian, rather than individual absolute root groups.

Source application: GLS3, Theorem 2.3.7, descending the ordered products of
Theorem 1.12.7 to Steinberg fixed points.
-/

namespace Subgroup

variable {G : Type*} [Group G] {m : ℕ}

/-- Multiply subgroup coordinates in their specified order. -/
@[expose] public def orderedProduct (Y : Fin m → Subgroup G)
    (x : ∀ i, Y i) : G := (List.ofFn fun i => (x i : G)).prod

/-- Uniqueness of ordered coordinates forces the coordinates of a fixed
product to be fixed, including for nonabelian factors. -/
public theorem fixed_coordinates_of_orderedProduct_injective
    (σ : G →* G) (Y : Fin m → Subgroup G)
    (hσ : ∀ i x, x ∈ Y i → σ x ∈ Y i)
    (hinj : Function.Injective (orderedProduct Y))
    (x : ∀ i, Y i) (hfix : σ (orderedProduct Y x) = orderedProduct Y x) :
    ∀ i, σ (x i : G) = x i := by
  let y : ∀ i, Y i := fun i => ⟨σ (x i), hσ i _ (x i).property⟩
  have hy : orderedProduct Y y = orderedProduct Y x := by
    rw [← hfix]
    simp only [orderedProduct, MonoidHom.map_list_prod, List.map_ofFn]
    rfl
  have heq := hinj hy
  intro i
  exact congrArg (fun z : ∀ i, Y i => (z i : G)) heq

end Subgroup
