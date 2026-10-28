module

public import Theory.AlgebraicGroup.CoordinateRing.Hopf.AugmentationIdeal

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-!
The augmentation ideal is the only non-constant part of a right-invariant
coordinate ring.  This elementary descent lemma isolates the corresponding
algebraic reduction: once a subalgebra contains every invariant function
vanishing at the identity, adjoining constants makes it contain the whole
invariant ring.
-/
public theorem stage_contains_all_invariants_of_contains_augmentation
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (C : Subalgebra k (Variety.PolynomialFunction G))
    (haug : ∀ f : rightInvariantCoordinateAugmentationIdeal H,
      ∃ c : C, (c : Variety.PolynomialFunction G) = f.1.1) :
    ∀ f : rightInvariantCoordinateRing H,
      ∃ c : C, (c : Variety.PolynomialFunction G) = f.1 := by
  intro f
  let ε : rightInvariantCoordinateRing H →ₐ[k] k :=
    rightInvariantCoordinateCounit H
  let f₀ : rightInvariantCoordinateRing H :=
    f - algebraMap k _ (ε f)
  have hf₀ : f₀ ∈ rightInvariantCoordinateAugmentationIdeal H := by
    change ε f₀ = 0
    dsimp [f₀]
    rw [map_sub, rightInvariantCoordinateCounit_algebraMap, sub_self]
  obtain ⟨c₀, hc₀⟩ := haug ⟨f₀, hf₀⟩
  let cε : C := algebraMap k C (ε f)
  refine ⟨c₀ + cε, ?_⟩
  change (c₀ : Variety.PolynomialFunction G) +
      (cε : Variety.PolynomialFunction G) = f.1
  rw [hc₀]
  change f₀.1 + algebraMap k (Variety.PolynomialFunction G) (ε f) = f.1
  dsimp [f₀, ε]
  rw [sub_add_cancel]

end Theory.AlgebraicGroup
