module

public import Theory.SpecificGroups.SymmetricFive.ReflectionCommutator

/-!
# Cubics inverted by the same transposition in S5

Two cubic permutations inverted by the same transposition have commutator
of square one. The finite certificate checks just two permutations and
ordered transpositions, without subgroup or automorphism enumeration.
-/

public noncomputable section
open Equiv Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymmetricFive

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem common_swap_certificate : ∀ x : Perm (Fin 5), x^3=1 →
    ∀ y : Perm (Fin 5), y^3=1 → ∀ i j : Fin 5,
      swap i j*x*(swap i j)⁻¹=x⁻¹ → swap i j*y*(swap i j)⁻¹=y⁻¹ →
      ⁅x,y⁆^2=1 := by
  decide +kernel

/-- The same transposition inverting two cubics forces their actual
commutator to have square one. The trivial cubic is allowed. -/
theorem common_transposition_inverted_cubics_commutator_square
    (a x y : Perm (Fin 5)) (ha : a.IsSwap) (hx : x^3=1) (hy : y^3=1)
    (hax : a*x*a⁻¹=x⁻¹) (hay : a*y*a⁻¹=y⁻¹) : ⁅x,y⁆^2=1 := by
  obtain ⟨i,j,_,rfl⟩ := ha
  exact common_swap_certificate x hx y hy i j hax hay

end Theory.SpecificGroups.SymmetricFive
