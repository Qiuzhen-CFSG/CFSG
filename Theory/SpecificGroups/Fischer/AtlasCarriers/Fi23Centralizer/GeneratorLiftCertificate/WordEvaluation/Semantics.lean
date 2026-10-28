module

public import Mathlib.GroupTheory.Perm.Basic

/-!
# Interpreting checked products and inverses

Multiplication of permutations is composition. A right inverse of a permutation
is its inverse, by injectivity. These generic facts interpret the finite node
certificates without unfolding the original string-decoded Fi23 generators.
Their consumer is the recovered-word evaluation for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate.WordEvaluation

theorem mul_eval {G α : Type*} [Group G] (ρ : G →* Equiv.Perm α)
    (u v : G) (f g k : α → α)
    (hu : ∀ x, ρ u x = f x) (hv : ∀ x, ρ v x = g x)
    (hk : ∀ x, k x = f (g x)) (x : α) : ρ (u * v) x = k x := by
  rw [map_mul, Equiv.Perm.mul_apply, hv, hu, hk]

theorem inv_eval {G α : Type*} [Group G] (ρ : G →* Equiv.Perm α)
    (u : G) (f k : α → α) (hu : ∀ x, ρ u x = f x)
    (hk : ∀ x, f (k x) = x) (x : α) : ρ u⁻¹ x = k x := by
  rw [map_inv]
  apply (ρ u).injective
  change (ρ u) ((ρ u).symm x) = (ρ u) (k x)
  rw [Equiv.apply_symm_apply, hu, hk]

-- Carry the definitional word equation explicitly. Comparing action values
-- directly would unfold the concrete permutation coercions along the program.
theorem mul_eval_of_eq {G α : Type*} [Group G] (ρ : G →* Equiv.Perm α)
    (w u v : G) (f g k : α → α) (hw : w = u * v)
    (hu : ∀ x, ρ u x = f x) (hv : ∀ x, ρ v x = g x)
    (hk : ∀ x, k x = f (g x)) (x : α) : ρ w x = k x := by
  rw [hw]
  exact mul_eval ρ u v f g k hu hv hk x

theorem inv_eval_of_eq {G α : Type*} [Group G] (ρ : G →* Equiv.Perm α)
    (w u : G) (f k : α → α) (hw : w = u⁻¹)
    (hu : ∀ x, ρ u x = f x) (hk : ∀ x, f (k x) = x)
    (x : α) : ρ w x = k x := by
  rw [hw]
  exact inv_eval ρ u f k hu hk x

theorem eval_of_eq {G α : Type*} [Group G] (ρ : G →* Equiv.Perm α)
    (w u : G) (f k : α → α) (hw : w = u) (hf : f = k)
    (hu : ∀ x, ρ u x = f x) (x : α) : ρ w x = k x := by
  rw [hw, ← hf]
  exact hu x

end Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate.WordEvaluation
