module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.Basic

/-!
# Counting neighbors in invariant color cells

A whole initial color cell is stable under every colored graph symmetry.
Counting neighbors in that cell supplies another invariant. Using only the
small cells needed to distinguish the next orbit reduces finite verification
cost. The cell lists are checked for both containment and completeness.

Source context: the literal ATLAS Held representative graph and colors for GLS3 Table 5.3p.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound
open Held.NormalizerGraph Held.NormalizerGraph.CardBound
open scoped BigOperators

@[expose] public def neighborCount (S : Finset (Fin 2058)) (x : Fin 2058) : ℕ :=
  ∑ y ∈ S, if Adj x y then 1 else 0

public theorem neighborCount_invariant {n : ℕ} {w : ℕ → ℕ}
    (hw : ColoredInvariant n w) (S : Finset (Fin 2058)) (a : ℕ)
    (hS : ∀ x, x ∈ S ↔ w x.val = a)
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ coloredGraphGroup) (hf : Fixes n σ)
    (x : Fin 2058) : neighborCount S (σ x) = neighborCount S x := by
  unfold neighborCount
  symm
  apply Finset.sum_bij (fun y _ => σ y)
  · intro y hy
    apply (hS _).mpr
    rw [hw σ hσ hf]
    exact (hS _).mp hy
  · intro y _ z _ h
    exact σ.injective h
  · intro y hy
    refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
    apply (hS _).mpr
    have he := hw σ hσ hf (σ.symm y)
    rw [σ.apply_symm_apply] at he
    exact he.symm.trans ((hS _).mp hy)
  · intro y _
    simp only [hσ.1 x y]

public theorem narrow_function {n : ℕ} {w v : ℕ → ℕ}
    (hw : ColoredInvariant n w) (f : Fin 2058 → ℕ)
    (hf : ∀ σ ∈ coloredGraphGroup, Fixes n σ → ∀ x, f (σ x) = f x)
    (a s : ℕ)
    (hc : ∀ x : Fin 2058,
      v x.val = if w x.val = a ∧ f x = s then 1 else 0) :
    ColoredInvariant n v := by
  intro σ hσ hfix x
  rw [hc, hc, hw σ hσ hfix x, hf σ hσ hfix x]

end Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound
