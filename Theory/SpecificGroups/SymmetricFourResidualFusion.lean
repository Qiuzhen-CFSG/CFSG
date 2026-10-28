module
public import Theory.SpecificGroups.SymmetricFourResidualCore
/-!
# Residual fusion in the symmetric-four core

The three nonidentity elements of the canonical Klein four are fused by
three-cycles. Retaining the cubic order relation ensures that these
conjugators map into every two-residual used by the source endpoint maps.
The finite check concerns only the 24 permutations of four letters.

Source application: Aschbacher–Smith F.5.5, printed pp.301–302.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymmetricFour
open Subgroup SymmetricSix.DuadCalculation
/-- Three-cycles fuse all three nonidentity elements of the canonical Klein four. -/
theorem core_cubic_conjugate : ∀ x∈core, x≠1 → ∀ y∈core, y≠1 →
    ∃ g : Equiv.Perm (Fin 4), g^3=1 ∧ g*x*g⁻¹=y := by
  have hc : ∀ x y : Equiv.Perm (Fin 4),
      (x∈core ∧ y∈core ∧ x≠1 ∧ y≠1) →
      ∃ g : Equiv.Perm (Fin 4), g^3=1 ∧ g*x*g⁻¹=y := by decide +kernel
  intro x hx hx1 y hy hy1
  exact hc x y ⟨hx,hy,hx1,hy1⟩
end Theory.SpecificGroups.SymmetricFour
