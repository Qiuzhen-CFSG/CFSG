module
public import Theory.SpecificGroups.OrthogonalFourBinary.TerminalLines.Rotations
public import Theory.GroupTheory.PResidual.FiniteImage
/-!
# Odd two-residuals in the binary plus-four isometry group

The actual residual consists of the independent cubic rotations of the two
definite planes, hence has order nine. Residual monotonicity gives odd order
for every group embedded in this isometry group, including its Ω subgroup.

Source: Aschbacher–Smith 15.1.2 and 15.1.6, printed pp.1085–1087.
-/

public section
open Subgroup
namespace OrthogonalFourBinary.TerminalLines

/-- The actual plus-four isometry residual is odd. -/
theorem odd_card_twoResidual : Odd (Nat.card (pResidual 2 IsometryGroup)) := by
  rw [← Nat.card_congr residualEquiv.toEquiv]
  change Odd (Nat.card (Multiplicative (ZMod 3 × ZMod 3)))
  rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod 3 × ZMod 3)),Nat.card_prod,
    Nat.card_zmod]
  decide

/-- Oddness passes through an actual injective isometry representation. -/
theorem odd_twoResidual_of_injective {D : Type*} [Group D]
    (f : D →* IsometryGroup) (hf : Function.Injective f) :
    Odd (Nat.card (pResidual 2 D)) := by
  have hc : Nat.card ((pResidual 2 D).map f) = Nat.card (pResidual 2 D) :=
    card_map_of_injective hf
  rw [← hc]
  exact odd_card_twoResidual.of_dvd_nat (card_dvd_of_le (map_pResidual_le 2 f))
end OrthogonalFourBinary.TerminalLines
