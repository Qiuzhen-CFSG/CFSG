module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ShortIrreducibility.InvariantSubspaces
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ShortIrreducibility.CoordinateProjection
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ShortIrreducibility.RootSpanning
public import Theory.AlgebraicGroup.Representations.Algebraic.Irreducible

/-!
# Irreducibility of the literal F4 short-ideal action

The submodule here is the short-root and short-Cartan ideal inside the
52-coordinate integral Geck representation. Its invariant subspaces have been
transported to actual matrix subspaces in `InvariantSubspaces`.

In characteristic two, short-root coordinate projections preserve every invariant
subspace of the short ideal. If a nonzero vector has only Cartan coordinates,
the zero-common-kernel calculation instead detects a short-root line by a root
operator. Actual Tits words then generate every short-root line, and opposite
simple-root operators supply the short Cartan coordinates. Thus every nonzero
invariant submodule is the whole short ideal. The final theorem discharges both
matrix premises of the retained conditional reduction.

Source: Steinberg's integral Chevalley construction
(`refs/KGroup/GLS3/Chapter2St1.tex`) and the short-root Weyl geometry in GLS3
Remark 1.8.9 (`refs/KGroup/GLS3/Chapter1.tex`).
-/

public section
open scoped Classical
open ReeF4

namespace Theory.AlgebraicGroup.F4Chevalley
open ShortIrreducibility
variable {k : Type*} [Field k] [IsAlgClosed k] [CharP k 2]

/-- Reduction to two concrete matrix facts. The coordinate projection and
root-line spanning premises must both be proved before obtaining irreducibility. -/
theorem shortRepresentation_isAlgebraicallyIrreducible_of_projection_of_spanning
    (hprojection : ∀ W : Submodule k (BasisIndex → k), RootCurveInvariant W →
      W ≤ shortSubmodule → ∀ v ∈ W, ∀ r : Root, IsShortRoot r →
        Pi.single (Sum.inr r : BasisIndex) (v (Sum.inr r)) ∈ W)
    (hspanning : ∀ W : Submodule k (BasisIndex → k), RootCurveInvariant W →
      ∀ r : Root, IsShortRoot r → Pi.single (Sum.inr r : BasisIndex) (1 : k) ∈ W →
        shortSubmodule ≤ W) :
    IsAlgebraicallyIrreducibleRepresentation (shortRepresentation (k := k)) := by
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  have hcurve := ambientImage_invariant hW
  have hshort := ambientImage_le W
  have hne : ambientImage W ≠ ⊥ :=
    (ambientImage_eq_bot_iff W).not.mpr hbot
  obtain ⟨r, hr, hrW⟩ := hcurve.exists_root_single_of_projection hshort hne
    (hprojection _ hcurve hshort)
  apply (ambientImage_eq_short_iff W).mp
  exact le_antisymm hshort (hspanning _ hcurve r hr hrW)

/-- Every invariant submodule of the literal characteristic-two F4 short-ideal
action is zero or the whole short ideal. -/
theorem shortRepresentation_isAlgebraicallyIrreducible :
    IsAlgebraicallyIrreducibleRepresentation (shortRepresentation (k := k)) := by
  apply shortRepresentation_isAlgebraicallyIrreducible_of_projection_of_spanning
  · intro W hW hshort v hv r hr
    exact hW.root_coordinate_mem hshort hv r hr
  · intro W hW r hr hmem
    exact hW.shortSubmodule_le_of_root_single r hr hmem

end Theory.AlgebraicGroup.F4Chevalley
