module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ResidueDiagonal

/-!
# The remaining representation inputs for central torus placement

The residue diagonal has scalar values `1`, `u`, and `u⁻¹` on the three
central-weight classes. Its commutation with all six-node words is proved
in `ResidueDiagonal`. This does not assert that it belongs to their image.

This module gives the actual E7 and E8 applications of two separate inputs:
central words have this scalar form, and membership of such a diagonal in
the word image forces `u³ = 1`. With both inputs, the explicit six-coroot
witness discharges the premise of the published torus-to-central-word
theorem. Neither representation input is proved by this conditional assembly.

Sources: GLS3 §§1.12.5–6 and 2.6.2, and Aschbacher–Smith A.2.17,
printed p.39. The subsystem version and the characteristic-three case
remain obligations of the representation input producers.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement

attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _
variable (F : Type*) [Field F]

/-- The E7 application of scalar form and the independent cubic constraint. -/
theorem e7Six_torus_of_shape_and_cube
    (hshape : ∀ w : SixNodeWord F, (∀ z, Commute (e7Six F w) (e7Six F z)) →
      ∃ u : Fˣ, (e7Six F w).val = residueDiagonal F e7Node u)
    (hcube : ∀ (w : SixNodeWord F) (u : Fˣ),
      (e7Six F w).val = residueDiagonal F e7Node u → u ^ 3 = 1)
    (w : SixNodeWord F) (hc : ∀ z, Commute (e7Six F w) (e7Six F z)) :
    ∃ t : Fin 6 → Fˣ, (e7Six F w).val = sixCorootMatrix F e7Node t := by
  obtain ⟨u, hu⟩ := hshape w hc
  exact ⟨![u,u^2,1,1,u,u^2], hu.trans
    (residueDiagonal_eq_sixCorootMatrix F e7Node u (hcube w u hu))⟩

/-- The E8 application of scalar form and the independent cubic constraint. -/
theorem e8Six_torus_of_shape_and_cube
    (hshape : ∀ w : SixNodeWord F, (∀ z, Commute (e8Six F w) (e8Six F z)) →
      ∃ u : Fˣ, (e8Six F w).val = residueDiagonal F e8Node u)
    (hcube : ∀ (w : SixNodeWord F) (u : Fˣ),
      (e8Six F w).val = residueDiagonal F e8Node u → u ^ 3 = 1)
    (w : SixNodeWord F) (hc : ∀ z, Commute (e8Six F w) (e8Six F z)) :
    ∃ t : Fin 6 → Fˣ, (e8Six F w).val = sixCorootMatrix F e8Node t := by
  obtain ⟨u, hu⟩ := hshape w hc
  exact ⟨![u,u^2,1,1,u,u^2], hu.trans
    (residueDiagonal_eq_sixCorootMatrix F e8Node u (hcube w u hu))⟩

/-- Apply the published E7 Cartan-kernel calculation after torus placement. -/
theorem e7Six_eq_centralWord_of_shape_and_cube
    (hshape : ∀ w : SixNodeWord F, (∀ z, Commute (e7Six F w) (e7Six F z)) →
      ∃ u : Fˣ, (e7Six F w).val = residueDiagonal F e7Node u)
    (hcube : ∀ (w : SixNodeWord F) (u : Fˣ),
      (e7Six F w).val = residueDiagonal F e7Node u → u ^ 3 = 1)
    (w : SixNodeWord F) (hc : ∀ z, Commute (e7Six F w) (e7Six F z)) :
    ∃ u : Fˣ, u ^ 3 = 1 ∧ e7Six F w = e7Six F (centralWord F u) := by
  obtain ⟨t, ht⟩ := e7Six_torus_of_shape_and_cube F hshape hcube w hc
  exact e7Six_eq_centralWord_of_torus F w hc t ht

/-- Apply the published E8 Cartan-kernel calculation after torus placement. -/
theorem e8Six_eq_centralWord_of_shape_and_cube
    (hshape : ∀ w : SixNodeWord F, (∀ z, Commute (e8Six F w) (e8Six F z)) →
      ∃ u : Fˣ, (e8Six F w).val = residueDiagonal F e8Node u)
    (hcube : ∀ (w : SixNodeWord F) (u : Fˣ),
      (e8Six F w).val = residueDiagonal F e8Node u → u ^ 3 = 1)
    (w : SixNodeWord F) (hc : ∀ z, Commute (e8Six F w) (e8Six F z)) :
    ∃ u : Fˣ, u ^ 3 = 1 ∧ e8Six F w = e8Six F (centralWord F u) := by
  obtain ⟨t, ht⟩ := e8Six_torus_of_shape_and_cube F hshape hcube w hc
  exact e8Six_eq_centralWord_of_torus F w hc t ht

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement
