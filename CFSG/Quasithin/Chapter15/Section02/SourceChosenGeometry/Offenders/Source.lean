module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Quadratic
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Inputs

/-!
# The original uniform offender plane and the residual input

Uniform original-offender quadraticity discharges the last local premise of
the plane construction. Every member of the literal Sigma-minus-Sigma(T)
family has a nontrivial quadratic action and an order-four commutator plane,
normalized by T and H and contained in the embedded center of O²(H).
The final theorem constructs the actual input consumed by the residual-
geometry owner qt-e-152-plane-geometry. That owner discharges the preceding
small-action, wreath and two-overgroup results from qt-e-152-small-parabolic.
The transferred simultaneous marked-factor conclusions remain with this
Offenders owner; this module does not claim those additional statements.

Source: Aschbacher--Smith 15.2.9--11, printed pp.1110--1111.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The actual uniform offender-plane conclusion of 15.2.11. The preceding
small-action and wreath results are discharged by qt-e-152-plane-geometry
using qt-e-152-small-parabolic; no local offender premise remains. -/
theorem ChosenSmallSource.offender_plane
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    (sigmaOutside (T : Subgroup G) H).Nonempty ∧
      ∀ B ∈ sigmaOutside (T : Subgroup G) H,
        actor M V B h.prepared.normalized ∈ ChapterD.Q
          (imageRepresentation M V h.prepared.normalized) ∧
        ⁅V,B⁆ ≤ V ∧ Nat.card (⁅V,B⁆ : Subgroup G) = 4 ∧
        (T : Subgroup G) ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
        H ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
        ⁅V,B⁆ ≤ (center (ChosenGeometry.residual H)).map
          (ChosenGeometry.residual H).subtype :=
  h.offender_plane_of_uniform_quadratic ha hH he (fun _ hA => h.delta_quadratic hH he hA)

/-- An actual input for the residual-recognition owner, with the offender and
its central plane constructed uniformly from the preceding source hypotheses. -/
theorem ChosenSmallSource.exists_residualInput_of_preceding
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hover : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc}) :
    ∃ B, ResidualInput h H B := by
  obtain ⟨hne,hall⟩ := h.offender_plane ha hH he
  obtain ⟨B,hB⟩ := hne
  obtain ⟨_,_,hc,_,hn,hz⟩ := hall B hB
  exact ⟨B,hH,he,hover,hB,hc,hn,hz⟩

end CFSG.Quasithin.Chapter15.Section02
