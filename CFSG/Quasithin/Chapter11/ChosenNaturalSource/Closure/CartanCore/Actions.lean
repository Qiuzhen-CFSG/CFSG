module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.Borel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.Frattini

/-!
# Conditional assembly of the two Cartan action consequences

The Borel contradiction gives 11.5.6(3) from its two model outputs. The
quotient/Frattini argument then proves (4) without any additional action,
rank, quotient or generalized-Fitting premise. All groups are those of the
original chosen-natural Geometry, with normality only inside G₁.

This is not yet the unconditional source theorem: the field-detection and
odd point-normalizer outputs remain explicit until their producers finish.
The preceding flag and normalizer geometry remains with the Chapter 11
assembly owner.
Source: Aschbacher--Smith 11.5.6(3--4), printed pp.780--781.
-/

public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Both source action clauses, conditional on the two separately stated
model outputs. Clause (4) has no remaining independent input. -/
theorem cartan_actions_of_borel_detection (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hlocal : E.OddPointNormalizerAction) (hdetect : E.ComponentBorelDetection) :
    (∀ I : Subgroup G, Source.ComponentIn E.Y I → ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2) ∧
      (∀ P : Subgroup G, P ≤ T → P = ⁅P, E.X⁆ →
        (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P, E.Y⁆ ≤ E.Y.pCoreIn 2) := by
  have hcomp := E.component_actions_of_borel_detection hT hX hcart hXR hCX hz hNG
    hlocal hdetect
  exact ⟨hcomp, fun P hP hPX hphi =>
    E.frattini_action_of_component_actions hp hT hX hcart.odd hcomp P hP hPX hphi⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
