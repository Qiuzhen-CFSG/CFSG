module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowModelsCore
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsSource

/-!
# Sylow-normalizer containment in the natural A₇ branch

Assume N_G(T) escapes N_G(L). Construct the literal A₅ and A₆ point
quotients and their common two-core, giving the local models. The completed
ambient residual identities and omega-center action then produce a
conjugate A₅ inside A₆ normalized by its Sylow two-subgroup, contrary to
the proved finite-group obstruction. Thus N_G(T) ≤ N_G(L).

The final application discharges precisely this premise of the original
Burnside--TI fusion argument for 12.3.5. Only full natural coordinates and
earlier structural 12.2.2 remain explicit, as authorized for this branch;
their final discharge belongs to `qt-d-1231-local-analysis`. No `Models`,
ambient residual, core identity, conjugating-element or fusion assumption
remains in the containment theorem.

Source: Aschbacher--Smith, 3.3.1(1), printed p.586, its A₇ argument 3.3.22,
pp.597--598, and the application 12.3.5, p.809.
-/

@[expose] public noncomputable section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
namespace Setup.NaturalCoordinates
variable (E : S.NaturalCoordinates)
include E

/-- The A₇ natural-module specialization of source 3.3.1(1), as used in
12.3.5. All local-model, residual and omega-action premises are discharged. -/
theorem sylow_normalizer_le_component
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  obtain ⟨P⟩ := SylowNormalizer.points_nonempty E structural
  obtain ⟨M⟩ := P.models_of_contrary_normalizer structural hescape
  exact hescape (P.normalizer_le_of_models structural M)

/-- Source 12.3.5 for the original chosen natural module, with its earlier
Sylow-normalizer hypothesis proved from the setup. -/
theorem controlsFusion_of_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (x y : G) (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : ∃ g : G, g * x * g⁻¹ = y) : ∃ l ∈ L, l * x * l⁻¹ = y :=
  E.controlsFusion structural (E.sylow_normalizer_le_component structural)
    x y hx hy hx1 hy1 hxy

end Setup.NaturalCoordinates
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
