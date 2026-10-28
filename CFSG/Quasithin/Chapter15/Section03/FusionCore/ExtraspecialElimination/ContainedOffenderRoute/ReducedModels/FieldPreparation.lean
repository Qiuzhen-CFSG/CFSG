module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.LocalNormalizer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.ComponentSection

/-!
# The local restrictions and terminal natural-section contradiction

The contained-offender input supplies the genuine star normalizer, its theta
identity, and the three-rank-one bound. Relative normality of the component
closure, nontriviality of its image and seed centralization are also derived.
Thus the terminal natural-section contradiction needs no extra theta identity
in M ∩ C_G(V).

The remaining larger-field argument must construct the natural coordinates,
their compatible Borel marking, and the B.2.14 sum decomposition. They are
explicit intermediate premises of the terminal helper, not additional earlier
local hypotheses and not a proof of the larger-field exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1144,
the paragraph between 15.3.49(k) and (l).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
open Subgroup Representation.BinaryOffender ComponentReduction ModelReduction
open scoped IsMulCommutative

universe u
variable {G : Type u} [Group G] [Finite G]

namespace Input
variable {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)
include d

omit [Finite G] in
theorem star_normalizer :
    normalizer (starImage H Y0 : Set (H ⧸ pCore 2 H)) = starImage H (M ⊓ H) :=
  LargerFields.star_normalizer H M Y0 d.placed.theta_eq d.placed.normalizer_eq
    d.placed.core_le_m

theorem theta_closure_normalizer (hy : Y0 ≤ localSpan L T) :
    theta (starImage H (localSpan L T) ⊓
      normalizer (starImage H Y0 : Set (H ⧸ pCore 2 H))) = starImage H Y0 :=
  LargerFields.theta_star_component_normalizer H M (localSpan L T) Y0
    d.placed.theta_eq d.placed.normalizer_eq d.placed.core_le_m hy

theorem star_threeRank : primeRank 3 (starImage H Y0) = 1 :=
  LargerFields.star_threeRank_eq_one H M L Y0 d.l_le d.placed.theta_eq
    d.component.commutator_eq d.component_star_ne_bot d.quotient_card_in

/-- Once the larger-field argument has constructed its compatible natural
section and its sum decomposition, the generating seed gives a contradiction. -/
theorem no_natural_component_section
    {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    (hZS : ZS ≤ H) (hy : Y0 ≤ localSpan L T)
    (hsplit : LargerFields.componentSection Z H ZS L T ⊔
      fixedSpace d.placed.action.representation ⊤ = ⊤)
    (s : Representation.SL2CubicFixedSection.NaturalComponentSection (F := F)
      d.placed.action.representation (starImage H (localSpan L T))
        (LargerFields.componentSection Z H ZS L T))
    (hB : ∀ y : starImage H Y0,
      s.model ⟨y, (map_mono (comap_mono hy)) y.property⟩ ∈
        Matrix.SpecialLinearGroup.rankOneBorel F) : False :=
  no_natural_section_of_component_action H M ZS Z (localSpan L T) Y0
    d.placed.action hZS d.closure_le d.closure_normalized d.placed.theta_eq
    (componentClosure_commutator L Y0 T d.component.commutator_eq d.normalizes)
    d.closure_star_ne_bot (LargerFields.componentSection Z H ZS L T) hsplit s hy hB
    d.placed.seed_centralized

end Input
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
