module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.Inputs
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.OuterExclusion.A6CyclicThree

/-!
# The mixed A₆–cubic extension for the contained actor

The compatible index-two extension has a noncentral three-core of order
three. The residual-normalizer calculation for the selected contained
actor makes that same core central. Its proof uses only actor placement,
not equality with the endpoint. This eliminates the displayed group
configuration independently of either allowed module dimension.

The companion MixedSource module derives this index-two presentation and
inversion formula from the full B.5.6(4) record.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(4),
printed p.105, and proof of 15.3.49(i), printed pp.1143–1144.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence

open ComponentReduction FactorGeneration ClassificationCases.OuterExclusion

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : PlacedInput κ H M Y V Y0 T ZS Z E)

/-- The mixed extension is impossible for the actual contained best offender. -/
theorem not_a6_cyclic_three_extension
    (K : Subgroup (starImage H (localSpan d.selected.carrier H)))
    (hK : K.index = 2)
    (e : K ≃* alternatingGroup (Fin 6) × Multiplicative (ZMod 3))
    (t : starImage H (localSpan d.selected.carrier H))
    (hinv : t * (e.symm (1, Multiplicative.ofAdd 1) : K) * t⁻¹ =
      ((e.symm (1, Multiplicative.ofAdd 1) : K) :
        starImage H (localSpan d.selected.carrier H))⁻¹) : False := by
  obtain ⟨hcard, hnoncentral⟩ := a6_cyclic_three_extension_core K hK e t hinv
  exact hnoncentral (threeCore_le_center_of_card_three H M Y0 T d.selected.carrier
    d.selected.le_local (le_sup_left.trans d.base_le) d.toLocalInput.twoPerfect
    d.normalizer_eq d.core_le_m d.theta_eq d.actor_core hcard)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
