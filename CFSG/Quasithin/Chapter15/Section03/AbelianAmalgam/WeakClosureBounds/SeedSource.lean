module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalF918
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalBorel

/-!
# The original seed in the final Borel calculation

The literal fixed plane is centralized by T modulo its central involution.
The earlier local centralizer bound and B.2.14 then turn the calculation on
the two-residual commutator space into the contradiction used by 15.3.65.
The remaining module calculation is supplied by the independent normal and
exchanged component source proofs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.65, printed p.1152.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.OriginalSource
open ChapterA.Section05To06 GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- T centralizes the actual quotient image of its fixed plane. -/
theorem seed_fixed_from_original
    (d : CharacteristicTwo.LocalData G) {H : Subgroup G}
    (hTH : (d.T : Subgroup G) ≤ H)
    [IsElementaryAbelian 2 (conjugateSpanBy d.ZS H)]
    (a : LocalQuotientAction H (conjugateSpanBy d.ZS H) d.Z) :
    seedSpace a d.ZS ≤ fixedSpace a.representation (actorImage H d.T) :=
  (RepresentationReduction.seedSpace_le_actorImage_iff a
    (le_conjugateSpanBy d.ZS H) hTH).mpr
      (FusionCore.CosetSetup.OriginalSource.source_seed_commutator d)

/-- The actual marked E.2 component and the original seed discharge all
local inputs of the terminal contradiction except the module calculation. -/
theorem false_of_original_borel_calculation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {H : Subgroup G} (hH : H ∈ minimalSylowOutsideFamily d.T d.M) (hHMc : H ≤ d.Mc)
    {K : Subgroup H} {f : ℕ} (model : OriginalBorel.OddModel d.T H d.M K f)
    [IsElementaryAbelian 2 (conjugateSpanBy d.ZS H)]
    (a : LocalQuotientAction H (conjugateSpanBy d.ZS H) d.Z)
    (hres : Stellmacher.twoResidualAmbient (d.M ⊓ H) ≤ centralizer (d.V : Set G))
    (hcalc : subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ⊓
      fixedSpace a.representation (borelImage H d.M) ≤
        fixedSpace a.representation (actorImage H (residual H))) : False := by
  have hK : ((K.map H.subtype).subgroupOf H).IsCComponent := by
    change ((K.map H.subtype).comap H.subtype).IsCComponent
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    exact model.component
  have hres' : residual (d.M ⊓ H) ≤ centralizer (d.V : Set G) := by
    simpa only [ComponentIntersection.twoResidualAmbient_eq_map_pResidual, GenerationOne.residual] using hres
  exact false_of_commutator_borel_calculation a d.T d.sylow_le hH.prop.1.2
    inf_le_left hres' (seed_fixed_from_original d hH.prop.1.2 a)
    (FusionCore.CosetSetup.OriginalSource.source_seed_geometry d).2.1.le
    (hHMc.trans (FusionCore.CosetSetup.OriginalSource.source_partner_eq
      hG d hempty hM hu hmany).le) hK model.residual_eq hcalc

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.OriginalSource
