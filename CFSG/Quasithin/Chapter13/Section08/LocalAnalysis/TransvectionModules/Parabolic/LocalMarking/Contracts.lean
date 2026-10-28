module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.NaturalSetup
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.SourceAction.Inputs

/-!
# The two coordinate constructions needed for the local marking

`QuotientMarking` records the group portion of `CompatibleMarking`. It is a
construction target, not an additional source hypothesis or a theorem of
existence. Separating it allows quotient recognition and the proof that
coordinates on V/V₂ intertwine with any such quotient marking to proceed
independently. Their assembly must construct both witnesses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.4(2),(6), printed p.916, and the local action in 13.8.6, p.948.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.LocalMarking

open EarlierCore
variable {G : Type*} [Group G]

/-- A marked isomorphism of the literal local quotient, including both
specified subgroup images. No action on the seed quotient is included. -/
structure QuotientMarking (L V₁ V₂ : Subgroup G) where
  localEquiv : (localI L V₁ V₂ ⧸ pCore 2 (localI L V₁ V₂)) ≃*
    InvertedCubicTensor.S₃
  cubic_image : ((localResidual L V₂).subgroupOf (localI L V₁ V₂)).map
    (localEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localI L V₁ V₂)))) =
      zpowers InvertedCubicTensor.cubic
  inverter_image : (((normalizer (V₁ : Set G)).pCoreIn 2).subgroupOf
    (localI L V₁ V₂)).map
    (localEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localI L V₁ V₂)))) =
      zpowers InvertedCubicTensor.inverter

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.LocalMarking
