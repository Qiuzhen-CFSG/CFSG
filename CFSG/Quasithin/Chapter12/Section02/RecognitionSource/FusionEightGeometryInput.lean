module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometrySeed
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup

/-!
# The intermediate reduced FF-module in the A₈ point argument

These are the properties of the actual L-conjugate span of Ω₁Z(C_T(v))
needed to apply the earlier module classification. They are intermediate
conclusions to construct from the original source hypotheses, not additional
hypotheses of 12.2.16. In particular the contract contains no decomposition,
fusion assertion or omega-center containment in V.

The construction and its conditional module-theoretic consumer can be proved
independently; the original source assembly must supply this whole contract.
Source: Aschbacher--Smith 12.2.16, last paragraph, printed p.800.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
namespace AlternatingEightFusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The intermediate module, retaining its actual subgroup and faithful action image. -/
structure PointSpanModule (C : AlternatingEightFusion T L V) : Prop where
  elementary : IsElementaryAbelian 2 C.pointSpan
  le_sylow : C.pointSpan ≤ (T : Subgroup G)
  normalizes : L ⊔ (T : Subgroup G) ≤ normalizer (C.pointSpan : Set G)
  reduced : IsPReduced 2 (C.pointSpan.subgroupOf (L ⊔ (T : Subgroup G)))
  ff : letI := elementary
    Representation.BinaryOffender.IsFFModule
      (ChapterD.UniqueFactor.imageRepresentation (L ⊔ (T : Subgroup G))
        C.pointSpan normalizes)

end AlternatingEightFusion
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
