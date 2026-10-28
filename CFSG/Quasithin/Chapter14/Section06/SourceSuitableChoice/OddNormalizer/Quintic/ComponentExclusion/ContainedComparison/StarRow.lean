module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RankOneBlocks

/-!
# The natural rank-one row before reconstruction

This interface retains the actual moved section of the C.2.7 star
representation, its natural action and its best offenders. It is an explicit
classification premise, not a claimed consequence of five-rank one alone.
The proved C.2.7 geometry gives the Sylow and star-Borel conclusions from
these data. Identifying the original block still requires reconstruction.

Source: Aschbacher--Smith C.2.7(3)(a)(i), pp.145--147, applied in 14.6.15,
printed p.1035.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- The natural row on a specified representation and component image.
Abstracting the representation keeps its additive instances fixed. -/
structure NaturalRow {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) where
  included : L ≤ offenderSubgroup ρ
  sectionModel : MovedSection (ρ.comp (offenderSubgroup ρ).subtype)
    (L.subgroupOf (offenderSubgroup ρ))
  field : BinaryField
  natural : ActionEquiv
    (sectionModel.action.comp (L.subgroupOf (offenderSubgroup ρ)).subtype)
    (linearNatural field 2)
  ratio : quadraticRatio sectionModel.action = 1
  offenders : ∀ B, IsBestOffender sectionModel.action B →
    ∃ S : Sylow 2 (L.subgroupOf (offenderSubgroup ρ)),
      B = (S : Subgroup _).map (L.subgroupOf (offenderSubgroup ρ)).subtype

/-- Specialize without changing the actual C.2.7 action or its component. -/
abbrev NaturalStarRow (K R : Subgroup G) :=
  NaturalRow (starRepresentation K R) (starImage K R K)

/-- The original geometry consequences retain the literal star intersection.
The distinction between the natural and alternating-five blocks remains. -/
theorem NaturalStarRow.geometry {H K R M : Subgroup G}
    (row : NaturalStarRow K R) (h : Input KnownSimple.IsKnownSimple H R M K) :
    Chapter1.IsSylowIn 2 (starImage K R (elementaryAbelianMaxJ R)) (starImage K R K) ∧
      IsRankOneBorel (starImage K R K) (starM K R M) ∧
      Chapter1.IsSylowIn 2 R (K ⊔ R) ∧
      ((∃ n, ChapterC.IsL2EvenBlock K n) ∨ ChapterC.IsAlternatingBlock K 5) :=
  ChapterC.C27Source.rankOne_row_blocks_from_source h row.included row.sectionModel
    row.field row.natural row.ratio row.offenders

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
