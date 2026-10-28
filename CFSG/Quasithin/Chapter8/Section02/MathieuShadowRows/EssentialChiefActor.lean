module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SmallClassification
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.ChiefImageAlignment

/-!
# The same offender on the essential action and every chief factor

In the nonsolvable branch all chief kernels are the canonical core. A sharp
source offender therefore has the same residual membership in every factor.
Small natural actions put that offender outside the residual, whereas a
higher-field linear row puts it inside. This rules out mixing the small
and higher-field linear module alternatives on the common actor, including
the two different natural A₅ modules. No residual centralization of the
source overlap is assumed.

The actor properties below retain the original seed subspace in the actual
essential quotient, as well as all original action maps. Their constructor
is the original M22-code application in Chapter12.
Source: Aschbacher--Smith, 3.1.9(6), printed pp.577--578.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterB ChapterD
universe u
variable {G : Type u} [Group G] [Finite G] {H V : Subgroup G}
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
  {S : Sylow 2 H} {hVH : V ≤ H}


/-- Properties of the selected actor on the actual essential source action.
These properties are constructed from the original sharp chief actor. -/
structure EssentialChiefActor
    (a : EssentialSeedAction H V S hVH) (A : Subgroup H) : Prop where
  offender : IsOffender a.imageRepresentation (A.map a.projection)
  large : 2 ≤ rank (A.map a.projection)
  sharp : rank (A.map a.projection) =
    fixedCodim a.imageRepresentation (A.map a.projection)
  centralizes : A.map H.subtype ≤ centralizer (V : Set G)
  seed_fixed : Chapter3.quotientSeed H V a.kernel ≤
    fixedSpace a.kernel.quotientRepresentation A
  chief : ∀ (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (i : Fin s.series.length),
    ¬ s.Central i →
      IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) A) ∧
      Nonempty (LiteralChiefActionEquiv a.representation (s.factorRepresentation i))
  chief_sharp : ∀ (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length), ¬ s.Central i →
      rank (actionSubgroup (s.factorRepresentation i) A) =
        fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
          (actionSubgroup (s.factorRepresentation i) A)
  small_iff : ∀ (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (i : Fin s.series.length),
    ¬ s.Central i → (
      ChiefSmallNaturalAlternatives a.imageRepresentation ↔
        ChiefSmallNaturalAlternatives
          (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)))

theorem essential_small_iff_chief_small
    (a : EssentialSeedAction H V S hVH)
    (hD : IsSQTK KnownSimple.IsKnownSimple H) (hns : ¬ Group.IsSolvable H)
    (A : Subgroup H)
    (hff : ∀ (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (i : Fin s.series.length),
      ¬ s.Central i →
      IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) A) ∧
      rank (actionSubgroup (s.factorRepresentation i) A) =
        fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
          (actionSubgroup (s.factorRepresentation i) A))
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (i : Fin s.series.length)
    (hi : ¬ s.Central i) :
    (ChiefSmallNaturalAlternatives a.imageRepresentation ↔
      ChiefSmallNaturalAlternatives
        (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))) := by
  constructor
  · intro hsmall
    exact a.all_chief_small_of_sharp hD hsmall A hff s i hi
  · intro hsmall
    let := a.irreducible
    let := s.factorRepresentation_irreducible i
    have hseed := a.sharp_offender_of_chiefs A hff
    have hnot := minimalParabolic_small_chief_offender_not_le_twoResidual
      (s.factorRepresentation i) S a.original_minimal A (hff s i hi).1 hsmall
    have hbest := minimalParabolic_sharp_image_isBestOffender
      a.representation hD S a.original_minimal hseed.1 hseed.2
    apply minimalParabolic_chief_small_of_offender_not_residual
      a.representation hD S a.original_minimal hbest
    intro _ hres
    exact hnot ((a.chief_residual_membership_iff hD hns ⟨_,hseed.1⟩ s i
      ⟨_,(hff s i hi).1⟩ A).mpr hres)

end CFSG.Quasithin.Chapter8.MathieuShadowRows
