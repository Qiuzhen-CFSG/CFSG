module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.NumericalSource
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceChiefActions

/-!
# Faithful B.6.9 bounds for chief actions

A chief factor in the D.1 multiple-factor construction is represented on its
literal binary chief module.  When the source action is faithful, the
minimal-parabolic numerical source B.6.9 applies directly in the same universe;
this wrapper keeps the original Sylow and minimal-parabolic data visible to the
D.1 consumer.  Non-faithful factors continue to use the separate kernel
calculus in `SourceChiefActions`.

Source: Aschbacher--Smith B.6.9(1), D.1.2(5), pp. 115, 173.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterD.MultipleFactors
open NoncentralChiefRefinement
variable {H W : Type*} [Group H] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {U : Subgroup H} [U.Normal] [IsElementaryAbelian 2 U]

/-- Literal D.1 chief-action consumer for a faithful factor representation. -/
theorem source_chief_image_ratio_ge_one_of_faithful
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (s : SeriesOn U) (i : Fin s.series.length)
    (hfaith : Function.Injective (s.factorRepresentation i)) :
    1 ≤ quadraticRatio
      (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) := by
  let := s.factorRepresentation_irreducible i
  exact ChapterB.minimalParabolic_faithful_quadraticRatio_ge_one
    hH T hP (s.factorRepresentation i) hfaith

end CFSG.Quasithin.ChapterD.MultipleFactors
