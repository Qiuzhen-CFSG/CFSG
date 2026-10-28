module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.Criteria
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.Square
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Marked
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.ParabolicGeometry.Midpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.ParabolicGeometry.Star
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.ParabolicGeometry.FixedElement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Action.Midpoint

/-!
# Geometric assembly for the marked small-branch parabolic bounds

The midpoint actor is conjugate to the two-core of the selected parabolic.
Its actual fixed-preimage index therefore gives the codimension bound.
A residual-fixed element of core/U supplies a nonzero natural coordinate,
with the supplied marking unchanged and the same parabolic selected.

The small-intersection geometry supplies the midpoint facts. The edge-star
centralization and the absence of global fixed elements in VStar/Z transfer
a nonzero residual-fixed element to core/U. Thus `parabolicBounds_of_flag`
discharges both geometric inputs from the supplied edge-kernel equality and
triple-commutator bound, retaining either selected side and the original marking.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.11), printed p.909.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

include common radius in
/-- Concrete subgroup conclusions give both bounds at the same parabolic,
without altering the original natural-coordinate marking. -/
theorem parabolicBounds_of_midpoint_and_fixed_preimage
    (d : CoreModule source) (m : ℕ)
    (q : AbelianCore.QuotientRecognition.ModuleQuotient d.representation m)
    (s : CriticalSegment geometry) (hmid : MidpointFacts (source := source) s)
    (i : Bool) (hkernel : Flags.RankOne.flagKernel source i = Q R (beta R))
    (hfixed : ¬ commutatorPreimage (core R (alpha R)) (Flags.RankOne.flagResidual source i)
      (U R (alpha R)) ≤ U R (alpha R)) :
    ParabolicBounds d.representation q.marking source.flag i where
  fixed_vector := fixed_vector_of_flag_preimage source geometry common radius d m q i hfixed
  codimension := codimension_of_midpoint source geometry common d s hmid i hkernel

include common radius in
/-- The small-intersection geometry gives both bounds at the selected marked
parabolic from the two explicit flag-control clauses. -/
theorem parabolicBounds_of_flag (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hs : s.SmallIntersection)
    (d : CoreModule source) (m : ℕ)
    (q : AbelianCore.QuotientRecognition.ModuleQuotient d.representation m)
    (i : Bool) (hkernel : Flags.RankOne.flagKernel source i = Q R (beta R))
    (htriple : ⁅⁅V R (beta R), Flags.RankOne.flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ParabolicBounds d.representation q.marking source.flag i := by
  exact parabolicBounds_of_midpoint_and_fixed_preimage source geometry common radius d m q s
    (midpointFacts source geometry common radius hb s hs) i hkernel
    (flag_fixed_preimage_not_le_U source geometry common radius hb s hs d m q i hkernel htriple)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
