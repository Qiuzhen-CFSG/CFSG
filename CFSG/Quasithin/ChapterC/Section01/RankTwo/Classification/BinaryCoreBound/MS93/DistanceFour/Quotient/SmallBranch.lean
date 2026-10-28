module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity

/-!
# Single-factor recognition in MS93's small-intersection branch

The midpoint of the critical segment supplies an offender on the actual binary
core/U quotient. Homogeneous FF recognition gives natural coordinates modulo
the full fixed space. The starred-intersection and selected-parabolic arguments
then leave one copy with zero fixed space. Normalization aligns its quotient
map with the specified marking on U, retaining the natural and dual possibilities.

`singleQuotient_of_smallIntersection` discharges the small-branch premise of
`doubleDualQuotient_of_local_branches`. Its only inputs are the source, common
and radius facts, b = 4, and the actual critical segment's small intersection.
The square-map obstructions for the respective orientations also exclude this
branch in characteristic two, leaving the complementary branch of (4.6.12).

Source: Meierfrankenfeld--Stellmacher (1993), (1.4), printed p.842, and
(4.6.10)--(4.6.11), printed pp.908--909, specialized to the binary case.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

include radius in
/-- The recognition step of binary MS93 (4.6.11): the actual core/U quotient
has one natural factor, with either orientation relative to the given U marking.
Both the faithful FF-action and the one-copy, zero-fixed-space conclusion are
constructed from the source geometry. -/
theorem singleQuotient_of_smallIntersection (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hs : s.SmallIntersection) :
    Nonempty (SingleQuotient source common (fun g v => g.val.mulVec v)) ∨
      Nonempty (SingleQuotient source common Linear.dual) := by
  obtain ⟨d⟩ := SmallBranch.exists_coreModule source geometry common radius hb s hs
  exact SmallBranch.singleQuotient_of_FF_and_purity common d
    (SmallBranch.one_copy_and_no_fixed source geometry common radius hb s hs d)

include common radius in
/-- In characteristic two, the recognized quotient contradicts the square-map
obstruction for its own marking. Thus every actual critical segment belongs to
the complementary branch of (4.6.12). -/
theorem CriticalSegment.not_smallIntersection (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) : ¬ s.SmallIntersection := by
  intro hs
  rcases singleQuotient_of_smallIntersection source geometry common radius hb s hs with h | h
  · obtain ⟨d⟩ := h
    exact d.natural_impossible radius
  · obtain ⟨d⟩ := h
    exact SingleQuotient.dual_impossible radius d

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
