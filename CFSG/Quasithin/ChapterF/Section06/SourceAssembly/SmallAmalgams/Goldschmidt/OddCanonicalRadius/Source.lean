module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.TrackCommutator
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.TrackSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.RadiusReduction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.FiveArcTransport
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SourceReconstruction

/-!
# The complete canonical-radius restriction

The original large two-perfect tree action supplies the semilocal track
centralizers used by (6.11.3). Reversing its exact commutator reduces every odd
radius at least five to five, and the eight-arc midpoint calculation excludes
five. The resulting source input removes the radius premise from the actual
F.6 amalgam assembly.

Source: Goldschmidt (1980), (6.11), printed pp.401–403.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry GreenBook
universe u
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- Goldschmidt (6.11): the original large tree source forces canonical radius
three whenever it is odd. Reversing the source commutator first forces radius
five; the eight-arc commutator then gives the folded-arc contradiction. -/
theorem LargeTreeSource.canonical_radius (h : LargeTreeSource F s)
    (d : CanonicalLabelSetup F s) : d.radius = 2 ∨ d.radius = 3 := by
  rcases d.radius_cases with hr | ⟨ho, hr⟩
  · exact .inl hr
  right
  by_contra hne
  have hlarge : 5 ≤ d.radius := by obtain ⟨k, hk⟩ := ho; omega
  have hcomm (e : CanonicalLabelSetup F s) (he : e.radius = d.radius) :=
    e.odd_track_commutator h.action.toCubicTreeAction h.not_cubic h.not_alternating
      h.five_le h.regular h.track_centralizer_exists_three
      (by simpa only [he] using hlarge) (by simpa only [he] using ho)
  have hfive : d.radius = 5 := d.radius_eq_five_of_odd_track_commutator hcomm ho
  have htrack : ⁅d.label (d.track.vertex d.center),
      d.label (d.track.vertex (d.center+8))⁆ = d.label (d.track.vertex (d.center+4)) := by
    simpa only [hfive,Nat.cast_ofNat,show d.center+(5:ℤ)+3=d.center+8 by omega]
      using hcomm d rfl
  exact d.radius_ne_five_of_track_commutator h.action.toCubicTreeAction h.five_le
    h.regular htrack hfive

/-- The complete canonical-radius source input, with every earlier-source
premise supplied by the original large tree action. -/
theorem canonicalRadius : CanonicalRadiusInput := by
  intro G _ F s h d
  exact h.canonical_radius d

/-- Actual F.6 application: the radius argument is discharged before either
marked exceptional recognition theorem is applied. -/
theorem largeNonabelian_of_marked_source_cuts
    (labels : CanonicalLabelsInput.{u})
    (two : RadiusTwoMarkedInput.{u}) (three : RadiusThreeMarkedInput.{u}) :
    LargeNonabelianMarkedAmalgamInput.{u} :=
  largeNonabelian_of_geometric_source_cuts labels canonicalRadius two three

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
