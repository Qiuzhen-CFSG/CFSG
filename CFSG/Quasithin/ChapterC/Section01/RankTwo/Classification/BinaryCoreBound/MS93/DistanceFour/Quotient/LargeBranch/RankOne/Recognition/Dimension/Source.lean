module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Cases
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Factors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Assembly

/-!
# The source starred dimension and midpoint seed

The endpoint bound, radius bound and full-first-actor fixation of Y feed the
two literal Y-span intersection calculations. They construct all eight
Estimates fields for the original quotient and compatible frame. The proved
constituent and coordinate constructions then give starred dimension six
and two natural copies for the full rank-one action. The p.912 midpoint
kernel calculation places the canonical conjugate-span seed in Q_c.

The original starred escape remains explicit. Its unstarred consequence is
used only through the proved transport and estimates: the opening p.911
image bound is a lower bound, while the exact midpoint-kernel index is the
separate p.912 calculation. The final consumer discharges the dimension/seed
premise of recognition, leaving only the independently owned clause-(4)
source escape construction.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(5), printed pp.911--912.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace Dimension

/-- All source estimates for clause (5), with the original starred escape
and the literal Z_alpha quotient denominators. -/
theorem source_estimates
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle) :
    Estimates d f s := by
  obtain ⟨hendpoint, hradius, hY⟩ :=
    endpoint_radius_and_Y_fixed common radius hb s hs hbc d f hf hescape
  exact estimates_of_endpoint_and_intersection_calculations common radius hb s hbc d f hf
    hescape hendpoint hradius hY
    (crossing_bound_of_radius_and_Y_fixed common radius hb s hs hbc d f hf hescape hradius hY)
    (contained_bound_of_radius_and_Y_fixed common radius hb s hs hbc d f hf hescape hradius hY)

/-- The completed constituent and coordinate constructions give the exact
conditional dimension-six and full-rank-one natural-copy conclusion. -/
theorem star_dimension_and_natural_copies_of_estimates
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (hest : Estimates d f s) :
    Module.finrank (ZMod 2) (d.subspace (VStar R geometry (alpha R) (beta R))) = 6 ∧
      Nonempty (NaturalCopies (geometry := geometry) d f) := by
  obtain ⟨n⟩ := twoNaturalFactors_of_estimates common radius hb s hs hbc d f hf hescape hest
  exact ⟨n.finrank_eq_six,
    naturalCopies_of_twoNaturalFactors common radius hb s hs hbc d f hf hescape hest n⟩

/-- The complete clause-(5) construction for the original supplied module
and compatible frame. All estimates, natural coordinates and midpoint-kernel
premises are discharged from the source inputs and the explicit clause-(4) escape. -/
theorem star_dimension_and_seed
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle) :
    Module.finrank (ZMod 2) (d.subspace (VStar R geometry (alpha R) (beta R))) = 6 ∧
      Nonempty (Seed.Input (geometry := geometry) d f s.middle) := by
  obtain ⟨hdim, ⟨n⟩⟩ := star_dimension_and_natural_copies_of_estimates common radius hb s hs
    hbc d f hf hescape (source_estimates common radius hb s hs hbc d f hf hescape)
  obtain ⟨x, _⟩ := canonical_input_of_natural_copies common radius hb s hs hbc d f hf hescape n
  exact ⟨hdim, ⟨x⟩⟩

end Dimension

/-- The proved clause-(5) source family supplies the exact construction
callback of recognition. Only the independent clause-(4) escape remains. -/
theorem spanRecognition_of_source_star_escape
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4)
    (hescape : ∀ (s : CriticalSegment geometry), ¬ s.SmallIntersection →
      Adjacent R (beta R) s.middle →
      ∀ d : LayerModule source (V R (alpha R)),
        ∃ f : Seed.Frame source, Seed.Compatible f s ∧
          ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle) :
    SpanRecognition source common := by
  exact spanRecognition_of_star_escape_and_dimension common radius hb hescape
    (fun s hs hbc d f hf hnot =>
      Dimension.star_dimension_and_seed common radius hb s hs hbc d f hf hnot)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
