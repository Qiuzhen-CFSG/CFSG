module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Candidate
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Kernel.Index
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Kernel.Commutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Kernel.NaturalHyperplane

/-!
# The p.912 midpoint-kernel calculation and canonical seed

Kernel.Basic constructs the literal unstarred U_delta2 and X₁ = U_delta2
intersect Q_c, proves normalization and relative normality, and transports
the V_c commutator bound to the original quotient action. Kernel.Commutator
proves the commutator bound into Z_delta2 and its order bound, normalization
by the incident overlap, and the exact unstarred index two from starred escape.
Kernel.NaturalHyperplane then uses the supplied two natural full-SL2(2)
copies to place the midpoint line in the second star and its full
second-parabolic conjugate span in X₁, hence in Q_c.

The final application discharges both geometric premises of Candidate's
canonical seed constructor. The natural coordinates remain the explicit
conditional input; their construction and the dimension-six conclusion
belong to the parent source assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(5), printed p.912.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The p.912 midpoint containments follow from the actual two natural copies.
The index premise of the hyperplane argument is discharged using the
unstarred commutator bound and the original starred escape. -/
theorem midpoint_line_and_span_of_natural_copies
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (n : NaturalCopies (geometry := geometry) d f) :
    d.subspace (Z R s.middle) ≤ Seed.secondTildeStar (geometry := geometry) d f 1 ∧
      midpointSpan f s.middle ≤ Q R s.middle := by
  obtain ⟨hline, hspan⟩ := naturalCopies_midpoint_containments common radius hb s hs hbc d f hf n
    (midpointKernel_relIndex_eq_two common radius s hbc d f hf hescape)
  exact ⟨hline, hspan.trans inf_le_right⟩

/-- Apply the midpoint calculation to the literal canonical seed of clause (3).
Its quotient space is the second-parabolic conjugate span of the midpoint
line, with the original Z_alpha kernel restored by Candidate. -/
theorem canonical_input_of_natural_copies
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (n : NaturalCopies (geometry := geometry) d f) :
    ∃ x : Seed.Input (geometry := geometry) d f s.middle,
      x.space = midpointSpace d f s.middle := by
  obtain ⟨hline, hspan⟩ :=
    midpoint_line_and_span_of_natural_copies common radius hb s hs hbc d f hf hescape n
  exact canonical_input common radius s hs d f n hline hspan

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
