module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.DeltaActor.Nondegeneracy

/-!
# The actual delta actor and its remaining source-path obligation

Transport proves the candidate's local commutator from the original path.
Nondegeneracy uses both the given transporter and generation equation to
prove its distance four and containment in the original edge kernel.

The final helper exposes precisely how a regular source path through the
same delta, c and a would discharge the remaining product via (4.5.1)(iv).
Such a path is not constructed here: the complete actor construction and
the unconditional delta displacement conclusion remain open.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iii), printed p.899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement
variable {M : Type*} [Group M] {R L : Subgroup M}

/-- A regular path through the specified vertices supplies the exact product.
The product premise is the universally guarded literal (4.5.1)(iv), produced
by qt-c01-ms93-core-factors-early-layers; constructing q is the remaining
geometric obligation. The original path still supplies (4.5.3)(iii).
The orbit containment is the delta instance of (4.5.4)(ii), produced by
qt-c01-ms93-higher-orbit-geometry. -/
theorem delta_small_and_separated_of_regular_path [Finite M]
    (source : LocalSource L R) {geometry : Geometry R}
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (s : OrbitModule source p δ.vertex)
    (q : Higher.SourcePath δ.vertex)
    (hc : q.walk.getVert 6 = p.walk.getVert 6)
    (ha : q.walk.getVert 8 = alpha R)
    (ht : q.walk.getVert 7 = p.walk.getVert 5)
    (hproducts : ∀ (v : Vertex R) (r : Higher.SourcePath v),
      (hatW R v (r.walk.getVert 6) (r.walk.getVert 8) : Set (FreeAmalgam R)) *
        (Q R (r.walk.getVert 8) : Set (FreeAmalgam R)) =
          (Q R (r.walk.getVert 7) : Set (FreeAmalgam R)))
    (horbit : NormalizerTransfer.conjugatesIn (Z R δ.vertex)
      (stabilizer R (alpha R)) ≤ Q R δ.vertex)
    (hcomm : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (alpha R)⁆ ≤ Z R (alpha R)) : letI := s.normal
    Escape.Initial.Natural.Splitting.HasSmallInvolution s.action ∧
      DisplacementSeparation s.action common.natural.marking := by
  apply delta_small_and_separated_of_candidate_product source common earlier δ s
    _ horbit hcomm
  simpa only [hc, ha, ht] using hproducts δ.vertex q

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement
