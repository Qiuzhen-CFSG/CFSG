module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Regularity
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.SourceRecognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect.CenterIntersection

/-!
# The full second marked quotient from the genuine earlier source

The original orbit-containment proof supplies the first factor's bound.
The critical window through the actual delta is now separated by relative
normality and the prescribed source replacement. Reversing it keeps alpha
at its midpoint and delta at its endpoint, so the same source theorem gives
the second orbit bound. The completed recognition assembly constructs the
marked doubled-dual quotient without any orbit or dynamics premise.

The final consumer retains one original path for both marked sections, the
complete early orbit facts, the actual core's third-layer containment and
the first-layer core-centralizer intersection. Genuine Earlier, the source
(4.4) input, remains explicit; no assertion about the whole core center is
assumed or substituted for its remaining proof.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(ii)--(iii),(vi),
printed pp.898--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.OrbitSource
open NormalizerTransfer Recognition
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The preceding orbit-containment clause at the original selected delta. -/
theorem delta_orbit_le_Q (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (δ : DeltaChoice (Early.Orbit.SourceApplications.higherPath geometry p)) :
    conjugatesIn (Z R δ.vertex) (stabilizer R (alpha R)) ≤ Q R δ.vertex := by
  have hfirst := OrbitGeometry.Replacement.Source.source_orbit_le_Q common earlier p
  obtain ⟨e,v,hv,_,ha,_⟩ := Displacement.Regularity.delta_regular_critical_window
    common earlier δ hfirst
  have hr : (v.reverse common).walk.getVert 4 = alpha R := by
    change v.walk.reverse.getVert 4 = _
    rw [SimpleGraph.Walk.getVert_reverse,v.length_eq_b,earlier.distance]
    exact ha
  have h := OrbitGeometry.Replacement.Regularity.endpoint_orbit_le_Q common earlier
    (v.reverse common) (hv.reverse R common)
  simpa only [hr] using h

/-- Full recognition with the given original delta and no orbit premises. -/
theorem marked_pair_at_delta (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (δ : DeltaChoice (Early.Orbit.SourceApplications.higherPath geometry p)) :
    Nonempty (MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true) :=
  SourceRecognition.marked_pair_at_delta common earlier p δ
    (OrbitGeometry.Replacement.Source.source_orbit_le_Q common earlier p)
    (delta_orbit_le_Q common earlier p δ)

/-- MS93 (4.5.4)(iii), with delta selected from the genuine earlier source. -/
theorem marked_pair (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    Nonempty (MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true) := by
  obtain ⟨δ⟩ := SourceRecognition.deltaChoice_nonempty common earlier p
  exact marked_pair_at_delta common earlier p δ

/-- Simultaneous source output on one original path for the remaining
core-center and higher commutator assembly. -/
theorem source_sections (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    Nonempty (Σ' p : Early.SourcePath R (alpha R),
      Early.Orbit.Source.SourceOrbitFacts R p ∧
      Nonempty (MarkedDualSection source common
        (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R))) ∧
      Nonempty (MarkedPairSection source common
        (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
        (hatV R (alpha R) (p.walk.getVert 6)) true) ∧
      core R (alpha R) ≤ hatSix R (alpha R) (p.walk.getVert 6)
        (p.walk.getVert 8) (p.walk.getVert 10) ∧
      hatV R (alpha R) (p.walk.getVert 6) ⊓
        centralizer (core R (alpha R) : Set (FreeAmalgam R)) = Z R (alpha R)) := by
  obtain ⟨p⟩ := Early.sourcePath_nonempty source common earlier (alpha R) (by rfl)
  exact ⟨⟨p, Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p,
    FirstDirect.markedDualSection common earlier p, marked_pair common earlier p,
    Early.Orbit.Source.Complete.core_le_third_hat common earlier p,
    FirstDirect.first_hat_inf_core_centralizer common earlier p⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.OrbitSource
