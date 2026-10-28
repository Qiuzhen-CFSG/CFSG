module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Orientation

/-!
# Keeping the selected delta in the moving-layer argument

The already constructed regular critical window at delta is reversed and
extended at its right end. Its midpoint stays alpha and its sixth vertex
stays the original middle vertex. The first-hat identity replaces the added
forward neighbor by the intrinsic seed Vcirc(delta) joined with Z(delta).
The actual transporter identifies the new second-hat denominator with the
original one. No fresh choice of delta or new regularity premise is used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i) and the proof of
(4.5.4)(iv), printed pp.898--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
open NormalizerTransfer SecondLayer
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The chosen delta is the endpoint of an actual source path with the
original midpoint and the original middle vertex. -/
theorem sourcePath_at_delta (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (δ : DeltaChoice (Early.Orbit.SourceApplications.higherPath geometry p)) :
    Nonempty (Σ' q : Early.SourcePath R (alpha R),
      q.walk.getVert 6 = p.walk.getVert 6 ∧ q.walk.getVert 8 = δ.vertex) := by
  have hfirst := OrbitGeometry.Replacement.Source.source_orbit_le_Q common earlier p
  obtain ⟨e,v,hv,hc,ha,_⟩ := Recognition.Displacement.Regularity.delta_regular_critical_window
    common earlier δ hfirst
  have hl : v.walk.length = 8 := v.length_eq_b.trans earlier.distance
  have hr : (v.reverse common).walk.getVert 4 = alpha R := by
    change v.walk.reverse.getVert 4 = _
    rw [SimpleGraph.Walk.getVert_reverse,hl]
    exact ha
  obtain ⟨⟨q,hq⟩⟩ := OrbitGeometry.Replacement.Regularity.sourcePath_preserving_start_window
    common earlier (v.reverse common) (hv.reverse R common)
  let q' : Early.SourcePath R (alpha R) := { q with center_eq := q.center_eq.trans hr }
  refine ⟨⟨q',?_,?_⟩⟩
  · change q.walk.getVert 6 = _
    rw [hq 6 (by decide)]
    change v.walk.reverse.getVert 6 = _
    rw [SimpleGraph.Walk.getVert_reverse,hl]
    exact hc
  · change q.walk.getVert 8 = _
    rw [hq 8 (by decide)]
    change v.walk.reverse.getVert 8 = _
    rw [SimpleGraph.Walk.getVert_reverse,hl]
    exact SimpleGraph.Walk.getVert_zero _

/-- The moving orbit uses the intrinsic first-hat seed, so it is independent
of the two vertices added beyond the endpoint. -/
@[expose] noncomputable def sourceMovingOrbit (p : Higher.SourcePath (alpha R))
    (v : Vertex R) : Subgroup (FreeAmalgam R) :=
  conjugatesIn (Vcirc R v ⊔ Z R v) (stabilizer R (alpha R)) ⊔
    hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)

/-- The original first moving orbit agrees with its intrinsic seed. -/
theorem orbitMovingGroup_eq_sourceMovingOrbit (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    orbitMovingGroup (Early.Orbit.SourceApplications.higherPath geometry p) =
      sourceMovingOrbit (Early.Orbit.SourceApplications.higherPath geometry p) (p.walk.getVert 8) := by
  unfold orbitMovingGroup sourceMovingOrbit
  have he := (Early.Orbit.Source.HatIdentity.SmallSeed.identitiesOnPath common earlier p).forward
    8 (by decide) (by decide) (by decide)
  change conjugatesIn (hatV R (p.walk.getVert 8) (p.walk.getVert 10)) _ ⊔ _ = _
  rw [show hatV R (p.walk.getVert 8) (p.walk.getVert 10) = _ from he]

omit [Finite M] in
/-- The source path at delta has exactly the original denominator. -/
theorem delta_denominator_eq {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p) :
    hatW R (alpha R) (p.walk.getVert 6) δ.vertex =
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) := by
  unfold hatW
  rw [Recognition.delta_span_eq δ]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
