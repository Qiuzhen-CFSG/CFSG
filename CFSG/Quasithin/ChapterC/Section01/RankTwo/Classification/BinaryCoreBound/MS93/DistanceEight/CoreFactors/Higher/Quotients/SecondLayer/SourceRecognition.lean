module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Complete
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.CriticalOrbit
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Dynamics
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Dynamics.Delta
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Dynamics.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.DeltaActor.Regularity.CriticalWindow
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Selection

/-!
# Second-layer recognition from the preceding orbit containments

On the original fourteen-edge source path, the complete earlier calculations
supply the translated hat identities, actor products, and commutator bounds.
The first and delta orbit actions are faithful; their actual small actors give
full movement and distinguish the dual marking. Applying fixed-marking
recognition and gluing yields the literal pair section for the second hat layer.

The only additional geometric inputs are the two instances of (4.5.4)(ii):
the G_a-orbit spans of Z_d and of the selected Z_delta lie in Q_d and Q_delta.
Their independent source proof remains with higher orbit geometry. No action,
representation, displacement, or generation premise is retained here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(ii)--(iii), pp.898--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.SourceRecognition
open Recognition DistanceFour.Linear Escape.Initial.Natural.Splitting
open Early.Orbit.Source NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The first actor's product and commutator follow on the same path from
the already constructed (4.5.1) and (4.5.3) statements. -/
theorem first_actor_source (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ((hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12) :
      Set (FreeAmalgam R)) * (Q R (alpha R) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 5) : Set (FreeAmalgam R))) ∧
    ⁅hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8) := by
  let h := HatIdentity.SmallSeed.identitiesOnPath common earlier p
  refine ⟨?_, HatCommutators.forward_second_bound_of_identity common earlier p h
    (i := 8) (by decide) (by decide) (by decide)⟩
  apply Displacement.first_actor_product (Early.Orbit.SourceApplications.higherPath geometry p)
    (h.forward 6 (by decide) (by decide) (by decide))
    (h.backward (i := 6) (by decide) (by decide) (by decide))
    (h.forward 10 (by decide) (by decide) (by decide))
  exact (Early.firstFactsOnPath source common earlier p).backward 8
    (by decide) (by decide) (by decide) |>.hatW_product

/-- All four recognition properties of the first actual orbit action,
retaining only its preceding orbit-containment instance. -/
theorem first_dynamics (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (δ : DeltaChoice (Early.Orbit.SourceApplications.higherPath geometry p))
    (hfirst : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8))
    (s : OrbitModule source (Early.Orbit.SourceApplications.higherPath geometry p)
      (p.walk.getVert 8)) : letI := s.normal
    Function.Injective s.action ∧ HasSmallInvolution s.action ∧
      commutatorAction s.action.range
        (OrbitSpace (Early.Orbit.SourceApplications.higherPath geometry p) (p.walk.getVert 8)) = ⊤ ∧
      DisplacementSeparation s.action common.natural.marking := by
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  have ht : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := 4) (by rw [p.length_eq]; decide))
  obtain ⟨hprod, hcomm⟩ := first_actor_source common earlier p
  have hbase := Displacement.Regularity.sourcePath_hatW_product common earlier q
  have hb := first_displacement_not_normalized common earlier q hbase
  obtain ⟨hsmall, hsep⟩ := Displacement.small_and_separated_of_edge_product
    source common earlier s ht hprod (Displacement.first_actor_bound earlier q hfirst hcomm)
  exact ⟨first_factor_faithful common earlier q hbase s, hsmall,
    Generation.full_of_edge_product_and_obstruction common earlier δ (Or.inl rfl)
      s ht hprod hfirst hcomm hb, hsep⟩

/-- The corresponding four properties for the original selected delta.
Its transporter and the original path vertices are preserved. -/
theorem delta_dynamics (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (δ : DeltaChoice (Early.Orbit.SourceApplications.higherPath geometry p))
    (hfirst : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8))
    (hdelta : conjugatesIn (Z R δ.vertex) (stabilizer R (alpha R)) ≤ Q R δ.vertex)
    (s : OrbitModule source (Early.Orbit.SourceApplications.higherPath geometry p) δ.vertex) :
    letI := s.normal
    Function.Injective s.action ∧ HasSmallInvolution s.action ∧
      commutatorAction s.action.range
        (OrbitSpace (Early.Orbit.SourceApplications.higherPath geometry p) δ.vertex) = ⊤ ∧
      DisplacementSeparation s.action common.natural.marking := by
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  have ht : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := 4) (by rw [p.length_eq]; decide))
  have hbase := Displacement.Regularity.sourcePath_hatW_product common earlier q
  have hcomm := (Complete.sourceOrbitFacts common earlier p).hatW_commutator
  have hprod := Displacement.Regularity.delta_product_of_first_orbit common earlier δ hfirst
  obtain ⟨hsmall, hsep⟩ := Displacement.Regularity.delta_small_and_separated_of_first_orbit
    source common earlier δ s hfirst hdelta hcomm
  exact ⟨delta_factor_faithful common earlier δ hbase hfirst s, hsmall,
    Generation.full_of_edge_product_and_obstruction common earlier δ (Or.inr rfl)
      s ht hprod hdelta (Displacement.delta_actor_commutator δ hcomm)
      (delta_displacement_not_normalized common earlier δ hbase hfirst), hsep⟩

/-- MS93 (4.5.4)(iii) from its two literal preceding (ii) instances.
This constructs and recognizes both quotient actions before gluing them,
without a module model or dynamics assumption. -/
theorem marked_pair_at_delta (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (δ : DeltaChoice (Early.Orbit.SourceApplications.higherPath geometry p))
    (hfirst : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8))
    (hdelta : conjugatesIn (Z R δ.vertex) (stabilizer R (alpha R)) ≤ Q R δ.vertex) :
    Nonempty (MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true) := by
  apply markedPair_of_source_dynamics earlier δ
  · intro v hv
    rcases hv with rfl | rfl
    · exact OrbitGeometry.orbit_abelian_of_le_Q (p.even_color (i := 8)
        (by decide) (by decide)) hfirst
    · exact OrbitGeometry.orbit_abelian_of_le_Q (delta_color δ) hdelta
  · exact (Complete.sourceOrbitFacts common earlier p).hatW_commutator
  · intro v hv s
    rcases hv with rfl | rfl
    · exact first_dynamics common earlier p δ hfirst s
    · exact delta_dynamics common earlier p δ hfirst hdelta s
  · exact hfirst
  · exact Displacement.Regularity.sourcePath_hatW_product common earlier
      (Early.Orbit.SourceApplications.higherPath geometry p)

/-- The earlier source identities construct the actual three-seed choice
on the original path; no additional selection premise is needed. -/
theorem deltaChoice_nonempty (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    Nonempty (DeltaChoice (Early.Orbit.SourceApplications.higherPath geometry p)) :=
  Selection.exists_deltaChoice common earlier
    (Early.Orbit.SourceApplications.higherPath geometry p)
    ((HatIdentity.SmallSeed.identitiesOnPath common earlier p).forward 6
      (by decide) (by decide) (by decide))

/-- A consumer for the complete geometric orbit-containment clause: it
selects delta, checks both seed distances, and constructs the marked pair.
The displayed containment family is the sole remaining (4.5.4)(ii) input. -/
theorem marked_pair_of_orbit_containment (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (horbit : ∀ v : Vertex R, color R v = false →
      (cosetGraph R).dist (alpha R) v ≤ 4 →
      conjugatesIn (Z R v) (stabilizer R (alpha R)) ≤ Q R v) :
    Nonempty (MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true) := by
  obtain ⟨δ⟩ := deltaChoice_nonempty common earlier p
  apply marked_pair_at_delta common earlier p δ
  · apply horbit _ (p.even_color (i := 8) (by decide) (by decide))
    have h := p.distance (geometry := geometry) (i := 4) (j := 8)
      (by decide) (by decide)
    simpa only [p.center_eq, Nat.reduceSub] using h.le
  · exact horbit _ (delta_color δ) (Displacement.delta_dist_base_le δ)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.SourceRecognition
