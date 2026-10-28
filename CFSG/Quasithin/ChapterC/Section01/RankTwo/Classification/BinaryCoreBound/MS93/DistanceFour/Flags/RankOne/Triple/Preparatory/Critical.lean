module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Paths

/-!
# Selecting the critical midpoint in the bad flag branch

A double commutator bound passes from each generator to their join by two
commutator preimages, using only normalization in the M-vertex stabilizer.
Consequently a noncentral flag triple selects a genuinely noncentral
Z-generator at a neighbor of beta. The local residual normalizes V_alpha,
so this generator also forces V_alpha to escape its neighborhood kernel.
Two critical shifts, reversal, and the supplied common escape theorem extend
that same generator to the midpoint of a critical pair starting at alpha.

`flagCriticalData` constructs this initial configuration. Its endpoint lies
in Q_beta but not in Q_alpha, and its midpoint belongs to nu(alpha). It does
not assert the later incident-flag choices or numbered claims (2)--(4).
No FlagControl, RadiusFacts or natural-section conclusion is used here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the choice at the start of printed p.906 in the proof of (4.6.8),
using the critical escape and reversal statements recorded in CommonFacts.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

private theorem triple_le_of_generators {G : Type*} [Group G] {ι : Sort*}
    (A K V N : Subgroup G) (H : ι → Subgroup G)
    (hK : K ≤ A) (hV : A ≤ normalizer V) (hN : A ≤ normalizer N)
    (hH : ∀ j, H j ≤ A) (ht : ∀ j, ⁅⁅H j, K⁆, V⁆ ≤ N) :
    ⁅⁅⨆ j, H j, K⁆, V⁆ ≤ N := by
  let D := commutatorPreimage A V N
  have hD : A ≤ normalizer D :=
    commutatorPreimage_normalized A V N A hN A.le_normalizer hV hN
  have hle : (⨆ j, H j) ≤ commutatorPreimage A K D := by
    apply iSup_le
    intro j
    exact le_commutatorPreimage (hH j)
      (le_commutatorPreimage ((Subgroup.commutator_le_sup _ _).trans (sup_le (hH j) hK)) (ht j))
  exact (commutator_mono
    ((commutator_mono hle le_rfl).trans (commutator_commutatorPreimage_le A K D hD))
    le_rfl).trans (commutator_commutatorPreimage_le A V N hN)

private theorem triple_eq_bot_of_centralizes {G : Type*} [Group G]
    (H K V : Subgroup G) (hK : K ≤ normalizer V) (hH : ⁅H, V⁆ = ⊥) :
    ⁅⁅H, K⁆, V⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact (commutator_mono (commutator_eq_bot_iff_le_centralizer.mp hH) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      (hK.trans (normalizer_le_normalizer_centralizer _)))

/-- A bad triple has a bad generator at a neighbor of beta. -/
theorem exists_bad_flag_neighbor (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (i : Bool)
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ∃ c, Adjacent R (beta R) c ∧
      ¬ ⁅⁅Z R c, flagResidual source i⁆, V R (alpha R)⁆ ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  classical
  by_contra! hn
  apply hbad
  rw [V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
  have hN : stabilizer R (alpha R) ≤ normalizer
      ((center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :=
    (stabilizer R (alpha R)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ _)
  have hH (c : Vertex R) (hc : Adjacent R (beta R) c) :
      Z R c ≤ stabilizer R (alpha R) :=
    (le_iSup_of_le c (le_iSup_of_le hc le_rfl) : Z R c ≤ neighborSpan (beta R)).trans
      ((V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)).symm.le.trans
        ((edgeRadius_le_radius (alpha R) (beta R) rfl (base_adjacent R)).trans
          (geometry.V_local (alpha R) rfl common.large_distance)))
  apply triple_le_of_generators (stabilizer R (alpha R)) _ _ _ _
    ((flagResidual_le source i).trans (flagParabolic_le source i))
    (DistanceEight.V_normalized R _) hN
  · intro c
    exact iSup_le (hH c)
  · intro c
    exact triple_le_of_generators (stabilizer R (alpha R)) _ _ _ _
      ((flagResidual_le source i).trans (flagParabolic_le source i))
      (DistanceEight.V_normalized R _) hN (hH c) (hn c)

/-- The first choice on p.906, before the local incident flags are selected. -/
structure FlagCriticalData (source : LocalSource L R) (geometry : Geometry R) (i : Bool) where
  middle : Vertex R
  endpoint : Vertex R
  critical : CriticalPair R (alpha R) endpoint (geometry.exists_critical (alpha R) rfl)
  middle_neighbor : Adjacent R (beta R) middle
  first_distance : (cosetGraph R).dist (alpha R) middle = 2
  second_distance : (cosetGraph R).dist middle endpoint = 2
  middle_triple : ¬ ⁅⁅Z R middle, flagResidual source i⁆, V R (alpha R)⁆ ≤
    (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype

/-- Extend the chosen noncentral flag generator to a genuine critical pair. -/
theorem flagCriticalData (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) (i : Bool)
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    Nonempty (FlagCriticalData source geometry i) := by
  obtain ⟨c, hbc, hnc⟩ := exists_bad_flag_neighbor source geometry common i hbad
  have hcol : color R c = false := by
    have hh := adjacent_color_ne R hbc
    have hbeta : color R (beta R) = true := rfl
    cases he : color R c <;> simp_all
  have hK : flagResidual source i ≤ normalizer (V R (alpha R) : Set (FreeAmalgam R)) :=
    ((flagResidual_le source i).trans (flagParabolic_le source i)).trans
      (DistanceEight.V_normalized R _)
  have hescape : ¬ V R (alpha R) ≤ Q R c := by
    intro h
    apply hnc
    have hz : ⁅Z R c, V R (alpha R)⁆ = ⊥ :=
      bot_unique ((commutator_mono le_rfl h).trans (geometry.centralizes c hcol).le)
    rw [triple_eq_bot_of_centralizes _ _ _ hK hz]
    exact bot_le
  have hne : c ≠ alpha R := by
    intro he
    apply hescape
    rw [he]
    exact V_le_Q geometry common.large_distance _ rfl
  have hac : (cosetGraph R).dist (alpha R) c = 2 := by
    have hhi := (cosetGraph_connected R).dist_triangle (u := alpha R) (v := beta R) (w := c)
    have hab : (cosetGraph R).dist (alpha R) (beta R) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (base_adjacent R))
    have hbc' := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hbc)
    have hzero : (cosetGraph R).dist (alpha R) c ≠ 0 := by
      intro hz
      exact hne ((cosetGraph_connected R).dist_eq_zero_iff.mp hz).symm
    have hone : (cosetGraph R).dist (alpha R) c ≠ 1 := by
      intro ho
      have ha := (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp ho)
      exact adjacent_color_ne R ha hcol.symm
    omega
  have hforward : (cosetGraph R).dist (alpha R) c + 2 = geometry.b R := by rw [hac, hb]
  obtain ⟨d, hdcol, hda, hdcrit⟩ :=
    DistanceEight.PathCentrality.exists_critical_shift R rfl hforward hescape
  have hreverse := common.critical_reverse d hdcol c hcol hdcrit
  have hcescape : ¬ V R c ≤ Q R (alpha R) := by
    apply common.escape c hcol d hreverse (alpha R)
    · rw [SimpleGraph.dist_comm]
      exact hda
    · rw [SimpleGraph.dist_comm (u := c), hac, hreverse.1, geometry.distance_constant c hcol]
      exact hb.symm
  have hbackward : (cosetGraph R).dist c (alpha R) + 2 = geometry.b R := by
    rw [SimpleGraph.dist_comm, hac, hb]
  obtain ⟨a', ha', ha'c, hcrit⟩ :=
    DistanceEight.PathCentrality.exists_critical_shift R hcol hbackward hcescape
  exact ⟨⟨c, a', common.critical_reverse a' ha' (alpha R) rfl hcrit, hbc, hac,
    (SimpleGraph.dist_comm ..).trans ha'c, hnc⟩⟩

namespace FlagCriticalData
variable {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The selected midpoint is an M-vertex. -/
theorem middle_color (p : FlagCriticalData source geometry i) : color R p.middle = false := by
  have hh := adjacent_color_ne R p.middle_neighbor
  have hbeta : color R (beta R) = true := rfl
  cases he : color R p.middle <;> simp_all

/-- The selected endpoint is also an M-vertex. -/
theorem endpoint_color (p : FlagCriticalData source geometry i) : color R p.endpoint = false :=
  (DistanceEight.PathCentrality.CriticalPath.ofPair (geometry := geometry) rfl p.critical).end_color

/-- Reversal retains the actual critical noncontainment at alpha. -/
theorem endpoint_not_le_Q (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) : ¬ Z R p.endpoint ≤ Q R (alpha R) :=
  (common.critical_reverse _ rfl _ p.endpoint_color p.critical).2

/-- The endpoint lies in the edge kernel, since its distance from beta is at most three. -/
theorem endpoint_le_edgeKernel (p : FlagCriticalData source geometry i)
    (hb : geometry.b R = 4) : Z R p.endpoint ≤ Q R (beta R) := by
  apply Z_le_Q_of_dist_lt R p.endpoint (geometry.exists_critical _ p.endpoint_color)
  rw [geometry.distance_constant _ p.endpoint_color]
  change (cosetGraph R).dist p.endpoint (beta R) < geometry.b R
  have htri := (cosetGraph_connected R).dist_triangle
    (u := p.endpoint) (v := p.middle) (w := beta R)
  have hmb : (cosetGraph R).dist p.middle (beta R) = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (adjacent_symm R p.middle_neighbor))
  have hem : (cosetGraph R).dist p.endpoint p.middle = 2 := by
    rw [SimpleGraph.dist_comm]; exact p.second_distance
  omega

/-- The chosen Z-layer is literally a generator of the first flag layer. -/
theorem middle_le_firstLayer (p : FlagCriticalData source geometry i) :
    Z R p.middle ≤ firstFlagLayer (R := R) 1 := by
  rw [firstFlagLayer, localConjugate_one,
    V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
  exact le_iSup_of_le p.middle (le_iSup_of_le p.middle_neighbor le_rfl)

/-- The bad triple rules out the central radius layer, so the midpoint belongs to nu(alpha). -/
theorem middle_mem_nu (p : FlagCriticalData source geometry i)
    (early : EarlyFacts R geometry) : nu R geometry (alpha R) p.middle := by
  refine ⟨(SimpleGraph.dist_comm ..).trans p.first_distance, ?_⟩
  intro h
  apply p.middle_triple
  have hB : B R (alpha R) (geometry.Z_normal _) ≤
      centralizer (V R (alpha R) : Set (FreeAmalgam R)) := by
    rw [early.B_eq_center _ rfl]
    rintro _ ⟨z, hz, rfl⟩ v hv
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨v, hv⟩)
  have hK := ((flagResidual_le source i).trans (flagParabolic_le source i)).trans
    (DistanceEight.V_normalized R (alpha R))
  rw [triple_eq_bot_of_centralizes _ _ _ hK
    (commutator_eq_bot_iff_le_centralizer.mpr (h.trans hB))]
  exact bot_le

end FlagCriticalData
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
