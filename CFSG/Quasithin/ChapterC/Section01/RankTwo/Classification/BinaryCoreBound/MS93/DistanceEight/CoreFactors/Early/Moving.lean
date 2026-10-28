module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Paths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Layers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Reversal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Moving

/-!
# Moving generation on the actual extended critical path

A critical endpoint moves at its second predecessor. Reverse a neighboring
critical window and apply the supplied turn to obtain movement at the first
five even centers. The forward windows cover the remaining centers. The
actual natural section from `Earlier`, and irreducibility of its moving
factor, now give Vcirc_a <= hatV(a,c). The same argument contains Z_a.

The existential export supplies the precise local span consumed by the
numerical H bound. No natural section is constructed from the contrary
assumption used in (4.3). The reverse inclusion in (4.5.3)(i) is not asserted.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.5.3), pp.890--898.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
open PathCentrality PathCentrality.RegularPaths
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R}

/-- The genuine natural section puts the moving radius group in any moving orbit span. -/
theorem moving_le_hatV [Finite M] (source : LocalSource L R)
    (earlier : Earlier R geometry) {a c : Vertex R} (ha : color R a = false)
    (hc : c ∈ Escape.movingNeighbors geometry a) : Vcirc R a ≤ hatV R a c := by
  obtain ⟨s⟩ := earlier.natural_section a ha
  rw [hatV_eq_conjugatesIn]
  exact Escape.Initial.Natural.moving_generation_of_naturalSection source geometry
    (by rw [earlier.distance]; decide) a ha s c hc

/-- Reverse the neighboring critical window to make the previous M-vertex moving. -/
theorem backward_moving [Finite M] (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (e : ExtendedPath geometry a) {i : ℕ}
    (hi : Even i) (hi2 : 2 ≤ i) (hi10 : i ≤ 10) :
    e.walk.getVert (i - 2) ∈ Escape.movingNeighbors geometry (e.walk.getVert i) := by
  have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  let p := (e.window (i - 2) he (by omega)).reverse common
  have hlen : e.walk.length = 16 := by rw [e.length_eq, earlier.distance]
  apply Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
    source common.large_distance p.start_color p.critical
  constructor
  · rw [SimpleGraph.dist_comm]
    rw [segment_distance e (by omega) (by omega)]
    omega
  · rw [earlier.distance, SimpleGraph.dist_comm (u := e.walk.getVert (i - 2 + 8))
      (v := e.walk.getVert i), SimpleGraph.dist_comm (u := e.walk.getVert (i - 2 + 8))
      (v := e.walk.getVert (i - 2)), segment_distance e (by omega) (by omega),
      segment_distance e (by omega) (by omega)]
    omega

/-- The supplied local turn transfers movement from the previous to the next M-vertex. -/
theorem forward_moving [Finite M] (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (e : ExtendedPath geometry a) {i : ℕ}
    (hi : Even i) (hi2 : 2 ≤ i) (hi10 : i ≤ 10) :
    e.walk.getVert (i + 2) ∈ Escape.movingNeighbors geometry (e.walk.getVert i) := by
  obtain ⟨g, hg, ht⟩ := e.turns i hi hi2 (by rw [earlier.distance]; omega)
  have hback := backward_moving source common earlier e hi hi2 hi10
  have hca : color R (e.walk.getVert i) = false :=
    path_color e hi (by rw [e.length_eq, earlier.distance]; omega)
  have hact := Escape.Propagation.Rigidity.moving_of_local_act common.large_distance
    (e.walk.getVert i) (e.walk.getVert (i - 2)) hca hback g⁻¹
    ((stabilizer R (e.walk.getVert i)).inv_mem hg)
  rw [← ht, ← act_mul, mul_inv_cancel, act_one] at hact
  exact hact

/-- The first five even centers have the required moving-span inclusion. -/
theorem path_moving_le_hatV [Finite M] (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (e : ExtendedPath geometry a) {i : ℕ}
    (hi : Even i) (hi2 : 2 ≤ i) (hi10 : i ≤ 10) :
    Vcirc R (e.walk.getVert i) ≤ hatV R (e.walk.getVert i) (e.walk.getVert (i + 2)) :=
  moving_le_hatV source earlier
    (path_color e hi (by rw [e.length_eq, earlier.distance]; omega))
    (forward_moving source common earlier e hi hi2 hi10)


/-- At the far end, use the forward critical window directly; no extra turn is assumed. -/
theorem forward_moving_of_six_le [Finite M] (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (e : ExtendedPath geometry a) {i : ℕ}
    (hi : Even i) (hi6 : 6 ≤ i) (hi14 : i ≤ 14) :
    e.walk.getVert (i + 2) ∈ Escape.movingNeighbors geometry (e.walk.getVert i) := by
  have he : Even (i - 6) := by rw [Nat.even_iff] at hi ⊢; omega
  let p := e.window (i - 6) he (by omega)
  have hlen : e.walk.length = 16 := by rw [e.length_eq, earlier.distance]
  have hend : i - 6 + geometry.b R = i + 2 := by rw [earlier.distance]; omega
  have hm : e.walk.getVert (i - 6 + geometry.b R) ∈
      Escape.movingNeighbors geometry (e.walk.getVert i) := by
    apply Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
      source common.large_distance p.start_color p.critical
    constructor
    · rw [hend, segment_distance e (by omega) (by omega)]
      omega
    · rw [hend, segment_distance e (by omega) (by omega),
        segment_distance e (by omega) (by omega)]
      omega
  simpa only [hend] using hm

/-- Every even center with two-sided clearance in the extended path has the moving-span inclusion. -/
theorem path_moving_le_hatV_all [Finite M] (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (e : ExtendedPath geometry a) {i : ℕ}
    (hi : Even i) (hi2 : 2 ≤ i) (hi14 : i ≤ 14) :
    Vcirc R (e.walk.getVert i) ≤ hatV R (e.walk.getVert i) (e.walk.getVert (i + 2)) := by
  by_cases h : i ≤ 10
  · exact path_moving_le_hatV source common earlier e hi hi2 h
  · exact moving_le_hatV source earlier
      (path_color e hi (by rw [e.length_eq, earlier.distance]; omega))
      (forward_moving_of_six_le source common earlier e hi (by omega) hi14)

/-- The common edge puts the local Z-layer in the first orbit layer. -/
theorem Z_le_hatV [Finite M] {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) : Z R a ≤ hatV R a c := by
  rw [hatV_eq_conjugatesIn]
  exact Escape.Initial.Natural.Z_le_conjugatesIn_of_dist_two a c ha hd

/-- The lower inclusion in (4.5.3)(i), at every interior even center of the actual extended path. -/
theorem path_moving_join_Z_le_hatV [Finite M] (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (e : ExtendedPath geometry a) {i : ℕ}
    (hi : Even i) (hi2 : 2 ≤ i) (hi14 : i ≤ 14) :
    Vcirc R (e.walk.getVert i) ⊔ Z R (e.walk.getVert i) ≤
      hatV R (e.walk.getVert i) (e.walk.getVert (i + 2)) := by
  have hlen : e.walk.length = 16 := by rw [e.length_eq, earlier.distance]
  refine sup_le (path_moving_le_hatV_all source common earlier e hi hi2 hi14) ?_
  exact Z_le_hatV (path_color e hi (by omega))
    (by rw [segment_distance e (by omega) (by omega)]; omega)

/-- The actual (4.4) inputs supply the span witness used by the numerical H-bound consumer. -/
theorem exists_moving_span [Finite M] (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (ha : color R a = false) :
    ∃ c, color R c = false ∧ (cosetGraph R).dist a c = 2 ∧
      Vcirc R a ≤ localZSpan R c a := by
  obtain ⟨e⟩ := earlier.extended a ha
  have hlen : e.walk.length = 16 := by rw [e.length_eq, earlier.distance]
  refine ⟨e.walk.getVert 6, path_color e (by decide) (by omega), ?_, ?_⟩
  · simpa only [e.center_eq] using
      (segment_distance e (i := 4) (j := 6) (by omega) (by omega))
  · have hh := path_moving_join_Z_le_hatV source common earlier e (i := 4) (by decide)
      (by omega) (by omega)
    simpa only [e.center_eq, hatV] using (le_sup_left.trans hh :
      Vcirc R (e.walk.getVert 4) ≤ hatV R (e.walk.getVert 4) (e.walk.getVert 6))



end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
