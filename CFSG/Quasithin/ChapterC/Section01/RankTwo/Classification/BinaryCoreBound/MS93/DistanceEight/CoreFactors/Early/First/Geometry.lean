module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Statements
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Moving

/-!
# Geometry and moving spans on the chosen source path

The source path is geodesic in the actual amalgam tree. Its neighboring
critical windows make one of the two adjacent M-vertices moving, and its
specified turn transfers this to the other one. This proves moving-span
containment in both directions, including the last turn at index twelve.
Existence of this path is a separate obligation; no extended path is silently
treated as a source path.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.895--896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
open PathCentrality PathCentrality.RegularPaths
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R} {a : Vertex R}

namespace SourcePath

include geometry in
/-- The chosen path is geodesic because the amalgam graph is a tree. -/
theorem shortest (p : SourcePath R a) :
    p.walk.length = (cosetGraph R).dist p.first p.last := by
  obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist p.first p.last
  have heq : p.walk = w := Subtype.mk.inj
    ((geometry.tree.isAcyclic.subsingleton_path p.first p.last).elim
      ⟨p.walk, p.isPath⟩ ⟨w, w.isPath_of_length_eq_dist hw⟩)
  rw [heq]
  exact hw

include geometry in
/-- Exact distance between ordered positions on the chosen path. -/
theorem distance (p : SourcePath R a) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 14) :
    (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert j) = j - i := by
  have hh := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk (p.shortest (geometry := geometry))
      (p.walk.isSubwalk_drop i)) ((p.walk.drop i).isSubwalk_take (j - i))
  have hmin : j - i ≤ p.walk.length - i := by rw [p.length_eq]; omega
  simpa only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
    inf_eq_left.mpr hmin, SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij] using hh.symm

/-- Even positions are M-vertices. -/
theorem even_color (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi14 : i ≤ 14) :
    color R (p.walk.getVert i) = false :=
  (walk_vertex_color p.start_color p.walk (by rw [p.length_eq]; exact hi14)).mpr hi

/-- Consecutive positions give the literal oriented edges. -/
theorem adjacent (p : SourcePath R a) {i : ℕ} (hi : i < 14) :
    Adjacent R (p.walk.getVert i) (p.walk.getVert (i + 1)) :=
  (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by rw [p.length_eq]; exact hi))

/-- A printed critical window uses the same critical-radius witness as Geometry. -/
theorem critical_pair (earlier : Earlier R geometry) (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi6 : i ≤ 6) :
    CriticalPair R (p.walk.getVert i) (p.walk.getVert (i + 8))
      (geometry.exists_critical _ (p.even_color hi (by omega))) := by
  obtain ⟨hd, hn⟩ := p.critical i hi hi6
  exact ⟨hd.trans (earlier.distance.symm.trans
    (geometry.distance_constant _ (p.even_color hi (by omega))).symm), hn⟩

private theorem previous_moving [Finite M] (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (hi8 : i ≤ 8) :
    p.walk.getVert (i - 2) ∈ Escape.movingNeighbors geometry (p.walk.getVert i) := by
  have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hp := p.critical_pair earlier he (by omega)
  have hlast : i - 2 + 8 = i + 6 := by omega
  rw [hlast] at hp
  have hr := common.critical_reverse _ (p.even_color he (by omega)) _
    (p.even_color (hi.add (by decide : Even 6)) (by omega)) hp
  apply Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
    source common.large_distance (p.even_color (hi.add (by decide : Even 6)) (by omega)) hr
  constructor
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · rw [SimpleGraph.dist_comm (u := p.walk.getVert (i + 6)),
      SimpleGraph.dist_comm (u := p.walk.getVert (i + 6)),
      p.distance (geometry := geometry) (by omega) (by omega),
      p.distance (geometry := geometry) (by omega) (by omega)]
    omega

private theorem next_moving [Finite M] (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi6 : 6 ≤ i) (hi12 : i ≤ 12) :
    p.walk.getVert (i + 2) ∈ Escape.movingNeighbors geometry (p.walk.getVert i) := by
  have he : Even (i - 6) := by rw [Nat.even_iff] at hi ⊢; omega
  have hp := p.critical_pair earlier he (by omega)
  have hlast : i - 6 + 8 = i + 2 := by omega
  rw [hlast] at hp
  apply Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
    source common.large_distance (p.even_color he (by omega)) hp
  constructor
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · rw [p.distance (geometry := geometry) (by omega) (by omega),
      p.distance (geometry := geometry) (by omega) (by omega)]
    omega

/-- Both neighbors at every interior M-vertex are moving, using all the stated turns. -/
theorem moving_neighbors [Finite M] (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (hi12 : i ≤ 12) :
    p.walk.getVert (i - 2) ∈ Escape.movingNeighbors geometry (p.walk.getVert i) ∧
      p.walk.getVert (i + 2) ∈ Escape.movingNeighbors geometry (p.walk.getVert i) := by
  obtain ⟨g, hg, ht⟩ := p.turns i hi hi2 hi12
  have hc := p.even_color hi (by omega)
  by_cases h : i ≤ 8
  · have hback := p.previous_moving source common earlier hi hi2 h
    refine ⟨hback, ?_⟩
    have hm := Escape.Propagation.Rigidity.moving_of_local_act common.large_distance
      _ _ hc hback g⁻¹ ((stabilizer R _).inv_mem hg)
    rw [← ht, ← act_mul, mul_inv_cancel, act_one] at hm
    exact hm
  · have hnext := p.next_moving source common earlier hi (by omega) hi12
    refine ⟨?_, hnext⟩
    have hm := Escape.Propagation.Rigidity.moving_of_local_act common.large_distance
      _ _ hc hnext g hg
    rwa [ht] at hm

/-- Moving generation in both directions, as used at the midpoint of (4.5.1)(i). -/
theorem moving_spans [Finite M] (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (hi12 : i ≤ 12) :
    Vcirc R (p.walk.getVert i) ≤ hatV R (p.walk.getVert i) (p.walk.getVert (i - 2)) ∧
      Vcirc R (p.walk.getVert i) ≤ hatV R (p.walk.getVert i) (p.walk.getVert (i + 2)) := by
  obtain ⟨hb, hf⟩ := p.moving_neighbors source common earlier hi hi2 hi12
  exact ⟨moving_le_hatV source earlier (p.even_color hi (by omega)) hb,
    moving_le_hatV source earlier (p.even_color hi (by omega)) hf⟩

end SourcePath
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
