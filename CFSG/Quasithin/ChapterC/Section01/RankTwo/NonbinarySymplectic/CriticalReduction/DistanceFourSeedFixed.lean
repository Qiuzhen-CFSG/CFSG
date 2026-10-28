module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFixedEdge
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexOrbit

/-!
# Full seed displacement in the fixed-radius large-back branch

For the literal forward edge a--t--e, the full kernel Q_t acts quadratically
on both moving layers. The full Z decomposition retains the entire fixed
attachment, so its displacement agrees with the moving-layer displacement.
That displacement lies in the central omega of Q_t, hence in both incident
seeds and in each opposite B-subgroup.

Both conclusions use the same original path, compatible large backward path,
and edge t. No prescribed backward orbit or supplied seed-fixedness is used.
This is the seed-fixedness step of MS93 (5.12)(2), printed p.926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem quadratic_seed_displacement_le_edge
    {geometry : Geometry d.radical} (hb : 4 ≤ geometry.b d.radical)
    {e t : Vertex d.radical} (he : color d.radical e=false)
    (het : Adjacent d.radical e t)
    (hquad : ⁅⁅U d.radical e,Q d.radical t⁆,Q d.radical t⁆=⊥) :
    ⁅Z d.radical e,Q d.radical t⁆ ≤ Z d.radical t := by
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical het
    cases ht : color d.radical t <;> simp_all
  have hTS : Q d.radical t ≤ stabilizer d.radical e :=
    fun _ hx => hx.2 e (adjacent_symm d.radical het)
  have hZX : Z d.radical e ≤ X d.radical e :=
    geometry.omega_bound e he (by
      rw [geometry.distance_constant e he]
      exact lt_of_lt_of_le (by decide : 0 < 4) hb)
  have hcommZ : ⁅Z d.radical e,Q d.radical t⁆ ≤ Z d.radical e :=
    le_normalizer_iff_commutator_le_left.mp (hTS.trans (Z_normalized d.radical e))
  have hcommQ : ⁅Z d.radical e,Q d.radical t⁆ ≤ Q d.radical t :=
    hcommZ.trans (hZX.trans ((omegaCenter_le _).trans (Q_le_adjacent_h d.radical ht het)))
  have hcommC : ⁅Z d.radical e,Q d.radical t⁆ ≤
      centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [h.replacement_Z_commutator_eq_U d geometry hb he _ hTS]
    exact commutator_eq_bot_iff_le_centralizer.mp hquad
  intro x hx
  rw [Z,if_neg (by rw [ht]; decide)]
  exact mem_omegaCenter_iff.mpr
    ⟨hcommQ hx,(mem_omegaCenter_iff.mp (hZX (hcommZ hx))).2.1,hcommC hx⟩

/-- The actual fixed-radius, large-back branch fixes both full forward seeds
modulo the opposite B-subgroups, using the same literal edge kernel. -/
theorem Input.replacement_distance_four_seed_fixed
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlarge : Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let e := path.walk.getVert 2
    let t := path.walk.getVert 1
    ⁅Z d.radical e,Q d.radical t⁆ ≤ B d.radical a (geometry.Z_normal a) ∧
      ⁅Z d.radical a,Q d.radical t⁆ ≤ B d.radical e (geometry.Z_normal e) := by
  let e := path.walk.getVert 2
  let t := path.walk.getVert 1
  have hl := path.length_eq_b
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical a t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have het : Adjacent d.radical e t := adjacent_symm _
    ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  obtain ⟨_,_,hquadA,hquadE,_,_⟩ :=
    h.replacement_distance_four_fixed_edge d path hb back hmid hlarge hfixed
  refine ⟨?_,?_⟩
  · exact (quadratic_seed_displacement_le_edge h d hb4 he het hquadE).trans
      ((adjacent_Z_le d.radical path.start_color hat).trans
        (Escape.EdgeTransfer.Z_le_B (by omega : 2 < geometry.b d.radical) a path.start_color))
  · exact (quadratic_seed_displacement_le_edge h d hb4 path.start_color hat hquadA).trans
      ((adjacent_Z_le d.radical he het).trans
        (Escape.EdgeTransfer.Z_le_B (by omega : 2 < geometry.b d.radical) e he))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
