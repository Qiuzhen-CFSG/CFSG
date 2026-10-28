module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSeedFixedTransfer

/-!
# The actual large-back commutator in the nonfixed radius branch

Both ends of the compatible backward path lie in the radius at its literal
midpoint a. Radius centrality puts their commutator in X_a and makes Q_a
centralize it. The large backward image then forces [Z_e,Q_a] into that
commutator by the actual escaping-actor theorem. If the radius commutator
is not in D_a, midpoint fixed-core transfer proves this critical commutator
is not in D_a either.

This supplies the nonfixed commutator step in MS93 (5.12)(2), printed p.925.
The nonfixed branch is retained, and no distance-four exclusion is claimed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- In the actual large-back branch, failure of radius fixedness forces
failure of fixedness for the full backward critical commutator. -/
theorem Input.replacement_distance_four_nonfixed_critical_commutator
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlarge : Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (hnot : ¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let C := ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆
    C ≤ X d.radical a ∧
      ⁅Z d.radical (path.walk.getVert 2),Q d.radical a⁆ ≤ C ∧
      ¬ C ≤ fixedCore d.radical a := by
  let e := path.walk.getVert 2
  let C := ⁅Z d.radical u,Z d.radical e⁆
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hb0 : 0 < geometry.b d.radical := by omega
  have hl := path.length_eq_b
  have hbl := back.length_eq_b
  have hlarge₂ : Nat.card F^2 ≤ (Q d.radical e).relIndex (Z d.radical u) := by
    by_contra! hs
    have hi := (h.replacement_small_critical_indices_eq_field d back hb0 hs).1
    exact (ne_of_gt hlarge) hi
  have hae : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hua : (cosetGraph d.radical).dist u a=2 := by
    rw [←hmid]
    exact back.dist_start (by omega)
  have huV : Z d.radical u ≤ V d.radical a :=
    le_iSup_of_le u (le_iSup_of_le hua.le le_rfl)
  have heV : Z d.radical e ≤ V d.radical a :=
    le_iSup_of_le e (le_iSup_of_le (by rw [SimpleGraph.dist_comm,hae] :
      (cosetGraph d.radical).dist e a ≤ 2) le_rfl)
  have hCder : C ≤ ⁅V d.radical a,V d.radical a⁆ := commutator_mono huV heV
  have hCX : C ≤ X d.radical a := hCder.trans
    (h.replacement_radius_commutator_bounds d geometry hb4 path.start_color u e).1
  have hQC : Q d.radical a ≤ centralizer (C : Set (FreeAmalgam d.radical)) :=
    (Q_le_centralizer_X d.radical a).trans (centralizer_le hCX)
  have hseed : ⁅Z d.radical e,Q d.radical a⁆ ≤ C := by
    by_contra hbad
    have hs := h.replacement_critical_index_lt_square_of_escape d back hb0
      (Q d.radical a) (Q_le_stabilizer_of_dist_two d.radical a e path.start_color hae)
      hQC hbad
    exact (not_lt_of_ge hlarge₂) hs
  refine ⟨hCX,hseed,?_⟩
  intro hCD
  apply hnot
  exact (h.replacement_distance_four_midpoint_fixed_iff_radius_fixed_of_large_path
    d path hb back hlarge₂).mp (hseed.trans hCD)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
