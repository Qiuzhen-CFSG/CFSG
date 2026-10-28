module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TrappedTwist

/-!
# The selected distance-four commutator cannot be central at both source vertices

Keep the actual second-selector marking v = a^g with g in G_u. If the
failed-comparison commutator were fixed by both G_a and G_u, conjugation by
this same g would make it fixed by G_v. It is a commutator on a subgroup of
the full U_v, acted on by the actual X_e intersect Q_u inside G_v. The
full-cover fixed-commutator theorem therefore makes it trivial, contrary
to its proved order q.

This is the final implication in the first case of MS93 (5.12)(1), p.925.
It requires neither v to a criticality nor a conjugacy between the first
backward vertex u and the original midpoint e. Producing both source
centralities from the same actual selectors remains a separate duty.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- With the literal second-selector conjugator, failure of the comparison
precludes simultaneous centrality at the two original source vertices. -/
theorem Input.replacement_distance_four_comparison_not_two_centers
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical u)
    (hga : act d.radical g a=v)
    (hbad : ¬ ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆) :
    ¬ ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ⊓
        centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical)) := by
  intro hcent
  let W := U d.radical v ⊓ Q d.radical z
  let A := X d.radical (path.walk.getVert 2) ⊓ Q d.radical u
  let D := ⁅W,A⁆
  have hDa : D ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) :=
    hcent.trans inf_le_left
  have hDu : D ≤ centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical)) :=
    hcent.trans inf_le_right
  have hDg : D.map (MulAut.conj g⁻¹).toMonoidHom=D :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hDu ((stabilizer d.radical u).inv_mem hg)))
  have hDv : D ≤ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hDa).trans
      (map_centralizer_le_centralizer_image _ _)
    change D.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer
      ((stabilizer d.radical a).map (MulAut.conj g⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
    rwa [hDg,←stabilizer_act,hga] at hh
  have hv : color d.radical v=false := by
    rw [←hga,action_preserves_color]
    exact path.start_color
  have hAS : A ≤ stabilizer d.radical v := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two u v back.start_color hv
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hut hvt))
  have hzero : ⁅A,W⁆=⊥ := (h.replacement_natural_commutator_fixed_iff d geometry (by omega)
    hv A W hAS inf_le_left).mp (by
      rw [commutator_comm]
      exact hDv.trans (centralizer_le (Ltilde_le_stabilizer v)))
  have hcard := (h.replacement_distance_four_root_comparison_of_failure d path hb back hut hvt hbad).2
  change Nat.card D=Nat.card F at hcard
  have hDbot : D=⊥ := by
    change ⁅W,A⁆=⊥
    rw [commutator_comm,hzero]
  have hone : Nat.card D=1 := card_eq_one.mpr hDbot
  have hq : 1 < Nat.card F := Finite.one_lt_card
  omega

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
