module
public import Theory.SpecificGroups.SymplecticFour.SecondaryPreimage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreReconstruction.OriginalSecondary

/-!
# The secondary flag in the original critical geometry

Quadratic action of Q_a on the opposite elementary layer puts its commutator
inside X_a. Conversely, actual flag coordinates on Z_z and placement of the
fixed point in the common edge layer turn a central secondary orbit into
quadratic action. Both statements keep the original free-amalgam subgroups.

Source: MS93 (3.6), printed p.871. These are local implications; their use
requires the original distance and simultaneous flag marking.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}

theorem critical_commutator_le_X_of_quadratic
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : geometry.b R = 2)
    (hq : ⁅⁅Z R z,Q R a⁆,Q R a⁆ = ⊥) : ⁅Z R z,Q R a⁆ ≤ X R a := by
  have hdist : (cosetGraph R).dist a z = 2 :=
    path.critical.1.trans ((geometry.distance_constant a path.start_color).trans hb)
  have hzS : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  have hQZ : Q R a ≤ normalizer (Z R z) :=
    (Q_le_stabilizer_of_dist_two R a z path.start_color hdist).trans (Z_normalized R z)
  have hCQ : ⁅Z R z,Q R a⁆ ≤ Q R a :=
    le_normalizer_iff_commutator_le_right.mp (hzS.trans (Q_normalized R a))
  have hCZ : ⁅Z R z,Q R a⁆ ≤ Z R z :=
    le_normalizer_iff_commutator_le_left.mp hQZ
  let := geometry.Z_elementary (show 0 < geometry.b R by omega) z path.end_color
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hCQ hx,
    elemPow_eq_one_of_isElementaryAbelian x (hCZ hx),
    (commutator_eq_bot_iff_le_centralizer.mp hq) hx⟩

theorem critical_quadratic_of_secondary_flag
    {M F : Type*} [Group M] [Finite M] [Field F]
    {R : Subgroup M} {geometry : Geometry R} {a t z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : geometry.b R = 2) (hzt : Adjacent R z t)
    (φ : Z R z ≃* Multiplicative (Theory.SpecificGroups.SymplecticFour.Vector F))
    (α : Q R a →* Theory.SpecificGroups.SymplecticFour.Sp F)
    (hα : ∀ p : Q R a, α p ∈ Theory.SpecificGroups.SymplecticFour.unipotent)
    (hact : ∀ (p : Q R a) (w : Z R z) (hw : p.val*w.val*p.val⁻¹ ∈ Z R z),
      φ ⟨p.val*w.val*p.val⁻¹,hw⟩ = Multiplicative.ofAdd (α p • (φ w).toAdd))
    (hpoint : ∀ w : Z R z, (φ w).toAdd ∈ Theory.SpecificGroups.SymplecticFour.point F →
      (w:FreeAmalgam R) ∈ Z R t)
    (hcomm : ⁅secondaryOrbit R a (secondarySeed R a t z),Q R a⁆ = ⊥) :
    ⁅⁅Z R z,Q R a⁆,Q R a⁆ = ⊥ := by
  have hdist : (cosetGraph R).dist a z = 2 :=
    path.critical.1.trans ((geometry.distance_constant a path.start_color).trans hb)
  have hn : Q R a ≤ normalizer (Z R z) :=
    (Q_le_stabilizer_of_dist_two R a z path.start_color hdist).trans (Z_normalized R z)
  refine Theory.SpecificGroups.SymplecticFour.quadratic_of_central_secondary_preimage
    (Z R z) (Q R a) (Z R t) hn φ α hα hact hpoint ?_
  have hseed : secondarySeed R a t z ≤ secondaryOrbit R a (secondarySeed R a t z) := by
    change secondarySeed R a t z ≤ conjugatesIn (secondarySeed R a t z) (stabilizer R a)
    rw [conjugatesIn_eq_conjugateSpan]
    exact le_conjugateSpanBy _ _
  have hpos : 0 < geometry.b R := by omega
  let := geometry.Z_elementary hpos z path.end_color
  have hZn : Z R z ≤ normalizer (Z R t) :=
    (le_centralizer_iff.mp ((edge_Z_le_endpoint R path.end_color hzt).trans
      (Z R z).le_centralizer)).trans (Subgroup.centralizer_le_normalizer _)
  have hpre : commutatorPreimage (Z R z) (Q R a) (Z R t) ≤ secondarySeed R a t z :=
    (secondarySeed_greatest R geometry path.end_color hzt hpos).2.2 _
      (commutatorPreimage_le _ _ _) (commutator_commutatorPreimage_le _ _ _ hZn)
  apply le_bot_iff.mp
  exact (commutator_mono (hpre.trans hseed) le_rfl).trans_eq hcomm
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction

