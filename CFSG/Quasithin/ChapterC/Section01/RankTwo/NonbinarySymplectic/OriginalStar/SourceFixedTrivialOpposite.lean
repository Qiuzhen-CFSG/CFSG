module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFixedTrivialQuotient
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFixedTrivialQuotient
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCore
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic

/-!
# The original fixed core against the opposite moving group

At a field-sized critical pair, the full first core acts on the opposite
center through the first center. Its fixed factor consequently moves the
opposite center inside the critical commutator and inside itself. The
proved disjointness of the first moving and fixed factors makes this
movement trivial. Thus the full first fixed core centralizes the opposite
center and lies in the opposite core.

Its intersection with the opposite moving group lies in the midpoint
omega-center and centralizes the entire first stabilizer. These are
unquotiented statements with the complete fixed factor retained. They do
not assert that this opposite intersection is trivial.

Source: MS93 (3.7), printed pp.876–877, before the opposite fixed-factor
intersection in the final point-parabolic argument.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include h hshort hinner hnsyl

/-- The full fixed core centralizes the opposite critical center. -/
theorem original_source_fixedCore_centralizes_opposite
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) :
    fixedCore R a ≤ centralizer (Z R z : Set (FreeAmalgam R)) := by
  have hinside := (original_source_three_of_field_critical h hshort hinner hnsyl g hb path hat hzt hcritical).1
  have hZzT : Z R z ≤ Q R t :=
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0<g.b R; omega)).trans
        (omegaCenter_le _)).trans (original_core_le_edge R path.end_color hzt)
  have hZaS : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  have hmove : ⁅Z R z,fixedCore R a⁆ ≤ ⁅Z R a,Z R z⁆ := by
    rw [commutator_comm (Z R a)]
    apply commutator_le_moving_of_inner_mod_centralizer
      (Z R z) (Z R a) (fixedCore R a) (hZaS.trans (Z_normalized R z))
    exact inf_le_left.trans (hinside.trans (sup_le_sup_left
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R z path.end_color))) _))
  have hW : ⁅Z R a,Z R z⁆ ≤ U R a :=
    (original_critical_paired_fixed_layers h hshort hinner path hb hat hzt hcritical).2.2.1.trans inf_le_left
  have hD : ⁅Z R z,fixedCore R a⁆ ≤ fixedCore R a :=
    le_normalizer_iff_commutator_le_right.mp (hZzT.trans (original_fixedCore_normalized hat))
  have hzero : ⁅Z R z,fixedCore R a⁆=⊥ := le_bot_iff.mp
    ((le_inf (hmove.trans hW) hD).trans
      (disjoint_iff.mp (original_source_moving_disjoint_fixedCore h hshort hinner hnsyl g hb path.start_color)).le)
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)

/-- The full first fixed core belongs to the opposite core. -/
theorem original_source_fixedCore_le_opposite_core
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) : fixedCore R a ≤ Q R z := by
  rw [←original_stabilizer_centralizer_moving_eq_core h path.end_color]
  exact le_inf
    ((inf_le_left.trans (original_core_le_edge R path.start_color hat)).trans
      (original_edge_le_stabilizer R hzt))
    ((original_source_fixedCore_centralizes_opposite h hshort hinner hnsyl g hb path hat hzt hcritical).trans
      (centralizer_le (U_le_Z z)))

/-- The opposite fixed/moving overlap belongs to the actual midpoint center. -/
theorem original_source_opposite_fixed_overlap_le_edge
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) :
    fixedCore R a ⊓ U R z ≤ Z R t := by
  have hZ : fixedCore R a ⊓ U R z ≤ Z R a :=
    (le_inf (inf_le_right.trans (U_le_Z z)) (inf_le_left.trans inf_le_left)).trans
      (field_critical_overlap_le_Z h hshort hinner hnsyl g hb path hat hzt hcritical)
  apply (le_inf (hZ.trans (g.omega_bound a path.start_color (by
    rw [g.distance_constant a path.start_color]; change 0<g.b R; omega)))
    (inf_le_left.trans inf_le_right)).trans
  exact original_fixed_X_le_edge h hinner path.start_color hat

/-- The opposite fixed/moving overlap centralizes the entire first stabilizer. -/
theorem original_source_opposite_fixed_overlap_centralizes_stabilizer
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) :
    fixedCore R a ⊓ U R z ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
  have hZ : fixedCore R a ⊓ U R z ≤ Z R a :=
    (original_source_opposite_fixed_overlap_le_edge h hshort hinner hnsyl g hb path hat hzt hcritical).trans
      (Sp4Four.edge_Z_le_endpoint R path.start_color hat)
  rw [original_stabilizer_eq_residual_sup_core h hinner path.start_color]
  apply le_centralizer_iff.mp
  exact sup_le
    (le_centralizer_iff.mp (inf_le_left.trans inf_le_right))
    (le_centralizer_iff.mp (hZ.trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a path.start_color))))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
