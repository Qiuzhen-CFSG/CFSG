module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.Attachments
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFixedTrivial
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic

/-!
# Triviality of the moving fixed attachment on the original Sylow star

Complete fixed attachments agree at every critical pair and lie in the
critical commutator. At each other midpoint neighbor, either the attachment
agrees or both critical centers lie in its core. Their commutator then lies
in the core Frattini subgroup and hence its full component-fixed factor.
The attachment therefore centralizes every neighboring component, and the
original edge characteristic condition forces it to vanish.

The internal imports intentionally reuse the generic original-edge
characteristic argument and core-derived fixedness. The full fixed core is
retained. Source: the argument after MS93 (3.7)(6), printed p.876, referring
to the last paragraph of (3.6), printed p.872.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include h hshort hinner hsy

private theorem fixed_attachments_eq_or_contained
    (g : Geometry R) (hb : g.b R=2)
    {a v t : Vertex R} (ha : color R a=false)
    (hat : Adjacent R a t) (hvt : Adjacent R v t) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      U R v ⊓ centralizer (Ltilde R v : Set (FreeAmalgam R)) ∨
      Z R a ≤ Q R v := by
  by_cases hin : Z R a ≤ Q R v
  · exact Or.inr hin
  have hneq : a≠v := by
    intro he
    subst v
    exact hin ((g.omega_bound a ha (by
      rw [g.distance_constant a ha]; change 0<g.b R; omega)).trans (omegaCenter_le _))
  have hd : (cosetGraph R).dist a v=2 :=
    Escape.Propagation.neighbor_distance_two ha hat hvt hneq
  let p : CriticalPath R g a v := CriticalPath.ofPair ha
    ⟨by rw [hd,g.distance_constant a ha]; exact hb.symm,hin⟩
  exact Or.inl (original_source_four_fixed_attachments h hshort hinner hsy g hb p hat hvt)

private theorem critical_fixed_attachment_le_commutator
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≤ ⁅Z R a,Z R z⁆ := by
  exact (original_critical_fixed_layer_index h hshort hinner path hb hat hzt
    (original_critical_indices_eq_field_of_full_sylow h hshort hinner hsy path hb hat hzt).1).1

private theorem critical_fixed_attachment_eq_bot
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))=⊥ := by
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  have he := original_source_four_fixed_attachments h hshort hinner hsy g hb path hat hzt
  have hAR := critical_fixed_attachment_le_commutator h hshort hinner hsy g hb path hat hzt
  apply edge_center_fixed_by_neighbors_eq_bot h hinner path.start_color hat A
    ((inf_le_inf_right _ ((U_le_Z a).trans (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0<g.b R; omega)))).trans
      (original_fixed_X_le_edge h hinner path.start_color hat))
  intro v hvt
  have hv : color R v=false := by
    have ht : color R t=true := by
      apply Bool.eq_true_of_not_eq_false
      intro hh
      exact adjacent_color_ne R hat (path.start_color.trans hh.symm)
    cases hv : color R v
    · rfl
    · exact (adjacent_color_ne R hvt (hv.trans ht.symm)).elim
  rcases fixed_attachments_eq_or_contained h hshort hinner hsy g hb path.start_color hat hvt with hA | hQa
  · exact hA.le.trans inf_le_right
  rcases fixed_attachments_eq_or_contained h hshort hinner hsy g hb path.end_color hzt hvt with hA | hQz
  · exact (he.trans hA).le.trans inf_le_right
  exact (hAR.trans ((commutator_mono hQa hQz).trans (core_derived_le_fixed h hshort hv))).trans inf_le_right

/-- The entire moving fixed attachment on the original Sylow star is
trivial. The complete fixed core remains present. -/
theorem original_source_moving_fixed_attachment_eq_bot
    (g : Geometry R) (hb : g.b R=2)
    {a : Vertex R} (ha : color R a=false) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))=⊥ := by
  obtain ⟨z,hz⟩ := criticalPair_exists R a (g.exists_critical a ha)
  let path : CriticalPath R g a z := CriticalPath.ofPair ha hz
  have hd : (cosetGraph R).dist a z=2 :=
    path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two R a z hd
  exact critical_fixed_attachment_eq_bot h hshort hinner hsy g hb path hat hzt

/-- The original moving group and the full component-fixed core are disjoint. -/
theorem original_source_moving_disjoint_fixedCore
    (g : Geometry R) (hb : g.b R=2)
    {a : Vertex R} (ha : color R a=false) :
    Disjoint (U R a) (fixedCore R a) := by
  apply disjoint_iff_inf_le.mpr
  exact (inf_le_inf_left _ (show fixedCore R a ≤
    centralizer (Ltilde R a : Set (FreeAmalgam R)) from inf_le_right)).trans
    (original_source_moving_fixed_attachment_eq_bot h hshort hinner hsy g hb ha).le

/-- At a field-sized original critical pair, the critical commutator has
order q before quotienting by the full fixed core. -/
theorem original_source_field_critical_commutator_order
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    Nat.card (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R))=2^n := by
  have hi := (original_critical_fixed_layer_index h hshort hinner path hb hat hzt
    (original_critical_indices_eq_field_of_full_sylow h hshort hinner hsy path hb hat hzt).1).2
  rw [original_source_moving_fixed_attachment_eq_bot h hshort hinner hsy g hb path.start_color,
    relIndex_bot_left] at hi
  exact hi

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
