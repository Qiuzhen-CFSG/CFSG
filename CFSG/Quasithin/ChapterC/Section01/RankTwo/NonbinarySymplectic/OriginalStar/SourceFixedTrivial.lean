module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourComplete
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCore
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic

/-!
# Triviality of the original moving fixed attachment

Source (4) identifies the complete fixed attachments at every original
critical pair. The common attachment lies in the critical commutator. At
any other neighbor of the midpoint, either it equals that neighbor's
attachment or both critical centers lie in its core. In the latter case
their commutator lies in the core Frattini subgroup, hence in its full
component-fixed factor. Thus the common attachment centralizes all
neighboring components. Characteristicity of the original amalgam then
forces it to vanish.

This is the argument referred to after MS93 (3.7)(6), printed p.876, in
the last paragraph of (3.6), printed p.872. The already proved Frattini
fixedness permits the argument before using the whole-core decomposition.
All groups belong to the original radical, with its given quotient marking.
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
include h hinner

omit [Finite F] [CharP F 2] in
private theorem edge_center_fixed_by_neighbors_eq_bot
    {a t : Vertex R} (ha : color R a=false)
    (hat : Adjacent R a t)
    (A : Subgroup (FreeAmalgam R)) (hAZ : A ≤ Z R t)
    (hAC : ∀ v : Vertex R, Adjacent R v t →
      A ≤ centralizer (Ltilde R v : Set (FreeAmalgam R))) : A=⊥ := by
  let W := ⨆ v : Vertex R, ⨆ (_ : Adjacent R v t), Ltilde R v
  let N := Z R t ⊓ centralizer (W : Set (FreeAmalgam R))
  have hAN : A ≤ N := le_inf hAZ (le_centralizer_iff.mp (iSup_le fun v => iSup_le fun hv =>
    le_centralizer_iff.mp (hAC v hv)))
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (ha.trans he.symm)
  have hZQ : Z R t ≤ Q R t := by
    rw [show Z R t=omegaCenter (Q R t) by simp [Z,ht,edgeOmega]]
    exact omegaCenter_le _
  have hZC : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [show Z R t=omegaCenter (Q R t) by simp [Z,ht,edgeOmega]]
    exact fun y hy => (mem_omegaCenter_iff.mp hy).2.2
  have hNS : N ≤ stabilizer R a ⊓ stabilizer R t :=
    le_inf ((inf_le_left.trans hZQ).trans (original_edge_le_stabilizer R hat))
      ((inf_le_left.trans hZQ).trans (fun _ hx => hx.1))
  have hNC : N ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
    rw [original_stabilizer_eq_residual_sup_core h hinner ha]
    apply le_centralizer_iff.mp
    apply sup_le
    · exact le_centralizer_iff.mp (inf_le_right.trans
        (centralizer_le (show Ltilde R a ≤ W from
          le_iSup_of_le a (le_iSup_of_le hat le_rfl))))
    · exact le_centralizer_iff.mp ((inf_le_left.trans hZC).trans (centralizer_le (original_core_le_edge R ha hat)))
  have hWN : stabilizer R t ≤ normalizer (W : Set (FreeAmalgam R)) := by
    apply le_normalizer_iff.mpr
    intro x hx w hw
    have hxT : act R x⁻¹ t=t := (stabilizer R t).inv_mem hx
    have hm : W.map (MulAut.conj x).toMonoidHom ≤ W := by
      dsimp only [W]
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro v
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro hv
      have hvT : Adjacent R (act R x⁻¹ v) t := by
        simpa only [hxT] using (adjacent_act_iff R x⁻¹ v t).mpr hv
      have he := Ltilde_act R x⁻¹ v
      rw [inv_inv] at he
      rw [←he]
      exact le_iSup_of_le _ (le_iSup_of_le hvT le_rfl)
    exact hm (mem_map_of_mem _ hw)
  have hNt : stabilizer R t ≤ normalizer (N : Set (FreeAmalgam R)) :=
    (le_inf (Z_normalized R t)
      (hWN.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hNb : N=⊥ := no_common_normal_at_edge R h.characteristic
    a t ha hat N hNS
    (normal_subgroupOf_of_le_normalizer
      ((le_centralizer_iff.mp hNC).trans (Subgroup.centralizer_le_normalizer _)))
    (normal_subgroupOf_of_le_normalizer hNt)
  exact le_bot_iff.mp (hAN.trans hNb.le)

include hshort hnsyl

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
  exact Or.inl (original_source_four_fixed_attachments h hshort hinner hnsyl g hb p hat hvt)

omit hinner hnsyl in
private theorem core_derived_le_fixed
    {a : Vertex R} (ha : color R a=false) :
    ⁅Q R a,Q R a⁆ ≤ fixedCore R a := by
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 (Q R a)) := ⟨Q_isPGroup R
    h.radical.isPGroup h.radical.twoCore_le a ha⟩
  have hh := map_mono (f := (Q R a).subtype)
    (commutator_le_frattini_of_isPGroup (R := Q R a) (p := 2))
  have hd : ⁅Q R a,Q R a⁆ ≤
      (frattini (Q R a)).map (Q R a).subtype := by
    simpa only [commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
  exact hd.trans (original_short_frattini_le_fixedCore h hshort ha)

private theorem critical_fixed_attachment_le_commutator
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≤ ⁅Z R a,Z R z⁆ := by
  by_cases hc : (2^n)^2 ≤ (Q R z).relIndex (Z R a)
  · rw [original_source_four_fixed_attachments h hshort hinner hnsyl g hb path hat hzt]
    exact (original_source_four_large_plane_cover h hshort hinner hnsyl g hb path hat hzt hc).2.2.2.trans
      (commutator_mono le_rfl (U_le_Z z))
  · obtain ⟨he,_⟩ := h.original_small_critical_indices_eq_field path (by omega)
      (by rw [h.field_card]; exact lt_of_not_ge hc)
    exact (original_critical_fixed_layer_index h hshort hinner path hb hat hzt
      (he.trans h.field_card)).1

private theorem critical_fixed_attachment_eq_bot
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))=⊥ := by
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  have he := original_source_four_fixed_attachments h hshort hinner hnsyl g hb path hat hzt
  have hAR := critical_fixed_attachment_le_commutator h hshort hinner hnsyl g hb path hat hzt
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
  rcases fixed_attachments_eq_or_contained h hshort hinner hnsyl g hb path.start_color hat hvt with hA | hQa
  · exact hA.le.trans inf_le_right
  rcases fixed_attachments_eq_or_contained h hshort hinner hnsyl g hb path.end_color hzt hvt with hA | hQz
  · exact (he.trans hA).le.trans inf_le_right
  exact (hAR.trans ((commutator_mono hQa hQz).trans (core_derived_le_fixed h hshort hv))).trans inf_le_right

/-- The entire moving fixed attachment on the original nonsylow star is
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
  exact critical_fixed_attachment_eq_bot h hshort hinner hnsyl g hb path hat hzt

/-- The original moving group and the full component-fixed core are disjoint. -/
theorem original_source_moving_disjoint_fixedCore
    (g : Geometry R) (hb : g.b R=2)
    {a : Vertex R} (ha : color R a=false) :
    Disjoint (U R a) (fixedCore R a) := by
  apply disjoint_iff_inf_le.mpr
  exact (inf_le_inf_left _ (show fixedCore R a ≤
    centralizer (Ltilde R a : Set (FreeAmalgam R)) from inf_le_right)).trans
    (original_source_moving_fixed_attachment_eq_bot h hshort hinner hnsyl g hb ha).le

/-- At a field-sized original critical pair, the critical commutator has
order q before quotienting by the full fixed core. -/
theorem original_source_field_critical_commutator_order
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) :
    Nat.card (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R))=2^n := by
  have hi := (original_critical_fixed_layer_index h hshort hinner path hb hat hzt hcritical).2
  rw [original_source_moving_fixed_attachment_eq_bot h hshort hinner hnsyl g hb path.start_color,
    relIndex_bot_left] at hi
  exact hi

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
