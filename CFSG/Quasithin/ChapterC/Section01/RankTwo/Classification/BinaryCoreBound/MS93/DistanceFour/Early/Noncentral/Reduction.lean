module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.FailureOffender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.Obstruction

/-!
# The quotient-offender contradiction in the second MS93 (4.6.6)

If [V_a,Q_a] were central in its vertex stabilizer, conjugacy would give the
same assertion at every M-vertex. For two vertices at distance two, the
opposite kernel lies in the other stabilizer. Thus the crossing commutator
[V_a intersect Q_c,V_c] centralizes Q_a. Involution generation makes it
elementary abelian, so it lies in X_a = Z_a.

At a critical midpoint both radius groups escape the opposite kernel.
The reciprocal crossing bounds therefore give a projected offender on the
actual V_a/Z(V_a). The already proved binary commutator-form obstruction
excludes this, because centrality also makes the radius-derived subgroup
component-fixed. This proves that [V_a,Q_a] is not central in G_a.

The transfer from centrality of V_a' to centrality of [V_a,Q_a] remains an
explicit premise of the final reduction. It is the preceding edge-plane
argument on pp.903--904, not a conclusion proved by this module. The last
use of source (4.2)(ii) is discharged by `kernel_central_of_moving_fixed`,
which consumes exactly CommonFacts.normalization_transfer and edge Z-containment.

Source: Meierfrankenfeld--Stellmacher (1993), the second assertion numbered
(4.6.6), especially the final paragraph on printed p.904, using (4.6.1)--(4.6.2).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
open Initial
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem center_le_centralizer {G : Type*} [Group G] (A : Subgroup G) :
    (center A).map A.subtype ≤ centralizer (A : Set G) := by
  rintro x ⟨z, hz, rfl⟩ y hy
  exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)

private theorem opposite_kernel_local [Finite M] (a c : Vertex R)
    (ha : color R a = false) (hac : (cosetGraph R).dist a c = 2) :
    Q R a ≤ stabilizer R c := by
  obtain ⟨b, hab, hcb⟩ := exists_common_neighbor_of_dist_two R a c hac
  have hb : color R b = true := by
    have hn := adjacent_color_ne R hab
    cases hh : color R b <;> simp_all
  exact (Q_le_adjacent_h R hb hab).trans (fun _ hx => hx.2 c (adjacent_symm R hcb))

/-- Opposite kernel centrality puts the crossing commutator in the original Z-layer. -/
theorem crossing_le_Z_of_kernel_central [Finite M]
    (common : CommonFacts R source geometry)
    (a c : Vertex R) (ha : color R a = false) (hc : color R c = false)
    (hac : (cosetGraph R).dist a c = 2)
    (hcentral : ⁅V R c, Q R c⁆ ≤
      (center (stabilizer R c)).map (stabilizer R c).subtype) :
    ⁅V R a ⊓ Q R c, V R c⁆ ≤ Z R a := by
  have hca : (cosetGraph R).dist c a = 2 := by rw [SimpleGraph.dist_comm, hac]
  have hlocal := (radius_le_Q common c hc).trans (opposite_kernel_local c a hc hca)
  have hleft : ⁅V R a ⊓ Q R c, V R c⁆ ≤ V R a :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hlocal.trans (DistanceEight.V_normalized R a)))
  have hcomm : ⁅V R a ⊓ Q R c, V R c⁆ ≤ ⁅V R c, Q R c⁆ := by
    rw [commutator_comm (V R c)]
    exact commutator_mono inf_le_right le_rfl
  let := DistanceEight.elementary_commutator_of_omegaOne_eq_self
    (V R c) (Q R c) (stabilizer R c)
    ((radius_le_Q common c hc).trans (fun _ hx => hx.1))
    (DistanceEight.VBall_omegaOne R c 2) hcentral
  rw [← common.X_eq_Z a ha]
  intro x hx
  apply mem_omegaCenter_iff.mpr
  exact ⟨radius_le_Q common a ha (hleft hx),
    elemPow_eq_one_of_isElementaryAbelian x (hcomm hx),
    fun y hy => center_le_centralizer (stabilizer R c) (hcentral (hcomm hx)) y
      (opposite_kernel_local a c ha hac hy)⟩
/-- Conjugacy propagates local kernel-commutator centrality to every M-vertex. -/
theorem kernel_central_at_all (a : Vertex R) (ha : color R a = false)
    (hcentral : ⁅V R a, Q R a⁆ ≤
      (center (stabilizer R a)).map (stabilizer R a).subtype)
    (c : Vertex R) (hc : color R c = false) :
    ⁅V R c, Q R c⁆ ≤ (center (stabilizer R c)).map (stabilizer R c).subtype := by
  obtain ⟨u, hu⟩ := exists_mVertex_of_color R ha
  obtain ⟨v, hv⟩ := exists_mVertex_of_color R hc
  let g := u⁻¹ * v
  have hg : act R g a = c := by
    rw [hu, act_mVertex]
    simpa only [g, mul_inv_cancel_left] using hv.symm
  rw [← hg, V_act, Q_act, stabilizer_act,
    ← map_embeddedCenter _ _ (MulAut.conj g⁻¹).injective, ← map_commutator]
  exact map_mono hcentral

variable [Finite M]

/-- The actual radius-kernel commutator cannot be central in the vertex stabilizer. -/
theorem kernel_noncentral (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (a : Vertex R) (ha : color R a = false) :
    ¬ ⁅V R a, Q R a⁆ ≤
      (center (stabilizer R a)).map (stabilizer R a).subtype := by
  intro hcentral
  have hall := kernel_central_at_all a ha hcentral
  have hfixed : ⁅V R a, V R a⁆ ≤ fixedCore R a := by
    apply le_inf ((commutator_le_self (V R a)).trans (radius_le_Q common a ha))
    exact ((commutator_mono le_rfl (radius_le_Q common a ha)).trans hcentral).trans
      ((center_le_centralizer _).trans (centralizer_le (map_subtype_le _)))
  apply not_radiusCenterOffender_of_derived_fixed common hb a ha hfixed
  apply radiusCenterOffender_of_critical_generator_bounds common hb a ha
  intro a' c hcrit hac _
  have hc : color R c = false :=
    (color_eq_of_dist_even R a c (by rw [hac]; decide)).symm.trans ha
  have hca : (cosetGraph R).dist c a = 2 := by rw [SimpleGraph.dist_comm, hac]
  constructor
  · intro d _ hdc _
    have hdV : Z R d ≤ V R c := le_iSup_of_le d (le_iSup_of_le hdc.le le_rfl)
    exact ((commutator_mono le_rfl hdV).trans
      (crossing_le_Z_of_kernel_central common a c ha hc hac (hall c hc))).trans
      (Z_le_radius_center common a ha)
  · intro d _ hda _
    have hdV : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le hda.le le_rfl)
    exact ((commutator_mono le_rfl hdV).trans
      (crossing_le_Z_of_kernel_central common c a hc ha hca hcentral)).trans
      (Z_le_radius_center common c hc)

/-- Source (4.2)(ii) transfers the moving-kernel bound. The edge Z-containment
then upgrades component fixation to centrality in the whole local stabilizer. -/
theorem kernel_central_of_moving_fixed (common : CommonFacts R source geometry)
    (edge : EdgeFacts R) (a : Vertex R) (ha : color R a = false)
    (hmove : ⁅Vcirc R a, Q R a⁆ ≤ fixedCore R a) :
    ⁅V R a, Q R a⁆ ≤ (center (stabilizer R a)).map (stabilizer R a).subtype := by
  have hfixed := common.normalization_transfer a ha (Q R a) le_rfl (Q_normal R a) hmove
  have hZ := edge.commutator_le_Z a ha
  have hCQ : ⁅V R a, Q R a⁆ ≤ centralizer (Q R a : Set (FreeAmalgam R)) :=
    hZ.trans (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha))
  have hCG : ⁅V R a, Q R a⁆ ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    rw [← source.local_generation a ha]
    exact sup_le (le_centralizer_iff.mp (hfixed.trans inf_le_right))
      (le_centralizer_iff.mp hCQ)
  intro x hx
  refine ⟨⟨x, Z_le_stabilizer R a (hZ hx)⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (hCG hx y y.property)


/-- Complete the second (4.6.6) once its preceding local transfer is supplied. -/
theorem derived_noncentral_of_kernel_transfer (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4)
    (transfer : ∀ a, color R a = false →
      ⁅V R a, V R a⁆ ≤ (center (stabilizer R a)).map (stabilizer R a).subtype →
      ⁅V R a, Q R a⁆ ≤ (center (stabilizer R a)).map (stabilizer R a).subtype)
    (a : Vertex R) (ha : color R a = false) :
    ¬ ⁅V R a, V R a⁆ ≤ (center (stabilizer R a)).map (stabilizer R a).subtype := by
  intro hcentral
  exact kernel_noncentral common hb a ha (transfer a ha hcentral)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
