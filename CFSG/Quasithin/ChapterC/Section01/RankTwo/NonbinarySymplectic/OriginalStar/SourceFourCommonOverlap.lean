module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourFixedKernels
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourCommonOverlap

/-!
# The common critical-overlap centralizer for the original radical

The full-core comparison identifies the common center overlap with the
centralizer of either critical center in the other. Its movement is
computed on U because the full midpoint supplement is fixed. The midpoint
containment from source (3.7)(2) makes the original edge radical centralize
the critical displacement.

The root-cover calculation then shows that the literal centralizer of the
common overlap modulo that displacement moves the overlap disjointly from
both complete component-fixed attachments. The source radical, full covers
and original quotient marking are retained throughout.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875,
field-sized critical-image case. SourceFourEquality supplies the comparison
that excludes unequal attachments and SourceFour applies it to the selected
original star.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include hshort hinner

variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include hnsyl

/-- The full original common radical centralizes the critical displacement,
by the midpoint containment of source (3.7)(2). -/
theorem original_critical_root_centralized_by_midpoint
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    Q R t ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  have hZQ := (g.omega_bound a path.start_color (by
    rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
    (omegaCenter_le _)
  have hW : ⁅Z R a,Z R z⁆ ≤ Z R t := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hZQ).trans
      (original_source_two_midpoint_containment h hshort hinner g hb hnsyl path hat hzt)
  have ht : color R t=true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hZt : Z R t=omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  apply le_centralizer_iff.mp
  intro x hx b hbT
  exact (mem_omegaCenter_iff.mp (hZt ▸ hW hx)).2.2 b hbT

set_option maxHeartbeats 400000 in
/-- Movement of the root-fixed part of U, when confined to the common
critical displacement, misses the complete component-fixed attachment. -/
theorem original_critical_overlap_movement_disjoint
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (B : Subgroup (FreeAmalgam R)) (hB : B ≤ Q R t)
    (hmove : ⁅U R a ⊓ centralizer (Z R z : Set (FreeAmalgam R)),B⁆ ≤
      ⁅Z R a,Z R z⁆) :
    Disjoint (⁅U R a ⊓ centralizer (Z R z : Set (FreeAmalgam R)),B⁆)
      (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) := by
  let := h.component_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hCtop : C = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (C) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have hγact (x : stabilizer R a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  obtain ⟨haq,hzq⟩ := h.original_small_critical_indices_eq_field path (by omega) (by
    rw [hcritical,h.field_card]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)
  rw [h.field_card] at haq hzq
  have hZS : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZS)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZS κ hκQ).trans (hzq.trans hFc.symm)
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer z path.end_color)
    h.nonbinary hFc s e he h.component_image_structure.2.2.2.2
    j hj hjr δ (fun x v => hconj (inclusion hZS x) v) hδcard (haq.trans hFc.symm)
  have hγβ : γ.comp (inclusion hZS)=β := by
    apply MonoidHom.ext
    intro x
    exact (congrArg e.groupEquiv
      (show κC (inclusion hZS x)=e.groupEquiv.symm (β x) from
        Subtype.ext (hβmark x).symm)).trans (e.groupEquiv.apply_symm_apply _)
  have hEF : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hcent : B ≤ centralizer
      ((⁅Z R z,j.range⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    rw [hjr,commutator_comm]
    rw [←original_critical_displacement_eq_moving h hshort hinner path hb hat hzt]
    exact hB.trans (original_critical_root_centralized_by_midpoint h hshort hinner hnsyl path hb hat hzt)
  have hm : ⁅j.range ⊓ centralizer (Z R z : Set (FreeAmalgam R)),B⁆ ≤
      ⁅Z R z,j.range⁆ := by
    rw [hjr,commutator_comm (Z R z),←original_critical_displacement_eq_moving h hshort hinner path hb hat hzt]
    exact hmove
  have hh := SaturatedDistanceTwo.embedded_root_overlap_disjoint hEF (MovedSection.coverProjection s e) he j hj
    (stabilizer R a) (Z R z) B hZS (hB.trans (fun _ hx => hx.2 _ (adjacent_symm R hat))) γ hγact
    (by rw [hγβ]; exact hβcard) (by rw [hγβ]; exact hβdim)
    (by rw [hγβ]; exact hβquad) hcent hm
  have hk : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hc,rfl⟩
  rwa [hjr,hk] at hh
/-- The actual common overlap is the full centralizer of either critical
layer inside the other; no fixed supplement is removed. -/
theorem original_critical_common_overlap_eq_centralizer
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) :
    Z R a ⊓ Z R z =
      Z R a ⊓ centralizer (Z R z : Set (FreeAmalgam R)) := by
  have hzQ := (g.omega_bound z path.end_color (by
    rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans
    (omegaCenter_le _)
  have hov := (original_source_three_of_field_critical h hshort hinner hnsyl g hb path hat hzt hcritical).2.2.2.1
  have hle : Z R a ⊓ Z R z ≤ Z R a ⊓ Q R z :=
    inf_le_inf_left _ hzQ
  have hm := relIndex_mul_relIndex (Z R a ⊓ Z R z)
    (Z R a ⊓ Q R z) (Z R a) hle inf_le_left
  rw [inf_relIndex_left,inf_relIndex_left,hcritical,hov] at hm
  have hi : (Z R a ⊓ Z R z).relIndex (Z R a ⊓ Q R z)=1 := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2^n by positivity)
    simpa only [one_mul] using hm
  have he := le_antisymm hle (relIndex_eq_one.mp hi)
  rw [he]
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  rw [←MSCentralOrbit.C_eq_Q R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer z path.end_color]
  ext x
  exact ⟨fun hx => ⟨hx.1,hx.2.2⟩,fun hx => ⟨hx.1,hAZ hx.1,hx.2⟩⟩

/-- The common overlap includes the full fixed midpoint supplement. Its
movement under any subgroup of the actual edge radical is computed on U. -/
theorem original_critical_common_overlap_movement
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n)
    (B : Subgroup (FreeAmalgam R)) (hB : B ≤ Q R t) :
    ⁅Z R a ⊓ Z R z,B⁆ =
      ⁅U R a ⊓ centralizer (Z R z : Set (FreeAmalgam R)),B⁆ := by
  rw [original_critical_common_overlap_eq_centralizer h hshort hinner hnsyl g hb path hat hzt hcritical]
  have hsub : U R a ⊓ centralizer (Z R z : Set (FreeAmalgam R)) ≤
      Z R a ⊓ centralizer (Z R z : Set (FreeAmalgam R)) :=
    fun x hx => ⟨U_le_Z a hx.1,hx.2⟩
  apply le_antisymm ?_ (commutator_mono hsub le_rfl)
  rw [commutator_comm _ B,commutator_comm _ B]
  apply commutator_le.mpr
  intro b hb' x hx
  have hxta : Z R t ≤ Z R a := Sp4Four.edge_Z_le_endpoint R path.start_color hat
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
  have hnorm : Z R t ≤ normalizer (U R a : Set (FreeAmalgam R)) :=
    (hxta.trans ((Z R a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hxjoin : x ∈ U R a ⊔ Z R t := by
    rw [←original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat]
    exact hx.1
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hnorm] at hxjoin
  obtain ⟨u,hu,v,hv,rfl⟩ := hxjoin
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  have hvC : v ∈ centralizer (Z R z : Set (FreeAmalgam R)) :=
    (Z R z).le_centralizer (Sp4Four.edge_Z_le_endpoint R path.end_color hzt hv)
  have huC : u ∈ centralizer (Z R z : Set (FreeAmalgam R)) := by
    have hh := (centralizer (Z R z : Set (FreeAmalgam R))).mul_mem
      hx.2 ((centralizer _).inv_mem hvC)
    simpa only [mul_inv_cancel_right] using hh
  have ht : color R t=true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hZt : Z R t=omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  have hbv : Commute b v := by
    exact (mem_omegaCenter_iff.mp (hZt ▸ hv)).2.2 b (hB hb')
  rw [commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_eq_one_iff_commute.mpr hbv]
  simpa only [mul_one,mul_inv_cancel,one_mul,mul_inv_cancel_right] using
    (commutator_mem_commutator hb' (show u ∈ U R a ⊓ centralizer
      (Z R z : Set (FreeAmalgam R)) from ⟨hu,huC⟩))
/-- The literal centralizer of the common overlap modulo the common
critical displacement moves that overlap disjointly from both complete
fixed attachments. This is the symmetric centralizer in MS93 (3.7)(4). -/
theorem original_source_four_common_overlap_centralizer
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) :
    let V := Z R a ⊓ Z R z
    let W := ⁅Z R a,Z R z⁆
    let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
    let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
    ∃ B : Subgroup (FreeAmalgam R), B ≤ Q R t ∧
      (∀ b : FreeAmalgam R,
        b ∈ B ↔ b ∈ Q R t ∧ ∀ v ∈ V, ⁅b,v⁆ ∈ W) ∧
      ⁅V,B⁆ ≤ W ∧ Disjoint ⁅V,B⁆ A ∧ Disjoint ⁅V,B⁆ A' := by
  dsimp only
  have hZaT : Z R a ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R a (g.exists_critical a path.start_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hat),
      g.distance_constant a path.start_color]
    change 1 < g.b R
    omega
  have hcent := original_critical_root_centralized_by_midpoint h hshort hinner hnsyl path hb hat hzt
  obtain ⟨B,hB,hmem,hm⟩ := SaturatedDistanceTwo.exists_section_centralizer (Q R t)
    (Z R a ⊓ Z R z) ⁅Z R a,Z R z⁆
    (inf_le_left.trans hZaT) hcent
  refine ⟨B,hB,hmem,hm,?_,?_⟩
  · have he := original_critical_common_overlap_movement h hshort hinner hnsyl g hb path hat hzt hcritical B hB
    rw [he] at hm ⊢
    exact original_critical_overlap_movement_disjoint h hshort hinner hnsyl path hb hat hzt hcritical B hB hm
  · have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer
    let rev : CriticalPath R g z a :=
      { start_color := path.end_color
        walk := path.walk.reverse
        shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
        critical := critical_reverse R g hedge a path.start_color
          (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
          z path.end_color path.critical }
    have hother := (h.original_small_critical_indices_eq_field path (by omega) (by
      rw [hcritical,h.field_card]
      have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
      nlinarith)).2
    rw [h.field_card] at hother
    rw [inf_comm] at hm ⊢
    rw [commutator_comm (Z R a)] at hm
    have he := original_critical_common_overlap_movement h hshort hinner hnsyl g hb rev hzt hat hother B hB
    rw [he] at hm ⊢
    exact original_critical_overlap_movement_disjoint h hshort hinner hnsyl rev hb hzt hat hother B hB hm


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
