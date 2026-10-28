module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceThreeMovement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreePlane
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreePlane
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreeMovement
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreeOverlap
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreeGenerators

/-!
# The original noncontained-core exclusion in MS93 (3.7)(3)

Assume the original critical Z-image has order q and Q is not contained in
Z Q'. The proved midpoint bound forces its natural displacement to be a
self-orthogonal plane. The literal original odd-index nonsylow radical has
cubic marked image, so its action fills the plane radical, with the entire
opposite core as kernel and the same natural-cover marking.

Equality of the natural displacement planes lifts through the full cover:
[T,Z'] = [Q,Z']. The original source triple and the complete fixed attachment
then give [T_0,Z'] = [Z,Z'], hence T_0 <= Z Q'. The opposite overlap lies in
the incident center times D, and its full-radical displacement lies in D.
The plane-radical generator argument forces the critical commutator into D.
Its order is q times the order of U intersect D, contradicting q > 1.
This excludes noncontainment, and the contained-core branch supplies Q = UD,
X = Z and both overlap indices q.

The companion SourceThree applies this result to the selected original star.
The nonsylow and field-sized critical-image branches are explicit; selection
of such a critical pair and the original Sylow branch are not asserted here.
The full fixed attachments and original quotient/action maps are retained.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(3), second paragraph, printed p.874. Internal imports reuse
only proved generic cover, plane-radical and root-displacement arguments;
all original graph, action-kernel and marked-image hypotheses are proved here.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology Representation.BinaryOffender
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- Noncontainment forces the full original edge action to be a plane radical. -/
theorem original_source_three_noncontained_plane_cover
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (hnot : ¬ Q R a ≤ Z R a ⊔ Q R z) :
    Nonempty (SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t) ∧
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex
        (U R z)=(2^n)^2 ∧
      (centralizer (Q R t : Set (FreeAmalgam R))).relIndex
        (U R z)=(2^n)^2 := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := h.component_normal
  let s := originalMovedSection h
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.end_color
  have hCtop : (K.map (QuotientGroup.mk' (pCore 2 H))) = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict ((K.map (QuotientGroup.mk' (pCore 2 H)))) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let β := γ.comp (inclusion hTSz)
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hact (u : Q R t) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β u) w)) =
        u.val*j (Multiplicative.ofAdd w)*u.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hTSz u)))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hTSz u) w
  have hαker : α.ker = (Q R z).subgroupOf (Q R t) := by
    have hkκ : κ.ker = (Q R z).subgroupOf (stabilizer R z) := by
      rw [←hκQ,subgroupOf_map_subtype_eq]
    dsimp only [α,β,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.comp_assoc,MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      ←MonoidHom.comap_ker,MonoidHom.ker_codRestrict,hkκ,comap_inclusion_subgroupOf]
  have hFc : Nat.card E.Carrier=2^n := E.card_eq.trans (congrArg (2^·) hE)
  have hZaQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _)
  have hZaT := hZaQ.trans hQaT
  let βA := β.comp (inclusion hQaT)
  let αA := (commutator (Sp E.Carrier)).subtype.comp βA
  let βZ := β.comp (inclusion hZaT)
  let αZ := (commutator (Sp E.Carrier)).subtype.comp βZ
  have hZaS := hZaT.trans hTSz
  let δ := κ.comp (inclusion hZaS)
  have hother := (h.original_small_critical_indices_eq_field path (by omega) (by
    rw [h.field_card,hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  rw [h.field_card] at hother
  have hδcard : Nat.card δ.range=Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZaS κ hκQ).trans
      (hcritical.trans hFc.symm)
  obtain ⟨η,hηcard,hηmark,hηact,hηdim,hηquad⟩ := inner_root_actor_of_field_index path (by omega)
    (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer a path.start_color)
    h.nonbinary hFc s e he h.component_image_structure.2.2.2.2
    j hj hjr δ (fun x w => hconj (inclusion hZaS x) w) hδcard (hother.trans hFc.symm)
  have hβmark (u : Q R t) : (e.groupEquiv.symm (β u) : _) =
      κ (inclusion hTSz u) :=
    congrArg Subtype.val (e.groupEquiv.symm_apply_apply (κC (inclusion hTSz u)))
  have hβZ : βZ=η := by
    apply MonoidHom.ext
    intro x
    apply e.groupEquiv.symm.injective
    exact Subtype.ext ((hβmark (inclusion hZaT x)).trans (hηmark x).symm)
  have hZdim : Module.finrank E.Carrier (displacementSpace αZ.range)=1 := by
    have hr : αZ.range=η.range.map (commutator (Sp E.Carrier)).subtype := by
      rw [MonoidHom.range_comp,hβZ]
    rw [hr]
    exact hηdim
  have hZcard : Nat.card αZ.range=Nat.card E.Carrier := by
    rw [MonoidHom.range_comp,hβZ,card_map_of_injective
      (commutator (Sp E.Carrier)).subtype_injective,hηcard]
  have hAT : αA.range ≤ α.range := by
    rintro x ⟨y,rfl⟩
    exact ⟨inclusion hQaT y,rfl⟩
  have hZA : αZ.range ≤ αA.range := by
    rintro x ⟨y,rfl⟩
    exact ⟨inclusion hZaQ y,rfl⟩
  have hnot' : ¬ αA.range ≤ αZ.range := by
    intro hh
    apply hnot
    intro x hx
    obtain ⟨y,hy⟩ := hh (show αA ⟨x,hx⟩ ∈ αA.range from ⟨⟨x,hx⟩,rfl⟩)
    let u : Q R t := inclusion hQaT ⟨x,hx⟩ * (inclusion hZaT y)⁻¹
    have hu : u ∈ α.ker := by
      change α u=1
      dsimp only [u]
      rw [map_mul,map_inv]
      change αA ⟨x,hx⟩ * (αZ y)⁻¹=1
      rw [hy,mul_inv_cancel]
    have hq : x*y.val⁻¹ ∈ Q R z :=
      show u ∈ (Q R z).subgroupOf (Q R t) from hαker ▸ hu
    have hh := (Z R a ⊔ Q R z).mul_mem
      (mem_sup_right hq) (mem_sup_left y.property)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hzt (path.end_color.trans he.symm)
  have hZt : Z R t=omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  have hcomm : ⁅U R z,Q R a⁆ ≤
      centralizer (Q R t : Set (FreeAmalgam R)) := by
    apply ((commutator_mono (U_le_Z z) le_rfl).trans
      (original_source_two_midpoint_containment h hshort hinner g hb hnsyl path hat hzt)).trans
    rw [hZt]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hfix := embedded_displacement_fixed (MovedSection.coverProjection s e) he
    (U R z) (Q R t) (Q R a) hQaT
    j hj hjr β hact hcomm
  obtain ⟨hAdim,hfixed,hTdisp⟩ := plane_of_root_escape α.range αA.range αZ.range
    hAT hZA hZdim hZcard hfix hnot'
  have hquad : ∀ x ∈ αA.range, ∀ y ∈ αA.range, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    intro x hx y hy v
    exact hfix (Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp αA.range.subtype) ⟨y,hy⟩ v) x (hAT hx)
  have hcard : Nat.card E.Carrier^3 ≤ Nat.card α.range := by
    rw [←index_ker,hαker]
    change Nat.card E.Carrier^3 ≤ (Q R z).relIndex (Q R t)
    rw [original_nonsylow_full_radical_card h hinner hnsyl path.end_color hzt,hFc]
  have hp := plane_radical_of_fixed_plane α.range (displacementSpace αA.range)
    hAdim (quadratic_displacement_isotropic αA.range hquad) hfix hcard
  refine ⟨⟨{ toAmbientVertexCover := ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,
              hfaith,hsemi,hconj,hproj,hker⟩
             edge_le := hTSz
             actor := β
             actor_marking := hβmark
             actor_conjugation := hact
             actor_kernel := hαker
             plane_image := hp }⟩,?_,?_⟩
  · rw [cover_moving_index (MovedSection.coverAction s e) (MovedSection.coverProjection s e)
      he (U R z) (Q R a) j hj hjr βA
        (fun u w => hact (inclusion hQaT u) w),hAdim,hFc]
  · rw [cover_moving_index (MovedSection.coverAction s e) (MovedSection.coverProjection s e)
      he (U R z) (Q R t) j hj hjr β hact,hTdisp,hAdim,hFc]


/-- The full edge and endpoint core have the same opposite Z-displacement. -/
theorem original_source_three_noncontained_full_movement
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n)
    (hnot : ¬ Q R a ≤ Z R a ⊔ Q R z) :
    ⁅Q R t,Z R z⁆=⁅Q R a,Z R z⁆ := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  obtain ⟨⟨cv⟩,hcore,hfull⟩ :=
    original_source_three_noncontained_plane_cover h hshort hinner hnsyl g hb path hat hzt hcritical hnot
  have hpair := original_critical_paired_fixed_layers h hshort hinner path hb hat hzt hcritical
  have hZaQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _)
  have hmove : ⁅Q R t,U R z⁆ ≤ ⁅Q R a,U R z⁆ := by
    apply cover_displacement_le_of_equal_index
      (MovedSection.coverAction (originalMovedSection h) cv.equiv)
      (MovedSection.coverProjection (originalMovedSection h) cv.equiv) cv.cover
      (U R z) (Q R a) (Q R t) hQaT
      cv.embedding cv.injective cv.range_eq cv.actor cv.actor_conjugation
      (hcore.trans hfull.symm)
    intro w hw
    have hk : cv.embedding (Multiplicative.ofAdd w) ∈
        U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) :=
      ⟨cv.range_eq ▸ ⟨_,rfl⟩,(cv.kernel w).mp hw⟩
    have hh := hpair.2.1 (mem_sup_right hk)
    rw [hpair.1] at hh
    exact commutator_mono ((U_le_Z a).trans hZaQ) le_rfl hh
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hzt (path.end_color.trans he.symm)
  have hZt : Z R t=omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  have hcentral : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [hZt]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hUzT : U R z ≤ Q R t := (U_le_Z z).trans
    (Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color) (by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
        g.distance_constant z path.end_color]
      change 1 < g.b R
      omega))
  apply le_antisymm ?_ (commutator_mono hQaT le_rfl)
  apply (commutator_le_moving_of_inner_mod_centralizer (Q R t)
    (U R z) (Z R z) (hUzT.trans (Q R t).le_normalizer) ?_).trans
      (hmove.trans (commutator_mono le_rfl (U_le_Z z)))
  rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt]
  exact sup_le_sup_left hcentral _

/-- The component part of the full radical moves Z′ only into the critical
commutator. This is the component-intersection step on printed p.874; neither
full fixed core is discarded and no equality of their kernels is assumed. -/
theorem original_source_three_noncontained_component_movement
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n)
    (hnot : ¬ Q R a ≤ Z R a ⊔ Q R z) :
    ⁅(Q R t ⊓ Ltilde R a),Z R z⁆ = ⁅Z R a,Z R z⁆ := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let W := ⁅Z R a,Z R z⁆
  have hpair := original_critical_paired_fixed_layers h hshort hinner path hb hat hzt hcritical
  have hWU : W ≤ U R a := hpair.2.2.1.trans inf_le_left
  have hUQ : U R a ≤ Q R a := (U_le_Z a).trans
    ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _))
  have hWD : W ≤ normalizer (fixedCore R a : Set (FreeAmalgam R)) :=
    hWU.trans (hUQ.trans (hQaT.trans (original_fixedCore_normalized hat)))
  have hcomp : ⁅(Q R t ⊓ Ltilde R a),Z R z⁆ ≤ U R a := by
    rw [commutator_comm]
    exact (original_component_radical_triples h hshort hinner hnsyl g hb path hat hzt).1
  have hbound : ⁅(Q R t ⊓ Ltilde R a),Z R z⁆ ≤ W ⊔ fixedCore R a := by
    apply (commutator_mono inf_le_left le_rfl).trans
    rw [original_source_three_noncontained_full_movement h hshort hinner hnsyl g hb path hat hzt hcritical hnot]
    exact original_source_three_whole_core_movement h hshort hinner path hb hat hzt
  apply le_antisymm
  · intro x hx
    have hxU := hcomp hx
    have hxprod := hbound hx
    rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hWD] at hxprod
    obtain ⟨r,hr,y,hy,rfl⟩ := hxprod
    have hyU : y ∈ U R a := by
      have hh := (U R a).mul_mem ((U R a).inv_mem (hWU hr)) hxU
      simpa only [inv_mul_cancel_left] using hh
    have hyW : y ∈ W := hpair.2.1 (mem_sup_left ⟨hyU,hy.2⟩)
    exact W.mul_mem hr hyW
  · rw [original_critical_displacement_eq_moving h hshort hinner path hb hat hzt]
    exact commutator_mono
      (le_inf (hUQ.trans hQaT) ((original_component_core_intersection h hshort path.start_color).symm.le.trans inf_le_left)) le_rfl

/-- The original component radical lies in the actual critical product. -/
theorem original_source_three_noncontained_component_containment
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n)
    (hnot : ¬ Q R a ≤ Z R a ⊔ Q R z) :
    (Q R t ⊓ Ltilde R a) ≤ Z R a ⊔ Q R z := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := h.component_normal
  obtain ⟨⟨cv⟩,_,_⟩ :=
    original_source_three_noncontained_plane_cover h hshort hinner hnsyl g hb path hat hzt hcritical hnot
  rcases cv with ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩,
    hTS,β,hβmark,hact,hαker,hplane⟩
  let s := originalMovedSection h
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hZaQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _)
  have hZaT := hZaQ.trans hQaT
  have hBT : (Q R t ⊓ Ltilde R a) ≤ Q R t := inf_le_left
  let βB := β.comp (inclusion hBT)
  let βZ := β.comp (inclusion hZaT)
  let αB := (commutator (Sp E.Carrier)).subtype.comp βB
  let αZ := (commutator (Sp E.Carrier)).subtype.comp βZ
  have hZaS := hZaT.trans hTS
  let δ := κ.comp (inclusion hZaS)
  have hFc : Nat.card E.Carrier=2^n :=
    E.card_eq.trans (congrArg (2^·) hE)
  have hother := (h.original_small_critical_indices_eq_field path (by omega) (by
    rw [h.field_card,hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  rw [h.field_card] at hother
  have hδcard : Nat.card δ.range=Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZaS κ hκQ).trans
      (hcritical.trans hFc.symm)
  obtain ⟨η,hηcard,hηmark,hηact,hηdim,hηquad⟩ := inner_root_actor_of_field_index path (by omega)
    (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer a path.start_color)
    h.nonbinary hFc s e he h.component_image_structure.2.2.2.2
    j hj hjr δ
    (fun x w => hconj (inclusion hZaS x) w) hδcard (hother.trans hFc.symm)
  have hβZ : βZ=η := by
    apply MonoidHom.ext
    intro x
    apply e.groupEquiv.symm.injective
    exact Subtype.ext ((hβmark (inclusion hZaT x)).trans (hηmark x).symm)
  have hZrange : αZ.range=η.range.map (commutator (Sp E.Carrier)).subtype := by
    rw [MonoidHom.range_comp,hβZ]
  have hdim : Module.finrank E.Carrier (displacementSpace αZ.range)=1 := by
    rw [hZrange]
    exact hηdim
  have hcard : Nat.card αZ.range=Nat.card E.Carrier := by
    rw [hZrange,card_map_of_injective (commutator (Sp E.Carrier)).subtype_injective,hηcard]
  have hmove : ⁅(Q R t ⊓ Ltilde R a),U R z⁆ ≤ ⁅Z R a,U R z⁆ := by
    apply (commutator_mono le_rfl (U_le_Z z)).trans
    rw [original_source_three_noncontained_component_movement h hshort hinner hnsyl g hb path hat hzt hcritical hnot,
      original_critical_displacement_eq_paired_moving h hshort hinner path hb hat hzt]
    exact commutator_mono (U_le_Z a) le_rfl
  have hle : αB.range ≤ αZ.range :=
    embedded_actor_le_root_of_commutator_le
      (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he
      j hj ((Q R t ⊓ Ltilde R a)) (Z R a) βB βZ
      (fun x w => hact (inclusion hBT x) w)
      (fun x w => hact (inclusion hZaT x) w)
      (by rw [hjr]; exact hmove) hdim hcard
  intro x hx
  obtain ⟨y,hy⟩ := hle (show αB ⟨x,hx⟩ ∈ αB.range from ⟨⟨x,hx⟩,rfl⟩)
  let u : Q R t := inclusion hBT ⟨x,hx⟩*(inclusion hZaT y)⁻¹
  have hu : u ∈ α.ker := by
    change α u=1
    dsimp only [u]
    rw [map_mul,map_inv]
    change αB ⟨x,hx⟩*(αZ y)⁻¹=1
    rw [hy,mul_inv_cancel]
  have hq : x*y.val⁻¹ ∈ Q R z :=
    show u ∈ (Q R z).subgroupOf (Q R t) from hαker ▸ hu
  have hh := (Z R a ⊔ Q R z).mul_mem (mem_sup_right hq) (mem_sup_left y.property)
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

/-- The opposite overlap centralizes the component radical, and is contained
in the midpoint center times the complete fixed core. -/
theorem original_source_three_noncontained_overlap
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n)
    (hnot : ¬ Q R a ≤ Z R a ⊔ Q R z) :
    ⁅Z R z ⊓ Q R a,(Q R t ⊓ Ltilde R a)⁆=⊥ ∧
      Z R z ⊓ Q R a ≤ Z R t ⊔ fixedCore R a := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hinside := original_source_three_noncontained_component_containment h hshort hinner hnsyl g hb path hat hzt hcritical hnot
  have hcentral : Z R z ⊓ Q R a ≤
      centralizer ((Q R t ⊓ Ltilde R a : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mpr
    apply hinside.trans
    apply sup_le
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R a path.start_color)).trans (centralizer_le inf_le_right)
    · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R z path.end_color))).trans (centralizer_le inf_le_left)
  refine ⟨commutator_eq_bot_iff_le_centralizer.mpr hcentral,?_⟩
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  have hprod : Z R z ⊓ Q R a ≤ U R a ⊔ fixedCore R a :=
    (le_inf inf_le_right (inf_le_left.trans (Z R z).le_centralizer)).trans
      (short_original_critical_core_centralizer_le_moving_fixed h hshort (by omega) rev)
  have hUaC : U R a ≤ centralizer (Q R a : Set (FreeAmalgam R)) :=
    (U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R a path.start_color))
  have hUD : U R a ≤ normalizer (fixedCore R a : Set (FreeAmalgam R)) :=
    (hUaC.trans (centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hDC : fixedCore R a ≤
      centralizer ((Q R t ⊓ Ltilde R a : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    (show fixedCore R a ≤ centralizer (Ltilde R a : Set (FreeAmalgam R)) from inf_le_right).trans (centralizer_le inf_le_right)
  have hZX := g.omega_bound a path.start_color (by
    rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  have hZt : Z R t=omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  intro x hx
  have hxprod := hprod hx
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hUD] at hxprod
  obtain ⟨u,hu,v,hv,rfl⟩ := hxprod
  have huC : u ∈ centralizer ((Q R t ⊓ Ltilde R a : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    have hh := (centralizer ((Q R t ⊓ Ltilde R a : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))).mul_mem
      (hcentral hx) ((centralizer _).inv_mem (hDC hv))
    simpa only [mul_inv_cancel_right] using hh
  have huT : u ∈ centralizer (Q R t : Set (FreeAmalgam R)) := by
    have hB : (Q R t ⊓ Ltilde R a) ≤ centralizer ({u} : Set (FreeAmalgam R)) :=
      fun b hb => mem_centralizer_singleton_iff.mpr (huC b hb)
    have hQ : Q R a ≤ centralizer ({u} : Set (FreeAmalgam R)) :=
      fun q hq => mem_centralizer_singleton_iff.mpr (hUaC hu q hq)
    have hh := sup_le hB hQ
    rw [original_component_radical_sup_core h hinner path.start_color hat] at hh
    exact fun y hy => mem_centralizer_singleton_iff.mp (hh hy)
  have huZt : u ∈ Z R t := by
    rw [hZt]
    exact mem_omegaCenter_iff.mpr ⟨hQaT (omegaCenter_le _ (hZX (U_le_Z a hu))),
      (mem_omegaCenter_iff.mp (hZX (U_le_Z a hu))).2.1,huT⟩
  exact mul_mem (mem_sup_left huZt) (mem_sup_right hv)

/-- The whole radical moves the opposite overlap only into the complete
fixed core. This is the bound used in the final generator contradiction
of source (3.7)(3). -/
theorem original_source_three_noncontained_overlap_displacement
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n)
    (hnot : ¬ Q R a ≤ Z R a ⊔ Q R z) :
    ⁅Z R z ⊓ Q R a,Q R t⁆ ≤ fixedCore R a := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hle := (original_source_three_noncontained_overlap h hshort hinner hnsyl g hb path hat hzt hcritical hnot).2
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  have hZt : Z R t=omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  apply (commutator_mono hle le_rfl).trans
  apply commutator_sup_le_of_relative_normal (Q R t)
    (Z R t) (fixedCore R a) (Q R t) (fixedCore R a)
    (original_fixedCore_normalized hat) (hZt ▸ omegaCenter_le _) (inf_le_left.trans hQaT)
  · rw [commutator_eq_bot_iff_le_centralizer.mpr
      (show Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) from by
        rw [hZt]; exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2)]
    exact bot_le
  · exact le_normalizer_iff_commutator_le_left.mp (original_fixedCore_normalized hat)

/-- The source plane-radical generator contradiction excludes noncontainment. -/
theorem original_source_three_core_containment
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) :
    Q R a ≤ Z R a ⊔ Q R z := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  by_contra hnot
  let := h.component_normal
  obtain ⟨⟨cv⟩,_,_⟩ :=
    original_source_three_noncontained_plane_cover h hshort hinner hnsyl g hb path hat hzt hcritical hnot
  rcases cv with ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩,
    hTS,β,hβmark,hact,hαker,hplane⟩
  let s := originalMovedSection h
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hZaQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _)
  have hZaT := hZaQ.trans hQaT
  let βZ := β.comp (inclusion hZaT)
  let αZ := (commutator (Sp E.Carrier)).subtype.comp βZ
  have hZaS := hZaT.trans hTS
  let δ := κ.comp (inclusion hZaS)
  have hFc : Nat.card E.Carrier=2^n :=
    E.card_eq.trans (congrArg (2^·) hE)
  have hother := (h.original_small_critical_indices_eq_field path (by omega) (by
    rw [h.field_card,hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  rw [h.field_card] at hother
  have hδcard : Nat.card δ.range=Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZaS κ hκQ).trans
      (hcritical.trans hFc.symm)
  obtain ⟨η,hηcard,hηmark,hηact,hηdim,hηquad⟩ := inner_root_actor_of_field_index path (by omega)
    (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer a path.start_color)
    h.nonbinary hFc s e he h.component_image_structure.2.2.2.2
    j hj hjr δ
    (fun x w => hconj (inclusion hZaS x) w) hδcard (hother.trans hFc.symm)
  have hβZ : βZ=η := by
    apply MonoidHom.ext
    intro x
    apply e.groupEquiv.symm.injective
    exact Subtype.ext ((hβmark (inclusion hZaT x)).trans (hηmark x).symm)
  have hZrange : αZ.range=η.range.map (commutator (Sp E.Carrier)).subtype := by
    rw [MonoidHom.range_comp,hβZ]
  have hdim : Module.finrank E.Carrier (displacementSpace αZ.range)=1 := by
    rw [hZrange]
    exact hηdim
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ))
    (by have := h.nonbinary; omega)
  have hEF : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact (show (2:ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) h.nonbinary)
  have hC := MSCentralOrbit.C_eq_Q R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer a path.start_color
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hUC : U R z ⊓ centralizer (Z R a : Set (FreeAmalgam R)) ≤
      Z R z ⊓ Q R a := by
    intro x hx
    refine ⟨U_le_Z z hx.1,?_⟩
    rw [←hC]
    exact ⟨hZA (U_le_Z z hx.1),hx.2⟩
  have hfull : ⁅U R z,Q R t⁆ ≤ fixedCore R a := by
    apply SaturatedDistanceTwo.embedded_plane_overlap hEF
      (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he
      (U R z) (Q R t) (Z R a) (fixedCore R a)
      hZaT j hjr β hact hplane hdim
    exact (commutator_mono hUC le_rfl).trans
      (original_source_three_noncontained_overlap_displacement h hshort hinner hnsyl g hb path hat hzt hcritical hnot)
  have hpair := original_critical_paired_fixed_layers h hshort hinner path hb hat hzt hcritical
  have hRD : ⁅Z R a,Z R z⁆ ≤ fixedCore R a := by
    rw [hpair.1,commutator_comm]
    exact (commutator_mono le_rfl ((U_le_Z a).trans hZaT)).trans hfull
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  have hRA : ⁅Z R a,Z R z⁆ ≤ A :=
    le_inf (hpair.2.2.1.trans inf_le_left) (hRD.trans inf_le_right)
  let := finite_Z R a
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a)))
    (inclusion_injective _)
  have hc := Nat.card_le_card_of_injective (inclusion hRA) (inclusion_injective _)
  rw [hpair.2.2.2.1] at hc
  have ha : 0 < Nat.card A := Nat.card_pos
  change 2^n*Nat.card A ≤ Nat.card A at hc
  nlinarith

/-- Source (3.7)(3), with the actual critical image of order q: the full
core is U D, the central omega layer is Z, and both overlap indices are q.
The complete fixed attachments and original quotient markings remain. -/
theorem original_source_three_of_field_critical
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) :
    Q R a ≤ Z R a ⊔ Q R z ∧
      Q R a=U R a ⊔ fixedCore R a ∧
      X R a=Z R a ∧
      (Z R z).relIndex (Z R a)=2^n ∧
      (Z R a).relIndex (Z R z)=2^n := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hinside := original_source_three_core_containment h hshort hinner hnsyl g hb path hat hzt hcritical
  obtain ⟨hQ,hX⟩ := original_source_three_contained_core h hshort hinner path (by omega) hat hcritical hinside
  exact ⟨hinside,hQ,hX,original_source_three_contained_core_overlap h hshort hinner path hb hat hzt hcritical hinside⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
