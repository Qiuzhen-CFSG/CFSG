module
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourPlane
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourPlane

/-!
# The original large critical-image plane and full displacement

In the nonsylow original star, the midpoint bound makes the large critical
image quadratic on the natural cover. Symplectic orthogonality identifies
its displacement as a plane, and the original odd-index radical's cubic
marked order fills that plane's pointwise fixer. The entire cover kernel
belongs to the critical commutator: otherwise the large quadratic image
would preserve a quadratic refinement. This lifts equality of natural
planes to equality of full displacements at both ends.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875,
opening of the larger-image case. The hyperplane comparison uses this
literal original plane marking, without minimum-replacement saturation.
The internal import reuses only generic cover and symplectic geometry.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include h hshort hinner

/-- The full midpoint index is the actual moving-layer centralizer index. -/
theorem original_midpoint_relIndex_eq_moving_centralizer
    (g : Geometry R) (hb : g.b R=2)
    {z t : Vertex R} (hz : color R z=false)
    (hzt : Adjacent R z t) :
    (Z R t).relIndex (Z R z)=
      (centralizer (Q R t : Set (FreeAmalgam R))).relIndex (U R z) := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hzt (hz.trans he.symm)
  have hZt : Z R t=omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  have hZX := g.omega_bound z hz (by
    rw [g.distance_constant z hz]; change 0 < g.b R; omega)
  have hUZ : U R z ≤ Z R z := U_le_Z z
  have hZT : Z R z ≤ Q R t :=
    hZX.trans ((omegaCenter_le _).trans (Q_le_adjacent_h R ht hzt))
  have htZ := Sp4Four.edge_Z_le_endpoint R hz hzt
  have hEq : (Z R t).subgroupOf (U R z)=
      (centralizer (Q R t : Set (FreeAmalgam R))).subgroupOf (U R z) := by
    ext u
    constructor
    · intro hu
      exact (mem_omegaCenter_iff.mp (hZt ▸ hu)).2.2
    · intro hu
      change u.val ∈ Z R t
      rw [hZt]
      exact mem_omegaCenter_iff.mpr ⟨hZT (hUZ u.property),
        (mem_omegaCenter_iff.mp (hZX (hUZ u.property))).2.1,hu⟩
  let := g.Z_elementary (by omega : 0 < g.b R) z hz
  let : ((Z R t).subgroupOf (Z R z)).Normal := inferInstance
  calc
    _ = (Z R t).relIndex (U R z ⊔ Z R t) := by
      rw [←original_Z_eq_moving_sup_edge h hshort hinner g hb hz hzt]
    _ = (Z R t).relIndex (U R z) := by
      rw [←relIndex_subgroupOf (sup_le hUZ htZ),subgroupOf_sup hUZ htZ,
        relIndex_sup_right,relIndex_subgroupOf hUZ]
    _ = _ := congrArg Subgroup.index hEq

variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include hnsyl

/-- A critical image of at least q squared forces the full original nonsylow radical
onto the plane radical in the original natural cover. Its movement has index
q squared, and the complete fixed attachment lies in the critical commutator. -/
theorem original_source_four_large_plane_cover
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)) :
    Nonempty (SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t) ∧
      (centralizer (Z R a : Set (FreeAmalgam R))).relIndex
        (U R z)=(2^n)^2 ∧
      (centralizer (Q R t : Set (FreeAmalgam R))).relIndex
        (U R z)=(2^n)^2 ∧
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) ≤
        ⁅Z R a,U R z⁆ := by
  have ht : color R t = true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
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
  let βZ := β.comp (inclusion hZaT)
  let αZ := (commutator (Sp E.Carrier)).subtype.comp βZ
  have hZker : αZ.ker=(Q R z).subgroupOf (Z R a) := by
    change (α.comp (inclusion hZaT)).ker=_
    rw [←MonoidHom.comap_ker,hαker,comap_inclusion_subgroupOf]
  have hZcard : Nat.card E.Carrier^2 ≤ Nat.card αZ.range := by
    rw [←index_ker,hZker,hFc]
    exact hcritical
  have hZT : αZ.range ≤ α.range := by
    rintro x ⟨y,rfl⟩
    exact ⟨inclusion hZaT y,rfl⟩
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hzt (path.end_color.trans he.symm)
  have hZt : Z R t=omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  have hcomm : ⁅U R z,Z R a⁆ ≤
      centralizer (Q R t : Set (FreeAmalgam R)) := by
    apply ((commutator_mono (U_le_Z z) hZaQ).trans
      (original_source_two_midpoint_containment h hshort hinner g hb hnsyl path hat hzt)).trans
    rw [hZt]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hfix := embedded_displacement_fixed (MovedSection.coverProjection s e) he
    (U R z) (Q R t) (Z R a) hZaT
    j hj hjr β hact hcomm
  have hlarge : Nat.card E.Carrier < Nat.card αZ.range := by
    have hq : 1 < Nat.card E.Carrier := Finite.one_lt_card
    nlinarith
  obtain ⟨hZdim,hfixed,hTdisp⟩ := plane_of_large_fixed α.range αZ.range hZT hfix hlarge
  have hquad : ∀ x ∈ αZ.range, ∀ y ∈ αZ.range, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    intro x hx y hy v
    exact hfix (Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp αZ.range.subtype) ⟨y,hy⟩ v) x (hZT hx)
  have hcard : Nat.card E.Carrier^3 ≤ Nat.card α.range := by
    rw [←index_ker,hαker]
    change Nat.card E.Carrier^3 ≤ (Q R z).relIndex (Q R t)
    rw [original_nonsylow_full_radical_card h hinner hnsyl path.end_color hzt,hFc]
  have hp := plane_radical_of_fixed_plane α.range (displacementSpace αZ.range)
    hZdim (quadratic_displacement_isotropic αZ.range hquad) hfix hcard
  refine ⟨⟨{ toAmbientVertexCover := ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,
              hfaith,hsemi,hconj,hproj,hker⟩
             edge_le := hTSz
             actor := β
             actor_marking := fun u => congrArg Subtype.val
               (e.groupEquiv.symm_apply_apply (κC (inclusion hTSz u)))
             actor_conjugation := hact
             actor_kernel := hαker
             plane_image := hp }⟩,?_,?_,?_⟩
  · rw [cover_moving_index (MovedSection.coverAction s e) (MovedSection.coverProjection s e)
      he (U R z) (Z R a) j hj hjr βZ
        (fun u w => hact (inclusion hZaT u) w),hZdim,hFc]
  · rw [cover_moving_index (MovedSection.coverAction s e) (MovedSection.coverProjection s e)
      he (U R z) (Q R t) j hj hjr β hact,hTdisp,hZdim,hFc]
  · have hk : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
        U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
      apply le_antisymm
      · rintro x ⟨w,hw,rfl⟩
        exact ⟨hjr ▸ ⟨w,rfl⟩,(hker w.toAdd).mp hw⟩
      · rintro x ⟨hx,hc⟩
        obtain ⟨w,rfl⟩ := hjr.symm ▸ hx
        exact ⟨w,(hker w.toAdd).mpr hc,rfl⟩
    rw [←hk]
    apply large_cover_kernel_le_commutator
      (F := E.Carrier) ?_ (U R z) (Z R a)
      (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he j hjr βZ
      (fun u w => hact (inclusion hZaT u) w) hZcard hquad
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)



/-- In the large critical-image branch the full radical moves the opposite
Z-layer by exactly the critical commutator, including its full fixed kernel. -/
theorem original_source_four_large_full_movement
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)) :
    ⁅Q R t,Z R z⁆=⁅Z R a,Z R z⁆ := by
  have ht : color R t = true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  obtain ⟨⟨cv⟩,hcriticalIndex,hfull,hfixed⟩ :=
    original_source_four_large_plane_cover h hshort hinner hnsyl g hb path hat hzt hcritical
  have hZaQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _)
  have hZaT := hZaQ.trans hQaT
  have hmove : ⁅Q R t,U R z⁆ ≤ ⁅Z R a,U R z⁆ := by
    apply cover_displacement_le_of_equal_index
      (MovedSection.coverAction (originalMovedSection h) cv.equiv)
      (MovedSection.coverProjection (originalMovedSection h) cv.equiv) cv.cover
      (U R z) (Z R a) (Q R t) hZaT
      cv.embedding cv.injective cv.range_eq cv.actor cv.actor_conjugation
      (hcriticalIndex.trans hfull.symm)
    intro w hw
    exact hfixed ⟨cv.range_eq ▸ ⟨_,rfl⟩,(cv.kernel w).mp hw⟩
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
  apply le_antisymm ?_ (commutator_mono hZaT le_rfl)
  apply (commutator_le_moving_of_inner_mod_centralizer (Q R t)
    (U R z) (Z R z) (hUzT.trans (Q R t).le_normalizer) ?_).trans
      (hmove.trans (commutator_mono le_rfl (U_le_Z z)))
  rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt]
  exact sup_le_sup_left hcentral _

/-- The large critical branch has the plane-radical geometry at both ends,
both midpoint indices q squared, and the same full displacement R. Both
complete fixed attachments belong to R; their equality is not assumed. -/
theorem original_source_four_large_paired_geometry
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)) :
    Nonempty (SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n a t) ∧
      Nonempty (SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t) ∧
      (Z R t).relIndex (Z R a)=(2^n)^2 ∧
      (Z R t).relIndex (Z R z)=(2^n)^2 ∧
      ⁅Z R a,Q R t⁆=⁅Z R a,Z R z⁆ ∧
      ⁅Z R z,Q R t⁆=⁅Z R a,Z R z⁆ ∧
      (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) ⊔
        (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))) ≤
          ⁅Z R a,Z R z⁆ := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hreverse : (2^n)^2 ≤ (Q R a).relIndex (Z R z) := by
    by_contra hn
    have hh := (h.original_small_critical_indices_eq_field rev (by omega)
      (by simpa only [h.field_card] using lt_of_not_ge hn)).2
    rw [hh,h.field_card] at hcritical
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith
  obtain ⟨ha,_,hai,haf⟩ := original_source_four_large_plane_cover h hshort hinner hnsyl g hb rev hzt hat hreverse
  obtain ⟨hz,_,hzi,hzf⟩ := original_source_four_large_plane_cover h hshort hinner hnsyl g hb path hat hzt hcritical
  refine ⟨ha,hz,
    (original_midpoint_relIndex_eq_moving_centralizer h hshort hinner g hb path.start_color hat).trans hai,
    (original_midpoint_relIndex_eq_moving_centralizer h hshort hinner g hb path.end_color hzt).trans hzi,
    ?_,?_,?_⟩
  · rw [commutator_comm (Z R a),
      original_source_four_large_full_movement h hshort hinner hnsyl g hb rev hzt hat hreverse,
      commutator_comm]
  · rw [commutator_comm (Z R z)]
    exact original_source_four_large_full_movement h hshort hinner hnsyl g hb path hat hzt hcritical
  · apply sup_le
    · exact haf.trans (by rw [commutator_comm]; exact commutator_mono (U_le_Z a) le_rfl)
    · exact hzf.trans (commutator_mono le_rfl (U_le_Z z))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
