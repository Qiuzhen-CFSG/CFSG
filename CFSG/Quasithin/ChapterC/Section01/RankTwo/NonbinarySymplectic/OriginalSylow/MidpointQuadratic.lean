module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.MidpointTriples
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoFixedCore

/-!
# Original Sylow fixed-core quadraticity

The component-radical triples in the original Sylow branch give the same
large-movement comparison as the nonsylow branch. The complete original
cores and their fixed attachments are retained throughout. A hypothetical
fixed-core movement larger than q squared contradicts the four-critical-root
bound on the full opposite core quotient. Hence the full fixed core acts
quadratically on the entire opposite Z-layer, including its edge center.

Source: MS93 (3.7)(2), printed p.873. Internal imports reuse the short-component
whole-core and generic natural-cover calculations; no minimum replacement
or marked-image preservation premise is introduced.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit OriginalStar
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- In the original large-movement branch, the component part and the
moving layer have the same order-q image in the opposite full-core quotient. -/
private theorem original_large_movement_images
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (Q R z).relIndex (Q R t ⊓ Ltilde R a) = 2^n ∧
      (Q R z).relIndex (U R a) = 2^n ∧
      (Q R z).relIndex (Z R a) = 2^n ∧
      (Q R t ⊓ Ltilde R a) ⊔ Q R z = U R a ⊔ Q R z := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective (inclusion hTSz) (inclusion_injective _)
  let : ((Q R z).subgroupOf (Q R t)).Normal :=
    normal_subgroupOf_of_le_normalizer (hTSz.trans (Q_normalized R z))
  have hULQ := (original_component_core_intersection h hshort path.start_color).ge
  have hU₀ : U R a ≤ Q R t ⊓ Ltilde R a :=
    le_inf (hULQ.trans (inf_le_right.trans hQaT)) (hULQ.trans inf_le_left)
  have hUT := hU₀.trans inf_le_left
  have hZtQ : Z R t ≤ Q R z :=
    (Sp4Four.edge_Z_le_endpoint R path.end_color hzt).trans
      ((g.omega_bound z path.end_color (by
        rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans (omegaCenter_le _))
  have hZa : Z R a ≤ U R a ⊔ Q R z := by
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat]
    exact sup_le_sup_left hZtQ _
  have hsup (B : Subgroup (FreeAmalgam R)) (hBT : B ≤ Q R t) :
      (Q R z).relIndex (B ⊔ Q R z) = (Q R z).relIndex B := by
    rw [←relIndex_subgroupOf (sup_le hBT hQzT),
      subgroupOf_sup hBT hQzT,relIndex_sup_right,relIndex_subgroupOf hBT]
  have hfinite (B : Subgroup (FreeAmalgam R)) (hBT : B ≤ Q R t) :
      (Q R z).relIndex B ≠ 0 := by
    let : Finite B := Finite.of_injective (inclusion hBT) (inclusion_injective _)
    exact index_ne_zero_of_finite
  have htriple := (OriginalSylow.original_component_radical_triples h hshort hinner hsy g hb path hat hzt).2
  have hbound := original_moving_triple_index_le h hinner path.end_color
    (Q R a) (Q R t ⊓ Ltilde R a)
    (hQaT.trans hTSz) (inf_le_left.trans hTSz) hlarge
    (le_antisymm ((commutator_mono (commutator_mono (U_le_Z z) le_rfl) le_rfl).trans
      htriple.le) bot_le)
  have hlow := (h.original_critical_indices_ge_field path (by omega)).1
  rw [h.field_card] at hlow
  have hZU : (Q R z).relIndex (Z R a) ≤ (Q R z).relIndex (U R a) := by
    have hh := relIndex_le_of_le_right hZa (hfinite _ (sup_le hUT hQzT))
    rwa [hsup _ hUT] at hh
  have hU₀i := relIndex_le_of_le_right hU₀ (hfinite _ inf_le_left)
  have hUi : (Q R z).relIndex (U R a) = 2^n := by omega
  have h₀i : (Q R z).relIndex (Q R t ⊓ Ltilde R a) = 2^n := by omega
  refine ⟨h₀i,hUi,by omega,?_⟩
  have hQX : Q R z ≤ U R a ⊔ Q R z := le_sup_right
  have hXY : U R a ⊔ Q R z ≤ (Q R t ⊓ Ltilde R a) ⊔ Q R z := sup_le_sup_right hU₀ _
  have hm := relIndex_mul_relIndex (Q R z)
    (U R a ⊔ Q R z) ((Q R t ⊓ Ltilde R a) ⊔ Q R z) hQX hXY
  rw [hsup _ hUT,hsup (Q R t ⊓ Ltilde R a) inf_le_left,hUi,h₀i] at hm
  have hqi : (U R a ⊔ Q R z).relIndex ((Q R t ⊓ Ltilde R a) ⊔ Q R z) = 1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^n) (by simpa using hm)
  exact le_antisymm (relIndex_eq_one.mp hqi) hXY

/-- MS93 (3.7)(2), p.873: large movement gives the literal factorization
T₀ = U (T₀ ∩ Q′) in the original graph. The whole opposite core is retained.
Innerness and shortness are supplied by the actual source star below. -/
theorem original_large_movement_component_factorization
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (Q R t ⊓ Ltilde R a) = U R a ⊔ ((Q R t ⊓ Ltilde R a) ⊓ Q R z) := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hULQ := (original_component_core_intersection h hshort path.start_color).ge
  have hU₀ : U R a ≤ Q R t ⊓ Ltilde R a :=
    le_inf (hULQ.trans (inf_le_right.trans hQaT)) (hULQ.trans inf_le_left)
  have he := (original_large_movement_images h hshort hinner hsy g hb path hat hzt hlarge).2.2.2
  apply le_antisymm ?_ (sup_le hU₀ inf_le_left)
  intro x hx
  have hx' : x ∈ U R a ⊔ Q R z := he ▸ mem_sup_left hx
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    ((hU₀.trans inf_le_left).trans (hTSz.trans (Q_normalized R z)))] at hx'
  obtain ⟨u,hu,q,hq,rfl⟩ := hx'
  have hq₀ : q ∈ Q R t ⊓ Ltilde R a := by
    have hh := (Q R t ⊓ Ltilde R a).mul_mem
      ((Q R t ⊓ Ltilde R a).inv_mem (hU₀ hu)) hx
    simpa only [inv_mul_cancel_left] using hh
  exact mul_mem (mem_sup_left hu) (mem_sup_right ⟨hq₀,hq⟩)



private theorem original_fixedCore_large_centralizer_comparison
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (himage : (Q R z).relIndex (U R a) = 2^n)
    (hlarge : (2^n)^2 <
      (centralizer (fixedCore R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (Q R t ⊓ Ltilde R a) ⊓ (U R z ⊔ fixedCore R z) ≤
      U R a ⊔ fixedCore R z := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hUa : U R a ≤ Ltilde R a ⊓ Q R a := (original_component_core_intersection h hshort path.start_color).ge
  have hUz : U R z ≤ Ltilde R z ⊓ Q R z := (original_component_core_intersection h hshort path.end_color).ge
  let A := fixedCore R a
  let B := U R a
  have hAT : A ≤ Q R t := inf_le_left.trans hQaT
  have hB₀ : B ≤ (Q R t ⊓ Ltilde R a) :=
    le_inf (hUa.trans (inf_le_right.trans hQaT)) (hUa.trans inf_le_left)
  have hBT : B ≤ Q R t := hB₀.trans inf_le_left
  have hAS : A ≤ stabilizer R z := hAT.trans hTSz
  have hBS : B ≤ stabilizer R z := hBT.trans hTSz
  have hz := path.end_color
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex hz
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
  have haction (x : stabilizer R z) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  let βA := γ.comp (inclusion hAS)
  let βB := γ.comp (inclusion hBS)
  let αB := (commutator (Sp E.Carrier)).subtype.comp βB
  have hk : αB.ker = (Q R z).subgroupOf B := by
    have hkκ : κ.ker = (Q R z).subgroupOf (stabilizer R z) := by
      rw [←hκQ,subgroupOf_map_subtype_eq]
    dsimp only [αB,βB,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.comp_assoc,MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      ←MonoidHom.comap_ker,MonoidHom.ker_codRestrict,hkκ,comap_inclusion_subgroupOf]
  have hi : Nat.card αB.range = 2^n := by
    rw [←index_ker,hk]
    exact himage
  have hBlarge : 1 < Nat.card αB.range := by
    rw [hi]
    exact one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  have hmove : ⁅B,U R z⁆ ≤ U R a := by
    rw [commutator_comm]
    exact (commutator_mono (U_le_Z z) hB₀).trans
      (OriginalSylow.original_component_radical_triples h hshort hinner hsy g hb path hat hzt).1
  have htriple : ⁅⁅U R z,B⁆,A⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [commutator_comm (U R z)]
    exact hmove.trans (((U_le_Z a).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a path.start_color))).trans
      (centralizer_le (show A ≤ Q R a from inf_le_left)))
  have hUzT : U R z ≤ Q R t := hUz.trans (inf_le_right.trans hQzT)
  have hkernel (w : s.space.toSubmodule) :
      MovedSection.coverProjection s e w=0 ↔
        j (Multiplicative.ofAdd w) ∈ fixedCore R z := by
    constructor
    · intro hw
      refine ⟨?_,(hker w).mp hw⟩
      exact ((U_le_Z z).trans ((g.omega_bound z path.end_color (by
        rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans
          (omegaCenter_le _))) (hjr ▸ ⟨_,rfl⟩)
    · exact fun hw => (hker w).mpr hw.2
  have hfixed := cover_large_centralizer_le (MovedSection.coverAction s e)
    (MovedSection.coverProjection s e) he (U R z) A B
    (U R a) (fixedCore R z) j hj hjr βA βB
    (fun x => haction (inclusion hAS x)) (fun x => haction (inclusion hBS x))
    (by simpa only [E.card_eq,hE] using hlarge) hBlarge htriple hmove hkernel
    (hUzT.trans (original_fixedCore_normalized hzt))
  apply component_intersection_le_of_fixed_preimage (Q R t)
    ((Q R t ⊓ Ltilde R a)) A (U R z) (U R a)
    (fixedCore R z) inf_le_left hUzT (inf_le_left.trans hQzT)
    (le_normalizer_iff_commutator_le_left.mp (hAT.trans (original_fixedCore_normalized hzt)))
    (original_fixedCore_normalized hzt) ?_ hfixed
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (centralizer_le (show Q R t ⊓ Ltilde R a ≤ Ltilde R a from inf_le_right)))


/-- The full fixed core moves at most q² cosets of the opposite natural cover. -/
theorem original_fixedCore_movement_le_square
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    (centralizer (fixedCore R a : Set (FreeAmalgam R))).relIndex
      (U R z) ≤ (2^n)^2 := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective
    (inclusion hTSz) (inclusion_injective _)
  have hUzQ : U R z ≤ Q R z :=
    (original_component_core_intersection h hshort path.end_color).ge.trans inf_le_right
  have hUaQ : U R a ≤ Q R a :=
    (original_component_core_intersection h hshort path.start_color).ge.trans inf_le_right
  let : Finite (U R z) := Finite.of_injective
    (inclusion (hUzQ.trans hQzT)) (inclusion_injective _)
  by_contra! hlarge
  have hlargeQ : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z) :=
    hlarge.trans_le (relIndex_le_of_le_left (centralizer_le
      (show fixedCore R a ≤ Q R a from inf_le_left)) index_ne_zero_of_finite)
  obtain ⟨hT,hU,hZ,he⟩ := original_large_movement_images h hshort hinner hsy g hb path hat hzt hlargeQ
  have hfactor := original_large_movement_component_factorization h hshort hinner hsy g hb path hat hzt hlargeQ
  have hcomp := original_fixedCore_large_centralizer_comparison h hshort hinner hsy g hb path hat hzt hU hlarge
  have hZaT : Z R a ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R a (g.exists_critical a path.start_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hat),
      g.distance_constant a path.start_color]
    change 1 < g.b R
    omega
  have hbound := fixed_index_le_of_component_intersection (Q R t)
    ((Q R t ⊓ Ltilde R a)) (Q R a) (Q R z)
    (U R a) (U R z) (fixedCore R z) (Z R a)
    (original_component_radical_sup_core h hinner path.start_color hat) hfactor hUaQ hQzT hUzQ inf_le_left
    (hTSa.trans (Q_normalized R a)) (original_fixedCore_normalized hzt) hZaT
    (by rw [commutator_comm]; exact Z_centralizes_Q R a path.start_color)
    (hcomp.trans (sup_le_sup_right hUaQ _))
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hother := (h.original_small_critical_indices_eq_field path (by omega) (by
    rw [h.field_card]
    rw [hZ]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  exact (not_le_of_gt (short_original_core_critical_fixed_index_gt_natural_index h hshort rev (by omega) (by simpa only [h.field_card] using hother))) hbound




/-- The full fixed core acts quadratically on the entire opposite Z-layer
of the original source pair, including both complete fixed attachments. -/
theorem original_fixedCore_quadratic
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ⁅⁅Z R z,fixedCore R a⁆,fixedCore R a⁆ = ⊥ := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hAT : fixedCore R a ≤ Q R t := inf_le_left.trans hQaT
  have hsmall := original_fixedCore_movement_le_square h hshort hinner hsy g hb path hat hzt
  have hA : IsPGroup 2 (fixedCore R a) :=
    (Q_isPGroup R h.radical.isPGroup h.radical.twoCore_le a path.start_color).of_injective
      (inclusion (show fixedCore R a ≤ Q R a from inf_le_left)) (inclusion_injective _)
  have hquad := original_moving_quadratic_of_small_index h hinner path.end_color
    (fixedCore R a) (hAT.trans hTSz) hA hsmall
  have hcentral : Z R t ≤ centralizer (fixedCore R a : Set (FreeAmalgam R)) := by
    have hZt : Z R t = omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
    rw [hZt]
    exact fun x hx y hy => (mem_omegaCenter_iff.mp hx).2.2 y (hAT hy)
  have hUzT : U R z ≤ Q R t :=
    ((original_component_core_intersection h hshort path.end_color).ge.trans inf_le_right).trans
      (Q_le_adjacent_h R ht hzt)
  have heq : ⁅Z R z,fixedCore R a⁆ = ⁅U R z,fixedCore R a⁆ := by
    apply le_antisymm ?_ (commutator_mono (U_le_Z z) le_rfl)
    rw [commutator_comm (Z R z),commutator_comm (U R z)]
    apply commutator_le_moving_of_inner_mod_centralizer (fixedCore R a)
      (U R z) (Z R z) (hUzT.trans (original_fixedCore_normalized hat))
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt]
    exact sup_le_sup_left hcentral _
  simpa only [heq] using hquad


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
