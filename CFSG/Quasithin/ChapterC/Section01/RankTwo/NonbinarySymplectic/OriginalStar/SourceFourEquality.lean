module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourCommonOverlap
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourEquality

/-!
# Full fixed-attachment equality in the original field-sized critical case

On the original natural cover the critical-root preimage selects a
field-sized overlap, disjoint from the complete fixed attachment. The
individual-value comparison identifies an unequal opposite attachment
with this overlap. Its movement under the common-section centralizer is
then both contained in and disjoint from that attachment, hence trivial.

The literal root-normalizer action would therefore bound the original
marked radical by q squared. The original odd-index nonsylow branch has
cubic marked order, giving the contradiction. No saturation premise for
the characteristic-minimum replacement is used.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875,
case |Z_alpha Q_alpha' / Q_alpha'| = q. Both complete covering kernels
remain present; the larger critical-image branch is a separate obligation.
The selected-star application is in SourceFour.
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

omit hshort in
/-- The original nonsylow marked action is elementary, so the opposite
critical center commutes with the full edge radical modulo the entire core. -/
theorem original_nonsylow_critical_edge_commutator_le
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ⁅Z R z,Q R t⁆ ≤ Q R a := by
  have hZT : Z R z ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1 < g.b R
    omega
  obtain ⟨δ,hδk,hδr⟩ := original_edge_marked_action h hinner path.start_color hat
  let : IsElementaryAbelian 2 δ.range := hδr.symm ▸
    (original_nonsylow_marked_elementary_card h hnsyl).1
  apply commutator_le.mpr
  intro x hx y hy
  let xT : Q R t := ⟨x,hZT hx⟩
  let yT : Q R t := ⟨y,hy⟩
  have hc : Commute (δ xT) (δ yT) :=
    congrArg Subtype.val (mul_comm (δ.rangeRestrict xT) (δ.rangeRestrict yT))
  have hk : ⁅xT,yT⁆ ∈ δ.ker := by
    change δ ⁅xT,yT⁆=1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr hc
  rw [hδk] at hk
  exact hk


omit hnsyl

/-- The actual root preimage Q Z' selects a field-sized overlap, and every
critical displacement outside the full fixed attachment is either in this
overlap or is one individual commutator of the actual moving groups. -/
theorem original_critical_root_overlap_geometry
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    :
    let S := stabilizer R a
    let T := (Q R a ⊔ Z R z).subgroupOf S
    let B := (normalizer (T : Set S)).pCoreIn 2
    let D := ⁅U R a ⊓ centralizer ((Q R a ⊔ Z R z : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)),
      B.map S.subtype⁆
    (Disjoint D (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) ∧
      Nat.card D=2^n ∧ D ≤ ⁅Z R a,Z R z⁆) ∧
    ∀ x ∈ ⁅Z R a,Z R z⁆,
      x ∉ U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) →
      x ∈ D ∨ ∃ b ∈ U R z, ∃ u ∈ U R a, ⁅b,u⁆=x := by
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
  have hγker : γ.ker=κ.ker := by
    ext x
    change e.groupEquiv (κC x)=1 ↔ κ x=1
    rw [e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
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
  let S := stabilizer R a
  have hUS : U R a ≤ S := (U_le_Z a).trans (Z_le_stabilizer R a)
  have hQS : Q R a ≤ S := fun _ hx => hx.1
  have hTS : Q R a ⊔ Z R z ≤ S := sup_le hQS hZS
  let U₀ := (U R a).subgroupOf S
  let T₀ := (Q R a ⊔ Z R z).subgroupOf S
  let jS := j.codRestrict S (fun w => hUS (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  have hjSr : jS.range=U₀ := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      change j w ∈ U R a
      exact hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)
    · intro hx
      obtain ⟨w,hw⟩ := (show x.val ∈ j.range from hjr.symm ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
  have haction (x : S) (w : s.space.toSubmodule) :
      jS (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x*jS (Multiplicative.ofAdd w)*x⁻¹ := by
    apply Subtype.ext
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hγβ (x : Z R z) : γ (inclusion hZS x)=β x := by
    exact (congrArg e.groupEquiv
      (show κC (inclusion hZS x)=e.groupEquiv.symm (β x) from
        Subtype.ext (hβmark x).symm)).trans (e.groupEquiv.apply_symm_apply _)
  have hQker : (Q R a).subgroupOf S = γ.ker := by
    rw [hγker,←hκQ,subgroupOf_map_subtype_eq]
  have hZimage : ((Z R z).subgroupOf S).map γ=β.range := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,hγβ ⟨x.val,hx⟩ |>.symm⟩
    · rintro _ ⟨x,rfl⟩
      exact ⟨inclusion hZS x,x.property,hγβ x⟩
  have hTimage : T₀.map γ=β.range := by
    change ((Q R a ⊔ Z R z).subgroupOf S).map γ=β.range
    rw [subgroupOf_sup hQS hZS,Subgroup.map_sup,hQker,
      show γ.ker.map γ=⊥ from (Subgroup.map_eq_bot_iff _).mpr le_rfl,bot_sup_eq,hZimage]
  let := finite_stabilizer R a
  have hγonto : Function.Surjective γ := by
    intro x
    obtain ⟨y,hy⟩ := hκ (e.groupEquiv.symm x).val
    exact ⟨y,(congrArg e.groupEquiv (Subtype.ext hy)).trans (e.groupEquiv.apply_symm_apply x)⟩
  have hγp : IsPGroup 2 γ.ker := by
    rw [←hQker]
    exact (Q_isPGroup R h.radical.isPGroup h.radical.twoCore_le
      a path.start_color).comap_subtype
  have hγT : γ.ker ≤ T₀ := by
    rw [←hQker]
    intro x hx
    exact (show Q R a ≤ Q R a ⊔ Z R z from le_sup_left) hx
  let A := (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup
  have hAm : (A.map jS).map S.subtype=U R a ⊓
      centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
    rw [Subgroup.map_map]
    change A.map j=_
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hxc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hxc,rfl⟩
  have hDm : (⁅U₀ ⊓ centralizer (T₀ : Set S),(normalizer (T₀ : Set S)).pCoreIn 2⁆).map
      S.subtype = ⁅U R a ⊓ centralizer ((Q R a ⊔ Z R z : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)),
        ((normalizer (T₀ : Set S)).pCoreIn 2).map S.subtype⁆ := by
    rw [map_commutator,←map_inf_centralizer_of_injective S.subtype S.subtype_injective,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS]
  have hUT : ⁅U R a,Q R a ⊔ Z R z⁆=⁅Z R a,Z R z⁆ := by
    rw [←commutator_eq_of_centralizing_sup (B := Q R a ⊔ Z R z) rfl
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R a path.start_color))).trans (centralizer_le (U_le_Z a)))
      (hZS.trans (U_normalized a))]
    exact (original_critical_displacement_eq_moving h hshort hinner path hb hat hzt).symm
  have hgeom := embedded_root_normalizer_overlap hFc h.nonbinary U₀ T₀
    (MovedSection.coverProjection s e) he jS
    (fun x y hxy => hj (congrArg Subtype.val hxy)) hjSr γ haction hγonto hγp hγT
    (by rw [hTimage]; exact hβcard) (by rw [hTimage]; exact hβdim)
    (by rw [hTimage]; exact hβquad)
  dsimp only
  constructor
  · refine ⟨?_,?_,?_⟩
    · rw [←hAm,←hDm,disjoint_iff]
      rw [←map_inf _ _ _ S.subtype_injective,disjoint_iff.mp hgeom.1,Subgroup.map_bot]
    · rw [←hDm,card_map_of_injective S.subtype_injective,hgeom.2.1,hFc]
    · have hl := map_mono (f := S.subtype) hgeom.2.2
      rwa [hDm,map_commutator,map_subgroupOf_eq_of_le hUS,
        map_subgroupOf_eq_of_le hTS,hUT] at hl
  intro x hx hn
  have hxUT : x ∈ ⁅U R a,Q R a ⊔ Z R z⁆ := by
    apply commutator_mono le_rfl le_sup_right
    rwa [←original_critical_displacement_eq_moving h hshort hinner path hb hat hzt]
  have hWU : ⁅Z R a,Z R z⁆ ≤ U R a :=
    (original_critical_paired_fixed_layers h hshort hinner path hb hat hzt hcritical).2.2.1.trans inf_le_left
  have hxS : x ∈ S := hUS (hWU hx)
  let xS : S := ⟨x,hxS⟩
  have hmUT : (⁅U₀,T₀⁆).map S.subtype=⁅U R a,Q R a ⊔ Z R z⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS]
  have hxSUT : xS ∈ ⁅U₀,T₀⁆ := (mem_map_iff_mem S.subtype_injective).mp
    (show S.subtype xS ∈ (⁅U₀,T₀⁆).map S.subtype from hmUT.symm ▸ hxUT)
  have hxSA : xS ∉ A.map jS := by
    intro hxA
    exact hn (hAm ▸ mem_map_of_mem S.subtype hxA)
  have hh := embedded_root_normalizer_value_or_overlap hFc h.nonbinary U₀ T₀
    (MovedSection.coverProjection s e) he jS hjSr γ haction hγonto hγp hγT
    (by rw [hTimage]; exact hβcard) (by rw [hTimage]; exact hβdim)
    (by rw [hTimage]; exact hβquad) xS hxSUT hxSA
  rcases hh with hh | hh
  · left
    exact hDm ▸ mem_map_of_mem S.subtype hh
  · obtain ⟨b,hbT,u,hu,he⟩ := hh
    have he' : ⁅b.val,u.val⁆=x := congrArg Subtype.val he
    have hbjoin : b.val ∈ Z R z ⊔ Q R a := by
      rw [sup_comm]
      exact hbT
    have hZQ : Z R z ≤ normalizer (Q R a : Set (FreeAmalgam R)) :=
      hZS.trans (Q_normalized R a)
    rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hZQ] at hbjoin
    obtain ⟨v,hv,c,hc,hvc⟩ := hbjoin
    have hcu : Commute c u.val :=
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R a path.start_color))) hc u.val (U_le_Z a hu)).symm
    rw [←hvc,commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr hcu] at he'
    simp only [mul_one,mul_inv_cancel,one_mul] at he'
    let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
    let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
    have htz : Z R t ≤ Z R z := Sp4Four.edge_Z_le_endpoint R path.end_color hzt
    have hta : Z R t ≤ Z R a := Sp4Four.edge_Z_le_endpoint R path.start_color hat
    have hcent : Z R t ≤ centralizer (U R z : Set (FreeAmalgam R)) :=
      htz.trans ((Z R z).le_centralizer.trans (centralizer_le (U_le_Z z)))
    have hvjoin : v ∈ U R z ⊔ Z R t := by
      rwa [←original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt]
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _
      (hcent.trans (Subgroup.centralizer_le_normalizer _))] at hvjoin
    obtain ⟨w,hw,c,hc,rfl⟩ := hvjoin
    have hcu : Commute c u.val :=
      ((hta.trans ((Z R a).le_centralizer.trans (centralizer_le (U_le_Z a)))) hc u.val hu).symm
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr hcu] at he'
    exact Or.inr ⟨w,hw,u.val,hu,by simpa only [mul_one,mul_inv_cancel,one_mul] using he'⟩



/-- If the complete paired fixed kernels differ, the opposite kernel is
exactly the overlap selected by the critical-root normalizer two-core. -/
theorem original_critical_opposite_fixed_eq_root_overlap
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (hne : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≠
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))) :
    let S := stabilizer R a
    let T := (Q R a ⊔ Z R z).subgroupOf S
    let B := (normalizer (T : Set S)).pCoreIn 2
    U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) =
      ⁅U R a ⊓ centralizer ((Q R a ⊔ Z R z : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)),B.map S.subtype⁆ := by
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  let S := stabilizer R a
  let T := (Q R a ⊔ Z R z).subgroupOf S
  let B := (normalizer (T : Set S)).pCoreIn 2
  let D := ⁅U R a ⊓ centralizer ((Q R a ⊔ Z R z : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)),B.map S.subtype⁆
  obtain ⟨hdis,hA,hA',hjoin⟩ :=
    (original_critical_fixed_kernels_dichotomy h hshort hinner path hb hat hzt hcritical).resolve_left hne
  obtain ⟨⟨_,hD,hDW⟩,hvalues⟩ := original_critical_root_overlap_geometry h hshort hinner path hb hat hzt hcritical
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hle : A' ≤ D := by
    intro x hx
    by_cases hxA : x ∈ A
    · have hx1 : x=1 := (disjoint_iff_inf_le.mp hdis) ⟨hxA,hx⟩
      exact hx1 ▸ D.one_mem
    have hxW : x ∈ ⁅Z R a,Z R z⁆ := hjoin ▸ mem_sup_right hx
    rcases hvalues x hxW hxA with hd | hv
    · exact hd
    obtain ⟨b,hbU,u,hu,he⟩ := hv
    have hc : ⁅u,b⁆ ∈ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
      rw [←commutatorElement_inv,he]
      exact inv_mem hx.2
    have he1 := original_critical_value_in_fixed_eq_one h hinner rev hb hzt
      u (U_le_Z a hu) b hbU hc
    have he2 : ⁅b,u⁆=1 := commutatorElement_eq_one_iff_commute.mpr
      (commutatorElement_eq_one_iff_commute.mp he1).symm
    exact (hxA (he.symm ▸ he2.symm ▸ A.one_mem)).elim
  let := finite_stabilizer R a
  have hDS : D ≤ S := by
    exact hDW.trans ((original_critical_paired_fixed_layers h hshort hinner path hb hat hzt hcritical).2.2.1.trans
      inf_le_left |>.trans (U_le_Z a) |>.trans (Z_le_stabilizer R a))
  let : Finite D := Finite.of_injective (inclusion hDS) (inclusion_injective _)
  exact eq_of_le_of_card_ge hle (hD.trans hA'.symm).le


include hnsyl

omit hshort in
private theorem original_critical_root_overlap_actor_bound
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (hzero :
      let S := stabilizer R a
      let T := (Q R a ⊔ Z R z).subgroupOf S
      let B := ((normalizer (T : Set S)).pCoreIn 2).map S.subtype
      ⁅U R a ⊓ centralizer
        ((Q R a ⊔ Z R z : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)),
        B ⊓ Q R t⁆=⊥) :
    (Q R a).relIndex (Q R t) ≤ (2^n)^2 := by
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
  have hγker : γ.ker=κ.ker := by
    ext x
    change e.groupEquiv (κC x)=1 ↔ κ x=1
    rw [e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
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
  let S := stabilizer R a
  have hUS : U R a ≤ S := (U_le_Z a).trans (Z_le_stabilizer R a)
  have hQS : Q R a ≤ S := fun _ hx => hx.1
  have hTS : Q R a ⊔ Z R z ≤ S := sup_le hQS hZS
  let U₀ := (U R a).subgroupOf S
  let T₀ := (Q R a ⊔ Z R z).subgroupOf S
  let jS := j.codRestrict S (fun w => hUS (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  have hjSr : jS.range=U₀ := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      change j w ∈ U R a
      exact hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)
    · intro hx
      obtain ⟨w,hw⟩ := (show x.val ∈ j.range from hjr.symm ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
  have haction (x : S) (w : s.space.toSubmodule) :
      jS (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x*jS (Multiplicative.ofAdd w)*x⁻¹ := by
    apply Subtype.ext
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hγβ (x : Z R z) : γ (inclusion hZS x)=β x := by
    exact (congrArg e.groupEquiv
      (show κC (inclusion hZS x)=e.groupEquiv.symm (β x) from
        Subtype.ext (hβmark x).symm)).trans (e.groupEquiv.apply_symm_apply _)
  have hQker : (Q R a).subgroupOf S = γ.ker := by
    rw [hγker,←hκQ,subgroupOf_map_subtype_eq]
  have hZimage : ((Z R z).subgroupOf S).map γ=β.range := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,hγβ ⟨x.val,hx⟩ |>.symm⟩
    · rintro _ ⟨x,rfl⟩
      exact ⟨inclusion hZS x,x.property,hγβ x⟩
  have hTimage : T₀.map γ=β.range := by
    change ((Q R a ⊔ Z R z).subgroupOf S).map γ=β.range
    rw [subgroupOf_sup hQS hZS,Subgroup.map_sup,hQker,
      show γ.ker.map γ=⊥ from (Subgroup.map_eq_bot_iff _).mpr le_rfl,bot_sup_eq,hZimage]
  let := finite_stabilizer R a
  have hγonto : Function.Surjective γ := by
    intro x
    obtain ⟨y,hy⟩ := hκ (e.groupEquiv.symm x).val
    exact ⟨y,(congrArg e.groupEquiv (Subtype.ext hy)).trans (e.groupEquiv.apply_symm_apply x)⟩
  have hγp : IsPGroup 2 γ.ker := by
    rw [←hQker]
    exact (Q_isPGroup R h.radical.isPGroup h.radical.twoCore_le
      a path.start_color).comap_subtype
  have hγT : γ.ker ≤ T₀ := by
    rw [←hQker]
    intro x hx
    exact (show Q R a ≤ Q R a ⊔ Z R z from le_sup_left) hx
  have hEdge : Q R t ≤ S := fun _ hx => hx.2 _ (adjacent_symm R hat)
  let J := (Q R t).subgroupOf S
  have hJ : IsPGroup 2 J := by
    have hh : IsPGroup 2 (Q R t) := by
      obtain ⟨u,⟨hau,htu⟩ | ⟨hau,htu⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
      · have ht : hVertex R u = act R u (beta R) := by simp [beta,act_hVertex]
        rw [htu,ht,Q_act,Q_beta]
        exact (h.radical.isPGroup.map _).map _
      · have hc := path.start_color
        rw [hau] at hc
        cases hc
    exact hh.comap_subtype
  have hJT : ⁅J,T₀⁆ ≤ γ.ker := by
    rw [←hQker]
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hEdge,
      map_subgroupOf_eq_of_le hTS,map_subgroupOf_eq_of_le hQS,commutator_comm]
    exact commutator_sup_le_of_relative_normal S (Q R a) (Z R z)
      (Q R t) (Q R a) (Q_normalized R a) hQS hZS
      (le_normalizer_iff_commutator_le_left.mp (hEdge.trans (Q_normalized R a)))
      (original_nonsylow_critical_edge_commutator_le h hinner hnsyl path hb hat hzt)
  have hz : ⁅U₀ ⊓ centralizer (T₀ : Set S),(normalizer (T₀ : Set S)).pCoreIn 2 ⊓ J⁆=⊥ := by
    apply map_injective S.subtype_injective
    rw [map_commutator,←map_inf_centralizer_of_injective S.subtype S.subtype_injective,
      map_inf _ _ _ S.subtype_injective,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS,
      map_subgroupOf_eq_of_le hEdge,Subgroup.map_bot]
    exact hzero
  have hh := SaturatedDistanceTwo.root_overlap_actor_bound hFc h.nonbinary U₀ T₀ J
    (MovedSection.coverProjection s e) he jS
    (fun x y hxy => hj (congrArg Subtype.val hxy)) hjSr γ haction hγonto hγp hγT
    (by rw [hTimage]; exact hβcard) (by rw [hTimage]; exact hβdim)
    (by rw [hTimage]; exact hβquad) hJ hJT hz
  have hc : Nat.card (J.map γ)=(Q R a).relIndex (Q R t) := by
    have hh := Sp4Four.SourceComparison.quotient_image_card _ _ _ hEdge γ
      (by rw [hγker,hκQ])
    rwa [MonoidHom.range_comp,inclusion_range] at hh
  rwa [hc,hFc] at hh

/-- Source (3.7)(4) for an actual critical image of order q: the two
complete moving-cover attachments agree for the original nonsylow star. -/
theorem original_source_four_of_field_critical
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
  classical
  by_contra hne
  let S := stabilizer R a
  let T := (Q R a ⊔ Z R z).subgroupOf S
  let B := ((normalizer (T : Set S)).pCoreIn 2).map S.subtype
  let P := B ⊓ Q R t
  let V := Z R a ⊓ Z R z
  let W := ⁅Z R a,Z R z⁆
  let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  have hC : U R a ⊓ centralizer
      ((Q R a ⊔ Z R z : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) =
      U R a ⊓ centralizer (Z R z : Set (FreeAmalgam R)) := by
    apply le_antisymm (inf_le_inf_left _ (centralizer_le
      (show Z R z ≤ Q R a ⊔ Z R z from le_sup_right)))
    apply le_inf inf_le_left
    apply le_centralizer_iff.mpr
    refine sup_le ?_ (le_centralizer_iff.mp inf_le_right)
    exact le_centralizer_iff.mp ((inf_le_left.trans (U_le_Z a)).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a path.start_color)))
  have he : A' = ⁅U R a ⊓ centralizer
      (Z R z : Set (FreeAmalgam R)),B⁆ := by
    have hh := original_critical_opposite_fixed_eq_root_overlap h hshort hinner path hb hat hzt hcritical hne
    dsimp only at hh
    rwa [hC] at hh
  obtain ⟨⟨_,_,hDW⟩,_⟩ := original_critical_root_overlap_geometry h hshort hinner path hb hat hzt hcritical
  rw [hC] at hDW
  have hm : ⁅U R a ⊓ centralizer
      (Z R z : Set (FreeAmalgam R)),P⁆ ≤ W :=
    (commutator_mono le_rfl inf_le_left).trans hDW
  have hVm : ⁅V,P⁆=⁅U R a ⊓ centralizer
      (Z R z : Set (FreeAmalgam R)),P⁆ :=
    original_critical_common_overlap_movement h hshort hinner hnsyl g hb path hat hzt hcritical P inf_le_right
  obtain ⟨B₀,hB₀,hmem,_,_,hdis⟩ :=
    original_source_four_common_overlap_centralizer h hshort hinner hnsyl g hb path hat hzt hcritical
  have hPB : P ≤ B₀ := by
    intro b hbP
    refine (hmem b).mpr ⟨hbP.2,?_⟩
    have hh : ⁅P,V⁆ ≤ W := by rw [commutator_comm,hVm]; exact hm
    exact fun v hv => commutator_le.mp hh b hbP v hv
  have hdisP : Disjoint ⁅V,P⁆ A' := hdis.mono_left (commutator_mono le_rfl hPB)
  have hleA : ⁅V,P⁆ ≤ A' := by
    rw [hVm,he]
    exact commutator_mono le_rfl inf_le_left
  have hz : ⁅V,P⁆=⊥ := by
    apply le_bot_iff.mp
    exact (le_inf le_rfl hleA).trans (disjoint_iff_inf_le.mp hdisP)
  have hbnd := original_critical_root_overlap_actor_bound h hinner hnsyl path hb hat hzt hcritical (by
    dsimp only
    rw [hC]
    exact hVm.symm ▸ hz)
  rw [original_nonsylow_full_radical_card h hinner hnsyl path.start_color hat] at hbnd
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  exact (not_le_of_gt (Nat.pow_lt_pow_right hq (by decide : 2 < 3))) hbnd



end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
