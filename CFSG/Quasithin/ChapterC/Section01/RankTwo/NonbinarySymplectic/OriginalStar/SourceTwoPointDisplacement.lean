module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoDisplacementBounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoPointDisplacement
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoPointCover
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoPointDisplacement

import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.ComponentIntersection

/-!
# Original-star point-radical displacement

The nonsylow original odd-index radical has elementary abelian marked image
of order q³. We extend the literal component projection over the inner
ambient group and transport it to the full common radical at each endpoint.
The entire endpoint two-core is the action kernel. Large opposite-core
movement excludes the quadratic elementary alternative, identifying the
same full natural-cover action with a point radical.

In that point radical, displacement dimension at most one would put the
fixed-core image inside the order-q component image. The cubic full-radical
index excludes this. Fixed-core movement is therefore exactly q². The
previous full-cover upper bound forces both complete fixed attachments to
have order q and the full displacement to have order q². Equality in the
fixed-index/displacement inequality makes that displacement disjoint from
the entire opposite fixed core.

The final theorem applies all of these conclusions to the selected original
star, discharging shortness, innerness and its own distance-two geometry.
No saturation or marked-image preservation of the minimum replacement is
assumed. The companion SourceTwoMidpoint proves the fixed-core index contradiction.
The original Sylow branch and field-four/block assembly remain separate obligations.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(2), printed pp.873--874, through Aα ∩ Dα′ = 1. Generic
natural-cover calculations are reused from the saturated branch; the
original radical and the literal original quotient marking are retained.
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
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- The unchanged moved section of the original omega-center action. -/
@[expose] def originalMovedSection :=
  letI := h.component_image_structure.2.1
  MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) (QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm))
    (K.map (QuotientGroup.mk' (pCore 2 H)))

/-- Original odd-index radical classification, with its literal component image. -/
theorem original_nonsylow_marked_elementary_card
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    IsElementaryAbelian 2 ((R.subgroupOf K).map (componentProjection h)) ∧
      Nat.card ((R.subgroupOf K).map (componentProjection h)) = (2^n)^3 := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨d⟩ := exists_characteristicReduction_of_core_le (L := K) h.radical.twoCore_le
  rcases original_marked_radical_alternatives h d with ⟨u,hu⟩ | hs
  · let D := (R.subgroupOf K).map (componentProjection h)
    let e := D.equivMapOfInjective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective
    have he : IsElementaryAbelian 2 (D.map (MulAut.conj u).toMonoidHom) ∧
        Nat.card (D.map (MulAut.conj u).toMonoidHom) = (2^n)^3 := by
      rcases hu with ⟨hp,_⟩ | ⟨hp,_⟩
      · rw [hp]
        exact ⟨SymplecticConjugatePair.pointRadical_elementary,
          SymplecticConjugatePair.card_pointRadical.trans (congrArg (·^3) h.field_card)⟩
      · rw [hp]
        exact ⟨SymplecticConjugatePair.planeRadical_elementary,
          SymplecticConjugatePair.card_planeRadical.trans (congrArg (·^3) h.field_card)⟩
    let := he.1
    exact ⟨IsElementaryAbelian.of_injective e.toMonoidHom e.injective,
      (Nat.card_congr e.toEquiv).trans he.2⟩
  · exact (hnsyl hs).elim

omit [Finite F] [CharP F 2] in
/-- The inner original ambient projection extends the specified component marking. -/
theorem original_inner_marked_projection (hinner : K ⊔ pCore 2 H = ⊤) :
    ∃ f : H →* Sp F, Function.Surjective f ∧ f.ker = pCore 2 H ∧
      (∀ k : K, f k = componentProjection h k) ∧
      R.map f = (R.subgroupOf K).map (componentProjection h) := by
  let π := QuotientGroup.mk' (pCore 2 H)
  let C := K.map π
  have htop : C = ⊤ := by
    have hpre : C.comap π = ⊤ := by
      rw [show C = K.map π from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact hinner
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hpre]
    exact map_top_of_surjective π (QuotientGroup.mk'_surjective _)
  let q := π.codRestrict C (fun x => htop ▸ mem_top (π x))
  have hq : Function.Surjective q := by
    intro c
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (pCore 2 H) c.val
    exact ⟨x,Subtype.ext hx⟩
  let e : C ≃* Sp F := (cComponentTwoCoreQuotientEquiv h.component).symm.trans h.quotientEquiv
  let f := e.toMonoidHom.comp q
  have hfk : f.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    have he : q.ker = π.ker := by
      ext x
      exact Subtype.ext_iff
    rw [he,QuotientGroup.ker_mk']
  have hmark (k : K) : f k = componentProjection h k := by
    change h.quotientEquiv ((cComponentTwoCoreQuotientEquiv h.component).symm
      (π.subgroupMap K k)) = _
    exact congrArg h.quotientEquiv
      ((cComponentTwoCoreQuotientEquiv h.component).symm_apply_apply (QuotientGroup.mk' _ k))
  refine ⟨f,e.surjective.comp hq,hfk,hmark,?_⟩
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨k,hk,y,hy,he⟩ := mem_sup_of_normal_right.mp (hinner.symm ▸ mem_top x)
    have hkR : k ∈ R := by
      have hh := R.mul_mem hx (R.inv_mem (h.radical.twoCore_le hy))
      simpa only [←he,mul_inv_cancel_right] using hh
    refine ⟨⟨k,hk⟩,hkR,?_⟩
    have hyf : f y = 1 := by change y ∈ f.ker; rwa [hfk]
    rw [←he,map_mul,hyf,mul_one]
    exact (hmark ⟨k,hk⟩).symm
  · rintro _ ⟨k,hk,rfl⟩
    exact ⟨k.val,hk,hmark k⟩

omit [Finite F] [CharP F 2] in
/-- The full edge actor has the entire endpoint core as kernel and the
unchanged original component-radical image as range. -/
theorem original_edge_marked_action (hinner : K ⊔ pCore 2 H = ⊤)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    ∃ δ : Q R t →* Sp F,
      δ.ker = (Q R a).subgroupOf (Q R t) ∧
      δ.range = (R.subgroupOf K).map (componentProjection h) := by
  obtain ⟨u,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
  swap
  · cases ha
  let i := (MulAut.conj u⁻¹).toMonoidHom.comp (embedM R)
  have hi : Function.Injective i := (MulAut.conj u⁻¹).injective.comp (embedM_injective R)
  have ha : act R u (alpha R) = mVertex R u := by simp only [alpha,act_mVertex,one_mul]
  have ht : act R u (beta R) = hVertex R u := by simp only [beta,act_hVertex,one_mul]
  have hir : i.range = stabilizer R (mVertex R u) := by
    dsimp only [i]
    rw [MonoidHom.range_comp]
    change (Mbar R).map (MulAut.conj u⁻¹).toMonoidHom = _
    rw [←stabilizer_m_base,←stabilizer_act,act_mVertex,one_mul]
  have hiQ : (pCore 2 H).map i = Q R (mVertex R u) := by
    dsimp only [i]
    rw [←map_map,←Q_alpha R h.radical.isPGroup h.radical.twoCore_le,←Q_act,ha]
  have hiT : R.map i = Q R (hVertex R u) := by
    dsimp only [i]
    rw [←map_map,←Q_beta,←Q_act,ht]
  obtain ⟨f,hf,hk,hm,he⟩ := original_inner_marked_projection h hinner
  let κ := ElementaryMovedCover.embeddedQuotient f i hi _ hir
  have hκQ : κ.ker.map (stabilizer R (mVertex R u)).subtype = Q R (mVertex R u) := by
    rw [ElementaryMovedCover.embeddedQuotient_kernel,hk,hiQ]
  have hκT : ((Q R (hVertex R u)).subgroupOf (stabilizer R (mVertex R u))).map κ =
      (R.subgroupOf K).map (componentProjection h) := by
    rw [←hiT,ElementaryMovedCover.embeddedQuotient_subgroup,he]
  have hTS : Q R (hVertex R u) ≤ stabilizer R (mVertex R u) := by
    rw [←hiT,←hir]
    exact map_le_range _ _
  let δ := κ.comp (inclusion hTS)
  refine ⟨δ,?_,?_⟩
  · have hkκ : κ.ker = (Q R (mVertex R u)).subgroupOf (stabilizer R (mVertex R u)) := by
      rw [←hκQ,subgroupOf_map_subtype_eq]
    rw [show δ=κ.comp (inclusion hTS) from rfl,←MonoidHom.comap_ker,hkκ,comap_inclusion_subgroupOf]
  · rw [show δ=κ.comp (inclusion hTS) from rfl,MonoidHom.range_comp,inclusion_range,hκT]

/-- The original nonsylow full radical has cubic endpoint quotient order. -/
theorem original_nonsylow_full_radical_card (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    (Q R a).relIndex (Q R t) = (2^n)^3 := by
  obtain ⟨δ,hδk,hδr⟩ := original_edge_marked_action h hinner ha hat
  rw [relIndex,←hδk,index_ker,hδr]
  exact (original_nonsylow_marked_elementary_card h hnsyl).2

variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include hshort hinner

omit hshort in
theorem original_source_two_large_radical_point_cover
    (g : Geometry R) (_hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    Nonempty (SaturatedDistanceTwo.RadicalPointCover R (originalMovedSection h) n z t) := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  obtain ⟨δ,hδk,hδr⟩ := original_edge_marked_action h hinner path.end_color hzt
  let := h.component_normal
  let s := originalMovedSection h
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.end_color
  have hCtop : K.map (QuotientGroup.mk' (pCore 2 H)) = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (K.map (QuotientGroup.mk' (pCore 2 H))) (fun x => hCtop ▸ mem_top (κ x))
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
  let er := (QuotientGroup.quotientKerEquivRange α).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hαker.trans hδk.symm)).trans
      (QuotientGroup.quotientKerEquivRange δ))
  let : IsElementaryAbelian 2 δ.range := hδr.symm ▸
    (original_nonsylow_marked_elementary_card h hnsyl).1
  let : IsElementaryAbelian 2 α.range :=
    IsElementaryAbelian.of_surjective er.symm.toMonoidHom er.symm.surjective
  have hc : Nat.card α.range = Nat.card E.Carrier^3 := by
    rw [←index_ker,hαker]
    change (Q R z).relIndex (Q R t)=_
    rw [original_nonsylow_full_radical_card h hinner hnsyl path.end_color hzt,
      E.card_eq,hE]
  refine ⟨{ toAmbientVertexCover := ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,
              hfaith,hsemi,hconj,hproj,hker⟩
            edge_le := hTSz
            actor := β
            actor_marking := ?_
            actor_conjugation := hact
            actor_kernel := hαker
            point_image := ?_ }⟩
  · intro u
    exact congrArg Subtype.val (e.groupEquiv.symm_apply_apply (κC (inclusion hTSz u)))
  · apply MaximalElementary.conjugate_point_of_not_quadratic
      (E.card_eq.trans (congrArg (2^·) hE)) (by have := h.nonbinary; omega)
      α.range hc
    intro hq
    have hdim := TwoLocalCover.finrank_le_two_of_isotropic (displacementSpace α.range)
      (quadratic_displacement_isotropic α.range hq)
    have hi := cover_moving_index (MovedSection.coverAction s e)
      (MovedSection.coverProjection s e) he (U R z) (Q R t)
      j hj hjr β hact
    have hsmall : (centralizer (Q R t : Set (FreeAmalgam R))).relIndex
        (U R z) ≤ (2^n)^2 := by
      rw [hi]
      have hh := Nat.pow_le_pow_right (show 0 < Nat.card E.Carrier from Nat.card_pos) hdim
      simpa only [E.card_eq,hE] using hh
    let := finite_Z R z
    let : Finite (U R z) := Finite.of_injective
      (inclusion (U_le_Z z)) (inclusion_injective _)
    have hmono := relIndex_le_of_le_left (centralizer_le hQaT)
      (show (centralizer (Q R t : Set (FreeAmalgam R))).relIndex
        (U R z) ≠ 0 from index_ne_zero_of_finite)
    exact hlarge.not_ge (hmono.trans hsmall)

/-- T₀D has the same full index as UD in Q. -/
theorem original_component_fixedCore_relIndex
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    ((Q R t ⊓ Ltilde R a) ⊔ fixedCore R a).relIndex (Q R t) =
        (U R a ⊔ fixedCore R a).relIndex (Q R a) ∧
      ((Q R t ⊓ Ltilde R a) ⊔ fixedCore R a).relIndex (Q R t) ≤ 2^n := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all
  have hQT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hTS : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hBn : Q R t ≤ normalizer ((Q R t ⊓ Ltilde R a) : Set (FreeAmalgam R)) :=
    (le_inf (Q R t).le_normalizer (hTS.trans (original_residual_normalized a))).trans
      inf_normalizer_le_normalizer_inf
  have hBQ : (Q R t ⊓ Ltilde R a) ⊓ Q R a = U R a := by
    calc
      _ = Ltilde R a ⊓ Q R a := by
        ext x
        exact ⟨fun hx => ⟨hx.1.2,hx.2⟩,fun hx => ⟨⟨hQT hx.2,hx.1⟩,hx.2⟩⟩
      _ = _ := original_component_core_intersection h hshort ha
  have he := SaturatedDistanceTwo.index_of_normal_supplement (Q R t) (Q R a)
    (Q R t ⊓ Ltilde R a) (fixedCore R a)
    (original_component_radical_sup_core h hinner ha hat) inf_le_left
    hBn (original_fixedCore_normalized hat)
  rw [hBQ] at he
  exact ⟨he,he.trans_le (short_original_core_relIndex_natural_sup_fixed_le h hshort ha)⟩

private theorem original_source_two_large_fixedCore_not_le_component_sup
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    ¬ fixedCore R a ≤ (Q R t ⊓ Ltilde R a) ⊔ Q R z := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective
    (inclusion hTSz) (inclusion_injective _)
  let : ((Q R z).subgroupOf (Q R t)).Normal := normal_subgroupOf_of_le_normalizer (hTSz.trans (Q_normalized R z))
  have hBT : (Q R t ⊓ Ltilde R a) ≤ Q R t := inf_le_left
  have hDT : fixedCore R a ≤ Q R t := inf_le_left.trans hQaT
  intro hDle
  let X := (Q R t ⊓ Ltilde R a) ⊔ fixedCore R a
  have hXT : X ≤ Q R t := sup_le hBT hDT
  have hXle : X ≤ (Q R t ⊓ Ltilde R a) ⊔ Q R z := sup_le le_sup_left hDle
  have hrel : (Q R z).relIndex X ≤ 2^n := by
    have hh := relIndex_le_of_le_right hXle (show
      (Q R z).relIndex ((Q R t ⊓ Ltilde R a) ⊔ Q R z) ≠ 0 from by
        let : Finite ((Q R t ⊓ Ltilde R a) ⊔ Q R z : Subgroup (FreeAmalgam R)) := Finite.of_injective
          (inclusion (sup_le hBT hQzT)) (inclusion_injective _)
        exact index_ne_zero_of_finite)
    rw [←relIndex_subgroupOf (sup_le hBT hQzT),
      subgroupOf_sup hBT hQzT,relIndex_sup_right,relIndex_subgroupOf hBT,
      (original_large_movement_images h hshort hinner hnsyl g hb path hat hzt hlarge).1] at hh
    exact hh
  have hi := index_le_relative_product ((Q R z).subgroupOf (Q R t))
    (X.subgroupOf (Q R t))
  rw [relIndex_subgroupOf hXT] at hi
  change (Q R z).relIndex (Q R t) ≤
    (Q R z).relIndex X * X.relIndex (Q R t) at hi
  have hXindex := (original_component_fixedCore_relIndex h hshort hinner path.start_color hat).2
  have hc := original_nonsylow_full_radical_card h hinner hnsyl path.end_color hzt
  rw [hc] at hi
  have hle : (2^n)^3 ≤ (2^n)^2 := hi.trans (by
    simpa only [pow_two] using Nat.mul_le_mul hrel hXindex)
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  exact (not_le_of_gt (Nat.pow_lt_pow_right hq (by decide : 2 < 3))) hle

theorem original_source_two_large_fixedCore_movement_eq_square
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (centralizer (fixedCore R a : Set (FreeAmalgam R))).relIndex
      (U R z) = (2^n)^2 := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := h.component_normal
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective
    (inclusion hTSz) (inclusion_injective _)
  let : ((Q R z).subgroupOf (Q R t)).Normal := normal_subgroupOf_of_le_normalizer (hTSz.trans (Q_normalized R z))
  let s := originalMovedSection h
  obtain ⟨pc⟩ := original_source_two_large_radical_point_cover h hinner g hb hnsyl path hat hzt hlarge
  let E := pc.field
  let α := (commutator (Sp E.Carrier)).subtype.comp pc.actor
  have hAT : Q R a ≤ Q R t := hQaT
  have hBT : (Q R t ⊓ Ltilde R a) ≤ Q R t := inf_le_left
  have hDT : fixedCore R a ≤ Q R t := inf_le_left.trans hAT
  let βA := pc.actor.comp (inclusion hAT)
  let βB := pc.actor.comp (inclusion hBT)
  let βD := pc.actor.comp (inclusion hDT)
  let αB := (commutator (Sp E.Carrier)).subtype.comp βB
  let αD := (commutator (Sp E.Carrier)).subtype.comp βD
  have hBker : αB.ker = (Q R z).subgroupOf ((Q R t ⊓ Ltilde R a)) := by
    change (α.comp (inclusion hBT)).ker = _
    rw [←MonoidHom.comap_ker,pc.actor_kernel,comap_inclusion_subgroupOf]
  have hBcard : Nat.card αB.range = Nat.card E.Carrier := by
    rw [←index_ker,hBker]
    change (Q R z).relIndex ((Q R t ⊓ Ltilde R a))=_
    rw [(original_large_movement_images h hshort hinner hnsyl g hb path hat hzt hlarge).1,
      E.card_eq,pc.degree]
  have hBdim : Module.finrank E.Carrier (displacementSpace αB.range) ≤ 1 := by
    apply cover_large_movement_displacement_bound (MovedSection.coverAction s pc.equiv)
      (MovedSection.coverProjection s pc.equiv) pc.cover (U R z)
      (Q R a) ((Q R t ⊓ Ltilde R a)) pc.embedding pc.injective pc.range_eq βA βB
      (fun x => pc.actor_conjugation (inclusion hAT x))
      (fun x => pc.actor_conjugation (inclusion hBT x))
      (by simpa only [pc.field.card_eq,pc.degree] using hlarge)
    exact le_antisymm ((commutator_mono (commutator_mono (U_le_Z z) le_rfl) le_rfl).trans
      (original_component_radical_triples h hshort hinner hnsyl g hb path hat hzt).2.le) bot_le
  have hiD := cover_moving_index (MovedSection.coverAction s pc.equiv)
    (MovedSection.coverProjection s pc.equiv) pc.cover (U R z)
    (fixedCore R a) pc.embedding pc.injective pc.range_eq βD
    (fun x => pc.actor_conjugation (inclusion hDT x))
  have hsmall := original_fixedCore_movement_le_square h hshort hinner hnsyl g hb path hat hzt
  have hfield : Nat.card E.Carrier = 2^n := E.card_eq.trans (congrArg (2^·) pc.degree)
  have hdimupper : Module.finrank E.Carrier (displacementSpace αD.range) ≤ 2 := by
    have hp : Nat.card E.Carrier ^ Module.finrank E.Carrier (displacementSpace αD.range) ≤
        Nat.card E.Carrier ^ 2 := (hiD.symm.trans_le hsmall).trans_eq (congrArg (·^2) hfield.symm)
    exact (pow_le_pow_iff_right₀ (Finite.one_lt_card : 1 < Nat.card E.Carrier)).mp hp
  have hdimlower : ¬ Module.finrank E.Carrier (displacementSpace αD.range) ≤ 1 := by
    intro hDdim
    obtain ⟨δ,hδk,hδr⟩ := original_edge_marked_action h hinner path.end_color hzt
    let er := (QuotientGroup.quotientKerEquivRange α).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (pc.actor_kernel.trans hδk.symm)).trans
        (QuotientGroup.quotientKerEquivRange δ))
    let : IsElementaryAbelian 2 δ.range := hδr.symm ▸
      (original_nonsylow_marked_elementary_card h hnsyl).1
    let : IsElementaryAbelian 2 α.range :=
      IsElementaryAbelian.of_surjective er.symm.toMonoidHom er.symm.surjective
    obtain ⟨v,hv⟩ := pc.point_image
    have hDB : αD.range ≤ αB.range := point_small_displacement_le_root α.range αB.range αD.range
      (by rintro _ ⟨x,rfl⟩; exact ⟨inclusion hBT x,rfl⟩)
      (by rintro _ ⟨x,rfl⟩; exact ⟨inclusion hDT x,rfl⟩) hBdim hBcard hDdim v hv
    have hDle : fixedCore R a ≤ (Q R t ⊓ Ltilde R a) ⊔ Q R z := by
      intro x hx
      obtain ⟨b,hb⟩ := hDB (show αD ⟨x,hx⟩ ∈ αD.range from ⟨_,rfl⟩)
      have hker : (inclusion hBT b)⁻¹ * inclusion hDT ⟨x,hx⟩ ∈ α.ker := by
        change α ((inclusion hBT b)⁻¹ * inclusion hDT ⟨x,hx⟩)=1
        rw [map_mul,map_inv]
        change (αB b)⁻¹ * αD ⟨x,hx⟩ = 1
        rw [hb,inv_mul_cancel]
      rw [pc.actor_kernel] at hker
      have hm := ((Q R t ⊓ Ltilde R a) ⊔ Q R z).mul_mem
        (mem_sup_left b.property) (mem_sup_right hker)
      change b.val * (b.val⁻¹*x) ∈ _ at hm
      simpa only [mul_inv_cancel_left] using hm
    exact original_source_two_large_fixedCore_not_le_component_sup h hshort hinner g hb hnsyl path hat hzt hlarge hDle
  have hdim : Module.finrank E.Carrier (displacementSpace αD.range)=2 := by omega
  rw [hiD]
  change Nat.card E.Carrier ^ Module.finrank E.Carrier (displacementSpace αD.range)=_
  rw [hdim,hfield]

omit hshort hinner in
/-- The full fixed attachment in the original natural cover has order at most q. -/
theorem original_moving_fixed_attachment_card_le_field
    {a : Vertex R} (ha : color R a = false) :
    Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R)) ≤ 2^n := by
  let := h.component_normal
  let s := originalMovedSection h
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex ha
  let pc : AmbientVertexCover R (originalMovedSection h) n a :=
    ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩
  have hk : (MovedSection.coverProjection s pc.equiv).toLinearMap.ker.toAddSubgroup.toSubgroup.map
      pc.embedding = U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨pc.range_eq ▸ ⟨w,rfl⟩,(pc.kernel w.toAdd).mp hw⟩
    · intro x hx
      obtain ⟨w,rfl⟩ := (pc.range_eq.symm ▸ hx.1 : x ∈ pc.embedding.range)
      exact ⟨w,(pc.kernel w.toAdd).mpr hx.2,rfl⟩
  have hbound := embedded_kernel_card_le_field (MovedSection.coverAction s pc.equiv)
    (MovedSection.coverProjection s pc.equiv) pc.cover pc.embedding pc.injective
  rw [hk,pc.field.card_eq,pc.degree] at hbound
  exact hbound

/-- The source point-radical squeeze determines the full displacement and
both original fixed attachments without discarding a central kernel. -/
theorem original_source_two_large_fixed_attachment_displacement_card
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
    let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
    let C := ⁅Z R z,fixedCore R a⁆
    Nat.card A = 2^n ∧ Nat.card A' = 2^n ∧ Nat.card C = (2^n)^2 ∧ A ≤ C := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := h.component_normal
  let s := originalMovedSection h
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let C := ⁅Z R z,fixedCore R a⁆
  let W := ⁅Z R a,Z R z⁆
  change Nat.card A = 2^n ∧ _ ∧ Nat.card C = (2^n)^2 ∧ A ≤ C
  obtain ⟨pc⟩ := original_source_two_large_radical_point_cover h hinner g hb hnsyl path hat hzt hlarge
  have hDT : fixedCore R a ≤ Q R t := inf_le_left.trans hQaT
  let β := pc.actor.comp (inclusion hDT)
  have hlow := HyperplaneMovement.embedded_fixed_index_le_commutator_card
    (MovedSection.coverAction s pc.equiv) (MovedSection.coverProjection s pc.equiv) pc.cover
    (U R z) (fixedCore R a) pc.embedding pc.injective pc.range_eq β
    (fun x => pc.actor_conjugation (inclusion hDT x))
  have hmove : ⁅fixedCore R a,U R z⁆ = C := by
    rw [commutator_comm]
    exact (original_fixedCore_displacement_eq_moving h hshort hinner g hb path hat hzt).symm
  rw [original_source_two_large_fixedCore_movement_eq_square h hshort hinner g hb hnsyl path hat hzt hlarge,
    hmove] at hlow
  have hupper := original_source_two_large_displacement_card h hshort hinner g hb hnsyl path hat hzt hlarge
  have hA := original_moving_fixed_attachment_card_le_field h path.start_color
  have hq : 0 < 2^n := by positivity
  have hAc : Nat.card A = 2^n := by change Nat.card C ≤ 2^n * Nat.card A at hupper; nlinarith
  have hCc : Nat.card C = (2^n)^2 := by
    change Nat.card C ≤ 2^n * Nat.card A at hupper
    rw [hAc] at hupper
    nlinarith
  have hlayers := original_critical_paired_fixed_layers h hshort hinner path hb hat hzt
    (original_large_movement_images h hshort hinner hnsyl g hb path hat hzt hlarge).2.2.1
  refine ⟨hAc,hlayers.2.2.2.2.symm.trans hAc,hCc,?_⟩
  let := finite_Z R a
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a))) (inclusion_injective _)
  let : Finite (W ⊓ C : Subgroup (FreeAmalgam R)) := Finite.of_injective
    (inclusion (original_critical_commutator_inf_fixedCore_displacement h hshort hinner path hb hat hzt)) (inclusion_injective _)
  have hindex := original_source_two_large_displacement_index h hshort hinner g hb hnsyl path hat hzt hlarge
  have hmul : Nat.card (W ⊓ C : Subgroup (FreeAmalgam R)) * W.relIndex C = Nat.card C := by
    have hh := ((W ⊓ C).subgroupOf C).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show W ⊓ C ≤ C from inf_le_right)).toEquiv] at hh
    change Nat.card (W ⊓ C : Subgroup (FreeAmalgam R)) * (W ⊓ C).relIndex C = Nat.card C at hh
    rwa [inf_relIndex_right] at hh
  have hge : Nat.card A ≤ Nat.card (W ⊓ C : Subgroup (FreeAmalgam R)) := by
    rw [hAc]
    change W.relIndex C ≤ 2^n at hindex
    rw [hCc] at hmul
    nlinarith
  have he := Subgroup.eq_of_le_of_card_ge (original_critical_commutator_inf_fixedCore_displacement h hshort hinner path hb hat hzt) hge
  exact he.symm.le.trans inf_le_right

set_option maxHeartbeats 1000000 in
private theorem original_pointCover_displacement_disjoint_fixedCore
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (pc : SaturatedDistanceTwo.RadicalPointCover R (originalMovedSection h) n z t)
    (hsize : (centralizer (fixedCore R a : Set (FreeAmalgam R))).relIndex
      (U R z) = Nat.card (⁅Z R z,fixedCore R a⁆ : Subgroup (FreeAmalgam R))) :
    Disjoint ⁅Z R z,fixedCore R a⁆ (fixedCore R z) := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := h.component_normal
  let := finite_Z R z
  let : Finite (U R z) := Finite.of_injective
    (inclusion (U_le_Z z)) (inclusion_injective _)
  let s := originalMovedSection h
  have hDT : fixedCore R a ≤ Q R t := inf_le_left.trans hQaT
  have hnorm : fixedCore R a ≤ normalizer (U R z : Set (FreeAmalgam R)) :=
    hDT.trans (hTSz.trans (U_normalized z))
  let β := pc.actor.comp (inclusion hDT)
  have hk : (MovedSection.coverProjection s pc.equiv).toLinearMap.ker.toAddSubgroup.toSubgroup.map
      pc.embedding = U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨pc.range_eq ▸ ⟨w,rfl⟩,(pc.kernel w.toAdd).mp hw⟩
    · intro x hx
      obtain ⟨w,rfl⟩ := (pc.range_eq.symm ▸ hx.1 : x ∈ pc.embedding.range)
      exact ⟨w,(pc.kernel w.toAdd).mpr hx.2,rfl⟩
  have hmove : ⁅fixedCore R a,U R z⁆ = ⁅Z R z,fixedCore R a⁆ := by
    rw [commutator_comm]
    exact (original_fixedCore_displacement_eq_moving h hshort hinner g hb path hat hzt).symm
  have hsize' : (centralizer (fixedCore R a : Set (FreeAmalgam R))).relIndex
      (U R z) = Nat.card (⁅fixedCore R a,U R z⁆ : Subgroup (FreeAmalgam R)) := by
    rw [hmove]
    exact hsize
  have hdis := embedded_displacement_disjoint_kernel_of_card
    (MovedSection.coverAction s pc.equiv) (MovedSection.coverProjection s pc.equiv) pc.cover
    (U R z) (fixedCore R a) pc.embedding pc.injective pc.range_eq β
    (fun x => pc.actor_conjugation (inclusion hDT x)) hnorm hsize'
  rw [hmove,hk] at hdis
  have hCU : ⁅Z R z,fixedCore R a⁆ ≤ U R z := by
    rw [←hmove]
    exact le_normalizer_iff_commutator_le_right.mp hnorm
  have hfull : Disjoint ⁅Z R z,fixedCore R a⁆ (fixedCore R z) := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hz
    exact Subgroup.disjoint_def.mp hdis hx ⟨hCU hx,hz.2⟩
  exact hfull

/-- The full fixed-core displacement is disjoint from the opposite
entire fixed core; in particular the first attachment meets that core trivially. -/
theorem original_source_two_large_displacement_disjoint_opposite_fixedCore
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    Disjoint ⁅Z R z,fixedCore R a⁆ (fixedCore R z) ∧
      Disjoint (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)))
        (fixedCore R z) := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  obtain ⟨pc⟩ := original_source_two_large_radical_point_cover h hinner g hb hnsyl path hat hzt hlarge
  have hcards := original_source_two_large_fixed_attachment_displacement_card h hshort hinner g hb hnsyl path hat hzt hlarge
  have hsize := (original_source_two_large_fixedCore_movement_eq_square h hshort hinner g hb hnsyl path hat hzt hlarge).trans
    hcards.2.2.1.symm
  have hfull := original_pointCover_displacement_disjoint_fixedCore h hshort hinner g hb path hat hzt pc hsize
  exact ⟨hfull,hfull.mono_left hcards.2.2.2⟩

omit hshort hinner in
/-- The point-radical displacement comparison on the actual original star,
with its restricted original odd-index witness and unchanged quotient marking. -/
theorem exists_source_star_point_displacement
    (d : CharacteristicReduction K R) (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       let S := T.subgroupOf M
       ∃ hs : Input (K.subgroupOf M) S n F, ∃ gs : Geometry S,
         hs.quotientEquiv = (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv ∧
         S = R.subgroupOf M ∧
         (normalizer (S : Set M)).pCoreIn 2 = S ∧
         ((T.subgroupOf K).map (componentProjection h)) =
           (R.subgroupOf K).map (componentProjection h) ∧
         gs.b S = 2 ∧
         ∀ (a z t : Vertex S) (_path : CriticalPath S gs a z),
           Adjacent S a t → Adjacent S z t →
           (2^n)^2 < (centralizer (Q S a : Set (FreeAmalgam S))).relIndex (U S z) →
           (let A := U S a ⊓ centralizer (Ltilde S a : Set (FreeAmalgam S))
            let A' := U S z ⊓ centralizer (Ltilde S z : Set (FreeAmalgam S))
            let C := ⁅Z S z,fixedCore S a⁆
            (centralizer (fixedCore S a : Set (FreeAmalgam S))).relIndex (U S z) = (2^n)^2 ∧
              Nat.card A = 2^n ∧ Nat.card A' = 2^n ∧ Nat.card C = (2^n)^2 ∧
              A ≤ C ∧ Disjoint C (fixedCore S z))) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl,gs,hgs⟩ :=
    exists_source_star_intrinsic_distance_two h d g hb
  have hshort := (short_and_natural_of_distance_two h d g hb).1
  have hstarshort : IsShort (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype)) :=
    hshort.of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm
  have hstar_nsyl : ¬ ∃ S' : Sylow 2 (Sp F), (S' : Subgroup (Sp F)) =
      ((((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)).subgroupOf
          (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))).map (componentProjection hs) := by
    intro he
    exact hnsyl ((original_sylow_iff_marked_sylow h).mp
      (hsyl.mp ((original_sylow_iff_marked_sylow hs).mpr he)))
  refine ⟨P,Y,hY,hn,hmin,hs,gs,hquot,hrest,hsat,hmark,hgs,?_⟩
  intro a z t path hat hzt hlarge
  obtain ⟨hA,hA',hC,hAC⟩ := original_source_two_large_fixed_attachment_displacement_card
    hs hstarshort hinner gs hgs hstar_nsyl path hat hzt hlarge
  exact ⟨original_source_two_large_fixedCore_movement_eq_square
      hs hstarshort hinner gs hgs hstar_nsyl path hat hzt hlarge,
    hA,hA',hC,hAC,(original_source_two_large_displacement_disjoint_opposite_fixedCore
      hs hstarshort hinner gs hgs hstar_nsyl path hat hzt hlarge).1⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
