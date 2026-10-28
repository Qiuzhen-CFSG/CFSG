module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.FullCore
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.FullCenterTriples

/-!
# The original full-core index squeeze in MS93 (3.7)(2)

The whole original core has a natural dual cover after quotienting by its
complete fixed attachment.  The corresponding H¹ quotient has binary
dimension at most `n`, so the full quotient index is at most `2^n`.
Four conjugates of a critical root then force its fixed-core index to exceed
the natural index.  These are the source estimates on printed p.873, with
the original radical, original quotient marking and all fixed layers retained.

This file deliberately stops at the index squeeze.  The later exclusion of
large fixed-core movement still needs the source point-radical comparison and
must not be imported from the minimum replacement without its saturation
hypothesis.
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
variable (d : CharacteristicReduction K R)
include h

omit h d [Finite H] in
private theorem original_natural_dualCover_quotient_bound
    {E W : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (i : (binaryNatural (K := E)).IntertwiningMap σ)
    (hi : Function.Injective i) (hd : IsDualCover i.range) :
    Module.finrank (ZMod 2) (W ⧸ i.toLinearMap.range) ≤
      Module.finrank (ZMod 2) E := by
  have hr := LinearMap.finrank_le_finrank_of_injective
    (quotientToH1_injective i.range hd.1 hd.2)
  let e := LinearEquiv.ofInjective i.toLinearMap hi
  have he : ∀ g v, e ((binaryNatural (K := E)) g v) =
      i.range.toRepresentation g (e v) := by
    intro g v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining (binaryNatural (K := E)) σ i g v
  let ec := H1Congr (binaryNatural (K := E)) i.range.toRepresentation
    (MulEquiv.refl _) e he
  rw [←ec.finrank_eq,finrank_restrictScalars,
    Representation.OneCohomology.SymplecticFour.finrank_H1_eq_one,
    mul_one] at hr
  exact hr

/-- The original full quotient has index at most the field size after the
complete fixed attachment is included in the denominator. -/
theorem original_core_relIndex_natural_sup_fixed_le
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex R} (ha : color R a = false) :
    (U R a ⊔ fixedCore R a).relIndex (Q R a) ≤ 2^n := by
  obtain ⟨E,hE,s,γ,hγinj,hγ,hmap,i,hi,hd,hrange,_⟩ :=
    original_wholeKernel_natural_dualCover h d g hb ha
  have hrank := original_natural_dualCover_quotient_bound (s.action.comp γ) i hi hd
  have hdegree : Module.finrank (ZMod 2) E.Carrier = n := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E.Carrier)
    rw [Nat.card_zmod,E.card_eq,hE] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm
  rw [hdegree] at hrank
  let V := i.toLinearMap.range
  let π := s.sectionData.coordinates
  let f : Q R a →* Multiplicative (s.Carrier ⧸ V) :=
    V.mkQ.toAddMonoidHom.toMultiplicative.comp π
  have hf : Function.Surjective f := V.mkQ_surjective.comp s.sectionData.onto
  have hV : V.toAddSubgroup.toSubgroup =
      ((U R a).subgroupOf (Q R a)).map π := by
    ext w
    change w.toAdd ∈ i.toLinearMap.range ↔ _
    rw [hrange]
    constructor
    · rintro ⟨x,hx,he⟩
      exact ⟨x,hx,Multiplicative.toAdd.injective he⟩
    · rintro ⟨x,hx,he⟩
      exact ⟨x,hx,congrArg Multiplicative.toAdd he⟩
  have hk : f.ker = (V.toAddSubgroup.toSubgroup).comap π := by
    ext x
    change V.mkQ (π x).toAdd = 0 ↔ (π x).toAdd ∈ V
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  have hUQ : U R a ≤ Q R a := by
    obtain ⟨geometry,hpos,_⟩ := h.positive_even_geometry
    apply (U_le_Z _).trans
    exact (geometry.omega_bound a ha (by
      rw [geometry.distance_constant a ha]; exact hpos)).trans (omegaCenter_le _)
  have hkernel : f.ker.map (Q R a).subtype =
      U R a ⊔ fixedCore R a := by
    rw [hk,hV,comap_map_eq,Subgroup.map_sup,s.sectionData.kernel_eq,
      map_subgroupOf_eq_of_le hUQ,map_subgroupOf_eq_of_le s.sectionData.kernel_le]
    rfl
  have hindex : (U R a ⊔ fixedCore R a).relIndex (Q R a) =
      Nat.card (s.Carrier ⧸ V) := by
    rw [←hkernel]
    have hh := relIndex_map_map_of_injective (f := (Q R a).subtype)
      f.ker ⊤ (Q R a).subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype,relIndex_top_right,index_ker,
      MonoidHom.range_eq_top.mpr hf,
      Nat.card_congr (topEquiv :
        (⊤ : Subgroup (Multiplicative (s.Carrier ⧸ V))) ≃* _).toEquiv] at hh
    exact hh
  rw [hindex,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) hrank

/- The natural dual-cover image has dimension `4n`; the quotient index
   therefore factors through the complete fixed attachment as in (3.7). -/
theorem original_core_fixed_index_eq_natural_mul
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex R} (ha : color R a = false) :
    (fixedCore R a).relIndex (Q R a) = (2^n)^4 *
      (U R a ⊔ fixedCore R a).relIndex (Q R a) := by
  obtain ⟨E,hE,s,γ,hγinj,hγ,hmap,i,hi,hd,hrange,_⟩ :=
    original_wholeKernel_natural_dualCover h d g hb ha
  obtain ⟨geometry,hpos,_⟩ := h.positive_even_geometry
  have hUQ : U R a ≤ Q R a :=
    (U_le_Z a).trans ((geometry.omega_bound a ha (by
      rw [geometry.distance_constant a ha]; exact hpos)).trans (omegaCenter_le _))
  have himage : s.sectionData.imageSpace (U R a) = i.toLinearMap.range := by
    ext w
    rw [hrange,s.sectionData.mem_imageSpace_iff]
  have hiU : (fixedCore R a).relIndex (U R a) = (2^n)^4 := by
    have hic : Nat.card (s.sectionData.imageSpace (U R a)) =
        (fixedCore R a).relIndex (U R a) :=
      s.sectionData.imageSpace_card_eq_relIndex (U R a) hUQ
    rw [←hic,himage,
      ←Nat.card_congr (LinearEquiv.ofInjective i.toLinearMap hi).toEquiv]
    rw [Module.natCard_eq_pow_finrank (K := E.Carrier)]
    simp [Natural,E.card_eq,hE]
  let : ((fixedCore R a).subgroupOf (Q R a)).Normal :=
    s.sectionData.kernel_normal
  have hiUD : (fixedCore R a).relIndex (U R a ⊔ fixedCore R a) = (2^n)^4 := by
    rw [←relIndex_subgroupOf
      (sup_le hUQ (show fixedCore R a ≤ Q R a from inf_le_left)),
      subgroupOf_sup hUQ (show fixedCore R a ≤ Q R a from inf_le_left),
      relIndex_sup_right,relIndex_subgroupOf hUQ,hiU]
  exact (relIndex_mul_relIndex (fixedCore R a)
    (U R a ⊔ fixedCore R a) (Q R a) le_sup_right
    (sup_le hUQ inf_le_left)).symm.trans (by rw [hiUD])

theorem original_core_fixed_index_le_critical_index_pow_four
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hpos : 0 < geometry.b R)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n) :
    (fixedCore R a).relIndex (Q R a) ≤
      ((commutatorPreimage (Q R a) (Z R z)
        (fixedCore R a)).relIndex (Q R a))^4 := by
  let := h.component_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := h.component_image_structure.2.1
  let s₀ := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  obtain ⟨s,hs⟩ := original_wholeKernelQuotient_over h d g hb path.start_color κ hκ hκQ
  let B := K.map (QuotientGroup.mk' (pCore 2 H))
  let γ := B.subtype.comp e.groupEquiv.symm.toMonoidHom
  have hZQ : Z R a ≤ Q R a :=
    (geometry.omega_bound a path.start_color (by
      rw [geometry.distance_constant a path.start_color]; exact hpos)).trans
      (omegaCenter_le _)
  let σ := s.action.comp γ
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R geometry hedge a path.start_color
        (by rw [geometry.distance_constant a path.start_color]; exact hpos)
        z path.end_color path.critical }
  have hsmall : (Q R z).relIndex (Z R a) < (2^n)^2 := by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ))
      (by have := h.nonbinary; omega)
    nlinarith
  obtain ⟨haq,hzq⟩ := h.original_small_critical_indices_eq_field path hpos
    (by simpa only [h.field_card] using hsmall)
  rw [h.field_card] at haq hzq
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZA)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZA κ hκQ).trans (hzq.trans hFc.symm)
  have hδ : ∀ x : Z R z, ∀ v : s₀.space.toSubmodule,
      j (Multiplicative.ofAdd (s₀.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam R)⁻¹ :=
    fun x v => hconj (inclusion hZA x) v
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev hpos
    (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer z path.end_color)
    h.nonbinary hFc s₀ e he h.component_image_structure.2.2.2.2
    j hj hjr δ hδ hδcard (haq.trans hFc.symm)
  have hmap : ((Z R z).subgroupOf (stabilizer R a)).map κ = β.range.map γ := by
    have heq : γ.comp β = δ := by
      ext x
      exact hβmark x
    rw [←MonoidHom.range_comp,heq]
    apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
    · rintro y ⟨x,rfl⟩
      exact ⟨inclusion hZA x,x.property,rfl⟩
  have hSN : stabilizer R a ≤ normalizer
      ((Q R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) : Set (FreeAmalgam R)) := by
    have hSL : stabilizer R a ≤ normalizer (Ltilde R a : Set (FreeAmalgam R)) := by
      have ht := le_normalizer_map (H := pResidual 2 (stabilizer R a))
        (stabilizer R a).subtype
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
      exact ht
    exact (le_inf (Q_normalized R a)
      (hSL.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hfixed : fixedSpace σ ⊤ = ⊥ := by
    apply bot_unique
    intro v hv
    apply s.fixed_eq_bot.le
    rintro ⟨x,hx⟩
    rw [hs,hκL] at hx
    obtain ⟨b,hb⟩ := (e.groupEquiv.symm.surjective ⟨x,hx⟩)
    have he : γ b = x := congrArg Subtype.val hb
    change s.action x v = v
    rw [←he]
    exact hv ⟨b,mem_top _⟩
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  obtain ⟨f,hf⟩ := derived_four_conjugates_of_displacement_one
    hcard β.range hβcard hβdim hβquad
  have hdim := fixedCodim_le_card_mul_of_subgroup_conjugates σ ⊤ β.range f hf.ge
  have htotal := fixedCodim_add_finrank σ ⊤
  rw [hfixed,finrank_bot,add_zero] at htotal
  rw [htotal,Fintype.card_fin] at hdim
  have hindex := s.sectionData.fixed_index_of_relative_normalizers (Z R z)
    hZA (s.sectionData.section_le.trans hSN) (hZA.trans hSN)
  unfold fixedCodim at hindex
  rw [fixedSpace_comp_map,hs,hmap,←fixedSpace_comp_map] at hindex
  change (commutatorPreimage (Q R a) (Z R z)
    (fixedCore R a)).relIndex (Q R a) = 2^fixedCodim σ β.range at hindex
  have horder : (fixedCore R a).relIndex (Q R a) = Nat.card s.Carrier := by
    change ((fixedCore R a).subgroupOf (Q R a)).index = _
    have hk : s.sectionData.coordinates.ker =
        (fixedCore R a).subgroupOf (Q R a) := s.sectionData.kernel_eq
    rw [←hk,index_ker,MonoidHom.range_eq_top.mpr s.sectionData.onto,
      card_top]
    rfl
  rw [horder,hindex,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,←pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by simpa only [Nat.mul_comm] using hdim)

/-- Four critical-root conjugates make the full fixed-core index strictly
larger than the natural index. -/
theorem original_core_critical_fixed_index_gt_natural_index
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hpos : 0 < geometry.b R)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n) :
    (U R a ⊔ fixedCore R a).relIndex (Q R a) <
      (commutatorPreimage (Q R a) (Z R z)
        (fixedCore R a)).relIndex (Q R a) := by
  let q := 2^n
  let r := (U R a ⊔ fixedCore R a).relIndex (Q R a)
  let k := (commutatorPreimage (Q R a) (Z R z)
    (fixedCore R a)).relIndex (Q R a)
  have hq : 1 < q := one_lt_pow₀ (by decide : 1 < (2:ℕ))
    (by have := h.nonbinary; omega)
  have hr : r ≤ q := original_core_relIndex_natural_sup_fixed_le h d g hb path.start_color
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hrpos : 0 < r := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hh : q^4*r ≤ k^4 := by
    rw [←original_core_fixed_index_eq_natural_mul h d g hb path.start_color]
    exact original_core_fixed_index_le_critical_index_pow_four h d g hb path hpos hcritical
  by_contra! hkr
  have hle : q^4*r ≤ q^3*r := calc
    _ ≤ k^4 := hh
    _ ≤ r^4 := Nat.pow_le_pow_left hkr 4
    _ = r^3*r := pow_succ r 3
    _ ≤ q^3*r := Nat.mul_le_mul_right r (Nat.pow_le_pow_left hr 3)
  have he := Nat.le_of_mul_le_mul_right hle hrpos
  exact (not_le_of_gt ((pow_lt_pow_iff_right₀ hq).mpr (by decide : 3 < 4))) he

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
