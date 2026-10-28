module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.TranspositionImage
public import Stellmacher.BaumannIntermediate
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender

/-!
# Small Thompson and Baumann images on the original replacement

The small-image exclusion extends from the radical to its elementary Thompson
subgroup. First, if the Baumann image has order at most two, an actual MS3
maximum elementary offender identifies it with a transposition. Adjoining the
ambient two-core to the Baumann subgroup preserves that same Baumann subgroup.
The natural and augmentation forms of C.1.24(c) give shortness of the original
component: their characteristic-normal alternative contradicts MS3 on the
original radical. The whole-core radius argument then gives distance two.

The full moved cover has the same fixed vectors for the elementary Thompson
and Baumann subgroups. A small Thompson image is therefore enough: the cover
offender inequality bounds its fixed codimension by one, and the actual natural
quotient identifies the Baumann image with a transposition as well. Consequently
every remaining large-distance replacement has elementary Thompson image of
order at least four. Neither its original radical nor its Baumann subgroup is
assumed Sylow. Both moved-cover orders and all central attachments are retained.

These results settle the small Thompson-image branch, including replacements
whose radical image is larger. They do not settle the remaining large-image
branches or the endpoint and opposite-core estimates of MS93 (5.12).

Source: Aschbacher--Smith B.2.3--4, C.1.24(c), and the small-image argument in
C.1.37, printed pp.76--77,130--131,142; MS93 Section 5, pp.912--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (f : A ≃* B) (C : Subgroup A) [C.Characteristic] :
    (C.map f.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y,hy,rfl⟩ := hx
  let b : MulAut A := f.trans (a.trans f.symm)
  refine ⟨b y,(characteristic_iff_le_comap.mp inferInstance b) hy,?_⟩
  exact f.apply_symm_apply _

include h in
omit [Finite G] in
private theorem no_normal_characteristic_baumann
    (hC : ∃ C : Subgroup (ChapterB.baumann d.radical), C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map (ChapterB.baumann d.radical).subtype).Normal) : False := by
  obtain ⟨C,hC,hne,hn⟩ := hC
  let := hC
  let B := ChapterB.baumann d.radical
  have hBR : B ≤ d.radical := inf_le_left
  have hB : B.subgroupOf d.radical = ChapterB.baumann (⊤ : Subgroup d.radical) := by
    apply map_injective d.radical.subtype_injective
    rw [map_subgroupOf_eq_of_le hBR]
    change ChapterB.baumann d.radical =
      (ChapterB.baumann (⊤ : Subgroup d.radical)).map d.radical.subtype
    rw [ChapterC.RankOne.SymmetricSix.baumann_map d.radical d.radical.subtype
      d.radical.subtype_injective,←MonoidHom.range_eq_map,range_subtype]
  let : (B.subgroupOf d.radical).Characteristic := hB ▸ ChapterB.baumann_characteristic
  let fB : B ≃* B.subgroupOf d.radical := (subgroupOfEquivOfLe hBR).symm
  let C' := C.map fB.toMonoidHom
  let : C'.Characteristic := characteristic_map_equiv fB C
  let D := C'.map (B.subgroupOf d.radical).subtype
  let : D.Characteristic := inferInstance
  have hmap : D.map d.radical.subtype = C.map B.subtype := by
    rw [map_map,map_map]
    rfl
  have hDn : (D.map d.radical.subtype).Normal := hmap.symm ▸ hn
  have hD0 := (replacement_characteristic h d).eq_bot_of_normal D hDn
  have hC0 : C.map B.subtype = ⊥ := by rw [←hmap,hD0,Subgroup.map_bot]
  exact (hne ((C.map_eq_bot_iff_of_injective B.subtype_injective).mp hC0)).elim

private theorem cover_model_conjugation
    (s : FullSymmetricAction h e hz hn d)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) W)
    (E : Additive (replacementMoved d) ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (coverAction s g v) = ρ g (E v)) :
    letI := replacementMoved_normal h d
    ∀ (g : d.overgroup) (v : replacementMoved d),
      (E.toAddEquiv.toMultiplicativeRight (MulAut.conjNormal g v)).toAdd =
        ρ (s.projection g) (E.toAddEquiv.toMultiplicativeRight v).toAdd := by
  let := replacementMoved_normal h d
  intro g v
  have hconj : coverAction s (s.projection g) (Additive.ofMul v) =
      Additive.ofMul (MulAut.conjNormal g v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact coverAction_conjugate s g (Additive.ofMul v)
  change E (Additive.ofMul (MulAut.conjNormal g v)) = _
  rw [←hconj]
  exact hE (s.projection g) (Additive.ofMul v)

/-- A small image of the original Baumann subgroup is generated by a
transposition, detected by an actual MS3 maximum elementary offender. -/
theorem baumann_image_swap_of_card_le_two
    (hsmall : Nat.card ((ChapterB.baumann d.radical).map
      (SourceReduction.projection h e hz hn d)) ≤ 2) :
    ∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧
      (ChapterB.baumann d.radical).map (SourceReduction.projection h e hz hn d) = zpowers t := by
  obtain ⟨E,hE,hne,hoff⟩ := SourceReduction.Cover.exists_maxElementary_offender h e hz hn d
  let A := E.map (SourceReduction.projection h e hz hn d)
  let D := (ChapterB.baumann d.radical).map (SourceReduction.projection h e hz hn d)
  change Nat.card D ≤ 2 at hsmall
  have hAD : A ≤ D := map_mono ((le_sSup hE).trans
    (ChapterB.elementaryAbelianMaxJ_le_baumann d.radical))
  have hnA : A ≠ ⊥ := by
    intro hzA
    apply hne
    have hh := (map_eq_bot_iff E).mp hzA
    rwa [SourceReduction.projection_kernel h e hz hn d] at hh
  have hlo := (one_lt_card_iff_ne_bot A).mpr hnA
  have hup : Nat.card A ≤ Nat.card D := card_le_of_le hAD
  have htwo : Nat.card A = 2 := by omega
  have he : A = D := eq_of_le_of_card_ge hAD (by omega)
  have hr : rank A = 1 := by
    change Nat.log 2 (Nat.card A) = 1
    rw [htwo]
    decide
  have hfix : fixedCodim (BinaryPermutation.naturalRepresentation (Fin 6)) A ≤ 1 :=
    hoff.2.trans_eq hr
  obtain ⟨t,_,ht,htA⟩ :=
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
      A hnA hfix
  exact ⟨t,ht,he.symm.trans htA⟩

/-- Adjoining the ambient two-core to the original Baumann subgroup retains
that same Baumann subgroup. The two actual cover models then give shortness. -/
theorem short_component_of_baumann_transposition
    (s : FullSymmetricAction h e hz hn d)
    (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap)
    (himage : (ChapterB.baumann d.radical).map s.projection = zpowers t) :
    IsShort (replacementComponent d) := by
  let := replacementComponent_normal h d
  let := replacementMoved_normal h d
  let := h.relative_core_quasisimple e
  let f := subgroupOfEquivOfLe
    (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)
  let : IsQuasisimple ((replacementComponent d) ⧸ pCore 2 (replacementComponent d)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm
  have hcomp : (replacementComponent d).IsCComponent :=
    h.component.subgroupOf (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)
  have hself := replacement_self_centralizing h d
  have hf := generalizedFitting_eq_pCore_of_selfCentralizing 2 hself
  have hfL := generalizedFitting_eq_pCore_of_selfCentralizing 2
    (subnormal_core_selfCentralizing hself (replacementComponent d) hcomp.subnormal)
  obtain ⟨T,hRT⟩ := (replacement_radical_isPGroup h d).exists_le_sylow
  have hprod : ∀ m : d.overgroup, ∃ l ∈ replacementComponent d,
      ∃ t ∈ (T : Subgroup d.overgroup), l*t=m := by
    intro m
    obtain ⟨l,hl,t,ht,he⟩ := replacement_product h d m
    exact ⟨l,hl,t,hRT ht,he⟩
  have hm : ⁅replacementMoved d,replacementComponent d⁆ ≠ ⊥ := by
    rw [replacementMoved_idempotent h d]
    intro hzV
    have hc := moved_card s
    rw [hzV,card_bot] at hc
    omega
  let R0 := ChapterB.baumann d.radical ⊔ pCore 2 d.overgroup
  have hR0 : R0 ≤ d.radical := sup_le inf_le_left (replacement_core_le_radical h d)
  have hb : ChapterB.baumann R0 = ChapterB.baumann d.radical :=
    Stellmacher.baumann_eq_of_intermediate d.radical R0 le_sup_left hR0
  have him : R0.map s.projection = zpowers t := by
    rw [Subgroup.map_sup,himage,(Subgroup.map_eq_bot_iff _).mpr s.projection_kernel.symm.le,sup_bot_eq]
  rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
  · have hh := ChapterC.RankOne.SymmetricSix.normal_characteristic_or_alternatingBlock_of_natural_six
      (replacementComponent d) (replacementMoved d) R0 hcomp hf hfL T le_sup_right
      (hR0.trans hRT) hprod s.projection s.component_image E.toAddEquiv.toMultiplicativeRight
      (cover_model_conjugation s _ E hE) hm t ht him
    rw [hb] at hh
    exact hh.elim (fun hc => (no_normal_characteristic_baumann (h := h) hc).elim) (fun hb => hb.2.1)
  · have hh := ChapterC.RankOne.SymmetricSix.normal_characteristic_or_block_of_core_six
      (replacementComponent d) (replacementMoved d) R0 hcomp hf hfL T le_sup_right
      (hR0.trans hRT) hprod s.projection s.component_image E.toAddEquiv.toMultiplicativeRight
      (cover_model_conjugation s _ E hE) hm t ht him
    rw [hb] at hh
    exact hh.elim (fun hc => (no_normal_characteristic_baumann (h := h) hc).elim) (fun hb => hb.short)

/-- The actual replacement has distance two whenever its Baumann image has
order at most two, even if the original radical image is larger. -/
theorem distance_eq_two_of_small_baumann_image_knownSimple
    (hsmall : Nat.card ((ChapterB.baumann d.radical).map
      (SourceReduction.projection h e hz hn d)) ≤ 2) :
    replacementDistance h d = 2 := by
  by_cases hb : 2 < replacementDistance h d
  · let s := fullSymmetricAction_knownSimple h e hz hn d hb
    obtain ⟨t,ht,he⟩ := baumann_image_swap_of_card_le_two hsmall
    have him : (ChapterB.baumann d.radical).map s.projection = zpowers t := by
      rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact distance_eq_two_of_short_component (e := e) (hz := hz) (hn := hn)
      (short_component_of_baumann_transposition s t ht him)
  · exact replacementDistance_eq_two h d (Nat.le_of_not_gt hb)

/-- The full moved cover has the same fixed vectors for the elementary
Thompson image and the Baumann image. This uses the original maximum
subgroups of the radical and retains the possible central attachment. -/
theorem cover_thompson_fixed_le_baumann_fixed
    (s : FullSymmetricAction h e hz hn d) :
    fixedSpace (coverAction s) ((Stellmacher.elementaryAbelianMaxJ d.radical).map s.projection) ≤
      fixedSpace (coverAction s) ((ChapterB.baumann d.radical).map s.projection) := by
  let := replacementMoved_normal h d
  let W := replacementMoved d ⊓ centralizer
    (Stellmacher.elementaryAbelianMaxJ d.radical : Set d.overgroup)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le
    (show W ≤ replacementMoved d from inf_le_left)
  have hWR : W ≤ d.radical := inf_le_left.trans (fun x hx =>
    replacement_core_le_radical h d
      ((mem_omegaCenterIn_iff _ _).mp (replacementMoved_le_omegaCenter h d hx)).1)
  have hW := Stellmacher.elementary_centralizer_maxJ_le_omegaCenter d.radical W hWR inf_le_right
  intro v hv
  have hvJ : (v.toMul : d.overgroup) ∈ centralizer
      (Stellmacher.elementaryAbelianMaxJ d.radical : Set d.overgroup) :=
    (NormalElementaryQuotient.mem_fixedSpace_image _ _ _ _ _ v).mp hv
  have hvB : (v.toMul : d.overgroup) ∈ centralizer
      (ChapterB.baumann d.radical : Set d.overgroup) :=
    le_centralizer_iff.mp (show ChapterB.baumann d.radical ≤ centralizer
      (Stellmacher.omegaOneCenterAmbient (Stellmacher.elementaryAbelianMaxJ d.radical) :
        Set d.overgroup) from inf_le_right) (hW ⟨v.toMul.property,hvJ⟩)
  exact (NormalElementaryQuotient.mem_fixedSpace_image _ _ _ _ _ v).mpr hvB

/-- The cover offender inequality and its actual fixed subgroup force a
small Baumann image whenever the elementary Thompson image is small.
No point-core placement or cover splitting is needed. -/
theorem baumann_image_card_le_two_of_thompson_image
    (s : FullSymmetricAction h e hz hn d)
    (hsmall : Nat.card ((Stellmacher.elementaryAbelianMaxJ d.radical).map s.projection) ≤ 2) :
    Nat.card ((ChapterB.baumann d.radical).map s.projection) ≤ 2 := by
  let := replacementMoved_normal h d
  obtain ⟨E,hE,hne,_⟩ := SourceReduction.Cover.exists_maxElementary_offender h e hz hn d
  let A := E.map s.projection
  let J := (Stellmacher.elementaryAbelianMaxJ d.radical).map s.projection
  let B := (ChapterB.baumann d.radical).map s.projection
  have hAJ : A ≤ J := map_mono (le_sSup hE)
  have hnA : A ≠ ⊥ := by
    intro hzA
    apply hne
    have hh := (map_eq_bot_iff E).mp hzA
    rwa [s.projection_kernel] at hh
  have hlo := (one_lt_card_iff_ne_bot A).mpr hnA
  have hup : Nat.card A ≤ Nat.card J := card_le_of_le hAJ
  have htwo : Nat.card A = 2 := by change Nat.card J ≤ 2 at hsmall; omega
  have he : A = J := eq_of_le_of_card_ge hAJ (by change Nat.card J ≤ 2 at hsmall; omega)
  have hr : rank A = 1 := by
    change Nat.log 2 (Nat.card A) = 1
    rw [htwo]
    decide
  have hVR : replacementMoved d ≤ d.radical := fun x hx =>
    replacement_core_le_radical h d
      ((mem_omegaCenterIn_iff _ _).mp (replacementMoved_le_omegaCenter h d hx)).1
  have hoff : IsOffender (coverAction s) A :=
    NormalElementaryQuotient.maxElementary_isOffender (replacementMoved d) s.projection
      s.surjective (s.projection_kernel.trans (moved_centralizer s).symm)
      d.radical E hVR hE (by rwa [s.projection_kernel])
  have hco : fixedCodim (coverAction s) J ≤ 1 := by
    rw [←he]
    exact hoff.2.trans_eq hr
  have hdim := Submodule.finrank_mono (cover_thompson_fixed_le_baumann_fixed s)
  have hJdim := fixedCodim_add_finrank (coverAction s) J
  have hBdim := fixedCodim_add_finrank (coverAction s) B
  have hBco : fixedCodim (coverAction s) B ≤ 1 := by
    change Module.finrank (ZMod 2) (fixedSpace (coverAction s) J) ≤
      Module.finrank (ZMod 2) (fixedSpace (coverAction s) B) at hdim
    omega
  have hnat : fixedCodim (BinaryPermutation.naturalRepresentation (Fin 6)) B ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s)
      (BinaryPermutation.naturalRepresentation (Fin 6))
      (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      coverMap_surjective (coverMap_equivariant s) B).trans hBco
  have hnB : B ≠ ⊥ := by
    intro hzB
    apply hnA
    apply bot_unique
    exact (hAJ.trans (map_mono (ChapterB.elementaryAbelianMaxJ_le_baumann d.radical))).trans_eq hzB
  obtain ⟨t,_,ht,htB⟩ :=
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
      B hnB hnat
  change Nat.card B ≤ 2
  rw [htB,Nat.card_zpowers,ht.orderOf]

/-- Distance two for the literal replacement with a small elementary
Thompson image, allowing arbitrary larger radical and Baumann images a priori. -/
theorem distance_eq_two_of_small_thompson_image_knownSimple
    (hsmall : Nat.card ((Stellmacher.elementaryAbelianMaxJ d.radical).map
      (SourceReduction.projection h e hz hn d)) ≤ 2) :
    replacementDistance h d = 2 := by
  by_cases hb : 2 < replacementDistance h d
  · let s := fullSymmetricAction_knownSimple h e hz hn d hb
    have hJ : Nat.card ((Stellmacher.elementaryAbelianMaxJ d.radical).map s.projection) ≤ 2 := by
      rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    have hB := baumann_image_card_le_two_of_thompson_image s hJ
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hB
    exact distance_eq_two_of_small_baumann_image_knownSimple hB
  · exact replacementDistance_eq_two h d (Nat.le_of_not_gt hb)

/-- Every remaining large-distance replacement has elementary Thompson
image of order at least four on the unchanged natural quotient. -/
theorem large_distance_thompson_image_four_le_knownSimple
    (hb : 2 < replacementDistance h d) :
    4 ≤ Nat.card ((Stellmacher.elementaryAbelianMaxJ d.radical).map
      (SourceReduction.projection h e hz hn d)) := by
  have hnsmall : ¬ Nat.card ((Stellmacher.elementaryAbelianMaxJ d.radical).map
      (SourceReduction.projection h e hz hn d)) ≤ 2 := by
    intro hsmall
    have he := distance_eq_two_of_small_thompson_image_knownSimple hsmall
    omega
  have hp := ((replacement_radical_isPGroup h d).to_le
    (show Stellmacher.elementaryAbelianMaxJ d.radical ≤ d.radical from
      sSup_le fun _ hE => hE.1)).map (SourceReduction.projection h e hz hn d)
  obtain ⟨n,he⟩ := hp.exists_card_eq
  rw [he] at hnsmall ⊢
  have hn : 2 ≤ n := by
    by_contra! hh
    interval_cases n <;> norm_num at hnsmall
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hn

/-- Every remaining large-distance replacement has Baumann image of order
at least four, with both central covers and the original radical retained. -/
theorem large_distance_baumann_image_four_le_knownSimple
    (hb : 2 < replacementDistance h d) :
    4 ≤ Nat.card ((ChapterB.baumann d.radical).map (SourceReduction.projection h e hz hn d)) := by
  have hnsmall : ¬ Nat.card ((ChapterB.baumann d.radical).map
      (SourceReduction.projection h e hz hn d)) ≤ 2 := by
    intro hsmall
    have he := distance_eq_two_of_small_baumann_image_knownSimple hsmall
    omega
  have hp := ((replacement_radical_isPGroup h d).to_le
    (show ChapterB.baumann d.radical ≤ d.radical from inf_le_left)).map
      (SourceReduction.projection h e hz hn d)
  obtain ⟨n,he⟩ := hp.exists_card_eq
  rw [he] at hnsmall ⊢
  have hn : 2 ≤ n := by
    by_contra! hh
    interval_cases n <;> norm_num at hnsmall
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hn

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
