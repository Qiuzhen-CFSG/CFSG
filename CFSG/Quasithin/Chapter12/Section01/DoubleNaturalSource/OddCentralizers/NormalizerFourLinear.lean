module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourStar
public import Theory.SpecificGroups.BinaryLinear.QuinticNormalizer
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Theory.GroupTheory.PRadicalSylowNormalizer

/-!
# The actual endpoint parabolic in the constrained degree-four branch

The C.2.7 star map identifies the selected component's central core quotient
with SL₅(2). Its literal radical image is a two-radical. The original perfect
residual acts nontrivially by inner automorphisms and has quotient L₄(2), so
its action retains the factor five. The binary five-space normalizer theorem
then gives an order-sixteen radical and a point or hyperplane parabolic.
Maximality and the proper star intersection identify that whole intersection
with this parabolic. Order divisibility makes the original residual cover
its Levi quotient, with the implementing conjugation formula retained.

The final theorem supplies this marked structure to the actual C.2.8 witness
and retains the whole doubled orbit. The natural/orthogonal module exclusion
and the ordinary outer-section branch are still separate proof obligations.
Source: Aschbacher--Smith C.2.7, C.4.5--8, 4.4.6 and 12.1.9,
printed pp.145--147,152--154,620,793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter12.Section01.DoubleNaturalSource
open Chapter4.Section04.NormalizedRankOneOddControl
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open BinaryLinear.OuterCyclic

theorem doubledFour_linear_five_center : center (LinearGroup 5) = ⊥ :=
  (Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv (slEquivLinear 5).symm
    (Theory.SpecificGroups.BinaryComponentResidual.linear (Or.inr rfl))).1

variable {G : Type*} [Group G] [Finite G] {H M F R W : Subgroup G}

/-- The literal core-central marking, compatible with the source star map. -/
@[expose] def doubledFour_constrained_five_coordinates
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) :
    coreCentralQuotient K ≃* LinearGroup 5 :=
  (coreCentralQuotientCongr (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
    (ChapterC.Section04Constrained.source_simple_equiv
      (h.constrained_source_input K hK hq hout hfK) (e.trans (slEquivLinear 5)) doubledFour_linear_five_center)

theorem doubledFour_constrained_five_coordinates_apply
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) (k : K) :
    doubledFour_constrained_five_coordinates h K hK hq hout hfK e (coreCentralProjection K k) =
      slEquivLinear 5 (e (toStarImage (K.map H.subtype) R
        (K.equivMapOfInjective H.subtype H.subtype_injective k))) := by
  rw [doubledFour_constrained_five_coordinates,MulEquiv.trans_apply,
    coreCentralQuotientCongr_apply,ChapterC.Section04Constrained.source_simple_equiv_mk]
  rfl

/-- The source radical image agrees with the image of the actual intersection. -/
theorem doubledFour_constrained_five_intersection
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) :
    (coreCentralIntersectionImage K (R.subgroupOf H)).map
      (doubledFour_constrained_five_coordinates h K hK hq hout hfK e).toMonoidHom =
      ((starImage (K.map H.subtype) R R).subgroupOf
        (starImage (K.map H.subtype) R (K.map H.subtype))).map
        (e.trans (slEquivLinear 5)).toMonoidHom := by
  let Kg := K.map H.subtype
  let s := h.constrained_source_input K hK hq hout hfK
  let : (Kg.subgroupOf (Kg ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Kg.le_normalizer s.normalizes)
  have hR := ChapterC.C27Source.component_intersection_star_eq_of_normal_input
    (ChapterC.C27Source.source_join_input s)
  rw [←hR]
  ext x
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
    refine ⟨toStarImage Kg R (K.equivMapOfInjective H.subtype H.subtype_injective k),?_,?_⟩
    · exact mem_map_of_mem _ hk
    · exact (doubledFour_constrained_five_coordinates_apply h K hK hq hout hfK e k).symm
  · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
    let a := K.equivMapOfInjective H.subtype H.subtype_injective
    refine ⟨coreCentralProjection K (a.symm k),⟨a.symm k,?_,rfl⟩,?_⟩
    · have he := congrArg (fun z : Kg => (z : G)) (a.apply_symm_apply k)
      change ((a.symm k : K) : H).val ∈ R
      change ((a.symm k : K) : H).val = (k : G) at he
      rwa [he]
    · change doubledFour_constrained_five_coordinates h K hK hq hout hfK e
        (coreCentralProjection K (a.symm k)) = slEquivLinear 5 (e (toStarImage Kg R k))
      rw [doubledFour_constrained_five_coordinates_apply]
      change slEquivLinear 5 (e (toStarImage Kg R (a (a.symm k)))) = _
      rw [a.apply_symm_apply]

/-- The component remains normal in the actual ambient local group. -/
theorem doubledFour_constrained_five_normal
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) : K.Normal := by
  apply h.constrained_component_normal_of_star_central_threeRank K hK hq hout hfK
  rw [primeRank_congr 3 (QuotientGroup.congr _ _ e (FixedElementary.map_center e))]
  exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two

/-- The literal original intersection image is a nontrivial two-radical. -/
theorem doubledFour_constrained_five_radical
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) :
    IsPRadical 2 ((coreCentralIntersectionImage K (R.subgroupOf H)).map
      (doubledFour_constrained_five_coordinates h K hK hq hout hfK e).toMonoidHom) := by
  rw [doubledFour_constrained_five_intersection]
  apply IsPRadical.map_equiv _ (e.trans (slEquivLinear 5))
  apply (ChapterC.C27Source.star_intersection_placement_from_source_of_large_order
    (h.constrained_source_input K hK hq hout hfK) ?_).1
  rw [Nat.card_congr e.toEquiv,
    Nat.card_congr Representation.SL5TenDimensional.projectiveEquiv.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
  norm_num only [Nat.card_zmod,Fin.prod_univ_succ,Fin.val_zero,Fin.val_succ,
    Fin.prod_univ_zero,mul_one] at hc
  rw [hc]
  decide

/-- Conjugation by the original normalized residual on the selected component's
literal core-central quotient. -/
@[expose] def doubledFour_normalized_actor
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) : F →* MulAut (coreCentralQuotient K) := by
  have hFH : F ≤ H := h.component_le.trans h.local_le
  have hFK : F.subgroupOf H ≤ normalizer (K : Set H) := by
    simpa only [h.normalized_span_eq hn] using h.constrained_span_normalizes_intrinsic K hK hq
  exact (normalizerCoreCentralAction K).comp
    ((inclusion hFK).comp (subgroupOfEquivOfLe hFH).symm.toMonoidHom)

theorem doubledFour_normalized_actor_range
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    (doubledFour_normalized_actor h hn K hK hq).range =
      coreCentralActorImage K (F.subgroupOf H) := by
  ext x
  constructor
  · rintro ⟨f,rfl⟩
    exact mem_map_of_mem _ f.property
  · rintro ⟨f,hf,rfl⟩
    exact ⟨⟨f.val.val,hf⟩,rfl⟩

/-- The inner lift retains its implementing-conjugation formula. -/
theorem doubledFour_normalized_inner_lift
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (eF : (F ⧸ pCore 2 F) ≃* alternatingGroup (Fin 8))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H) :
    ∃ r : F →* coreCentralQuotient K, Group.IsSolvable r.ker ∧
      r.range ≤ normalizer (coreCentralIntersectionImage K (R.subgroupOf H) : Set _) ∧
      ∀ f : F, MulAut.conj (r f) = doubledFour_normalized_actor h hn K hK hq f := by
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)))
  let : Group.IsPerfect F := (h.normalized_span_eq hn) ▸ h.span_perfect
  let a := doubledFour_normalized_actor h hn K hK hq
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp ht)).elim
  obtain ⟨f,hf,hconj⟩ := MulAut.perfect_subgroup_exists_inner_lift a.range hz
  let r := f.comp a.rangeRestrict
  have hr : r ≠ 1 := by
    intro he
    apply h.constrained_span_action_nontrivial K hK hq hout
    rw [h.normalized_span_eq hn,←doubledFour_normalized_actor_range h hn K hK hq]
    have ha : a = 1 := by
      apply DFunLike.ext
      intro x
      have hx : f (a.rangeRestrict x) = f 1 := (DFunLike.congr_fun he x).trans f.map_one.symm
      exact congrArg a.range.subtype (hf hx)
    change a.range = ⊥
    rw [ha,MonoidHom.range_one]
  let π := eF.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hπ : Function.Surjective π := eF.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = pCore 2 F :=
    (MonoidHom.ker_comp_of_injective _ _ eF.injective).trans (QuotientGroup.ker_mk' _)
  let : Group.IsNilpotent (pCore 2 F) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable π.ker := hπker.symm ▸ inferInstance
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨r,solvable_ker_of_nontrivial_hom_of_simple_quotient π hπ r hr,?_,fun x => hconj (a.rangeRestrict x)⟩
  have hFR : F.subgroupOf H ≤ normalizer (R.subgroupOf H : Set H) := by
    intro f hf y
    exact h.span_normalizes_radical ((h.normalized_span_eq hn).symm ▸ hf) (y : G)
  rintro _ ⟨x,rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [show r x = f (a.rangeRestrict x) from rfl,hconj]
  exact coreCentralActorImage_stabilizes K _ _ hFR
    ((doubledFour_normalized_actor_range h hn K hK hq).le ⟨x,rfl⟩)

private theorem endpoint_coordinates (N : Subgroup (LinearGroup 5))
    (hN : BinaryLinear.FiveParabolicStabilizer.IsEndParabolic N) :
    ∃ (b : BinaryLinear.FiveFlagGeometry.FiveBasis) (i : Fin 4),
      (i = 0 ∨ i = 3) ∧ N = BinaryLinear.FiveFlagGeometry.flagStabilizer b {i} := by
  open BinaryLinear.FiveFlagGeometry in
    rcases hN with ⟨v,hv,rfl⟩ | ⟨f,hf,rfl⟩
    · obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace
        (Submodule.span (ZMod 2) {v}) 0 (by simpa using finrank_span_singleton hv)
      exact ⟨b,0,Or.inl rfl,by rw [flagStabilizer_singleton,hb]⟩
    · have hd : Module.finrank (ZMod 2) f.ker = 4 := by
        have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
        norm_num [Space] at hh
        omega
      obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace f.ker 3 (by simpa using hd)
      exact ⟨b,3,Or.inr rfl,by rw [flagStabilizer_singleton,hb]⟩

private theorem endpoint_quotient (N : Subgroup (LinearGroup 5))
    (hN : BinaryLinear.FiveParabolicStabilizer.IsEndParabolic N) :
    Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 8)) := by
  open BinaryLinear.FiveFlagGeometry in
    obtain ⟨b,i,hi,he⟩ := endpoint_coordinates N hN
    let t := MulEquiv.subgroupCongr he
    let q := QuotientGroup.congr _ _ t (pCore_map_iso 2 t)
    let a := Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm
    rcases hi with rfl | rfl
    · exact ⟨q.trans ((MaximalOvergroups.lineQuotientEquiv b).trans a)⟩
    · exact ⟨q.trans ((MaximalOvergroups.hyperplaneQuotientEquiv b).trans a)⟩

private theorem residual_surjective_levi {A Q : Type*} [Group A] [Group Q] [Finite Q]
    (eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 8))
    (eQ : Q ≃* alternatingGroup (Fin 8))
    (f : A →* Q) [Group.IsSolvable f.ker] : Function.Surjective f := by
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let q := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable f.rangeRestrict.ker := (MonoidHom.ker_rangeRestrict f).symm ▸ inferInstance
  have hd := SimpleSection.card_dvd_of_solvable_representation
    (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 8))) q hq f.rangeRestrict
  rw [←Nat.card_congr eQ.toEquiv] at hd
  exact MonoidHom.range_eq_top.mp (f.range.eq_top_of_card_eq
    (le_antisymm (card_le_card_group _) (Nat.le_of_dvd Nat.card_pos hd)))

/-- In the surviving SL₅(2) star, the literal radical has order sixteen,
its normalizer is an endpoint parabolic, and the original residual covers
its entire L₄(2) Levi quotient. -/
theorem doubledFour_constrained_five_parabolic
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (eF : (F ⧸ pCore 2 F) ≃* alternatingGroup (Fin 8))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) :
    let a := doubledFour_constrained_five_coordinates h K hK hq hout hfK e
    let P := (coreCentralIntersectionImage K (R.subgroupOf H)).map a.toMonoidHom
    let N := normalizer (P : Set (LinearGroup 5))
    K.Normal ∧ IsPRadical 2 P ∧ Nat.card P = 16 ∧
      (∃ (b : BinaryLinear.FiveFlagGeometry.FiveBasis) (i : Fin 4),
        (i = 0 ∨ i = 3) ∧ N = BinaryLinear.FiveFlagGeometry.flagStabilizer b {i}) ∧
      ∃ r : F →* N, Group.IsSolvable r.ker ∧
        (∀ x : F, MulAut.conj (r x : LinearGroup 5) =
          MulAut.congr a (doubledFour_normalized_actor h hn K hK hq x)) ∧
        Function.Surjective ((QuotientGroup.mk' (pCore 2 N)).comp r) := by
  dsimp only
  let a := doubledFour_constrained_five_coordinates h K hK hq hout hfK e
  let P := (coreCentralIntersectionImage K (R.subgroupOf H)).map a.toMonoidHom
  let N := normalizer (P : Set (LinearGroup 5))
  have hP : IsPRadical 2 P := doubledFour_constrained_five_radical h K hK hq hout hfK e
  obtain ⟨r,hker,hr,hconj⟩ := doubledFour_normalized_inner_lift h hn eF K hK hq hout
  let := hker
  let f := a.toMonoidHom.comp r
  have hfker : f.ker = r.ker := MonoidHom.ker_comp_of_injective _ _ a.injective
  let : Group.IsSolvable f.ker := hfker.symm ▸ hker
  have hfN : f.range ≤ N := by
    rw [MonoidHom.range_comp]
    exact (map_mono hr).trans ((coreCentralIntersectionImage K (R.subgroupOf H)).le_normalizer_map _)
  let rN : F →* N := f.codRestrict N (fun x => hfN ⟨x,rfl⟩)
  have hkN : rN.ker = f.ker := MonoidHom.ker_codRestrict _ _ _
  let : Group.IsSolvable rN.ker := hkN.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hd := SimpleSection.card_dvd_of_solvable_representation
    (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 8)))
    (eF.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F)))
    (eF.surjective.comp (QuotientGroup.mk'_surjective _)) rN
  have h5 : 5 ∣ Nat.card N := (show 5 ∣ Nat.card (alternatingGroup (Fin 8)) by
    rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]).trans hd
  have hN := BinaryLinear.QuinticNormalizer.normalizer_isEndParabolic P hP.isPGroup hP.1 h5
  refine ⟨doubledFour_constrained_five_normal h K hK hq hout hfK e,hP,
    BinaryLinear.QuinticNormalizer.card_sixteen P hP.isPGroup hP.1 h5,
    endpoint_coordinates N hN,rN,inferInstance,?_,?_⟩
  · intro x
    change MulAut.conj (a (r x)) = MulAut.congr a (doubledFour_normalized_actor h hn K hK hq x)
    rw [←hconj]
    ext y
    simp [MulAut.congr_apply,MulAut.conj_apply]
  obtain ⟨eN⟩ := endpoint_quotient N hN
  let : Group.IsNilpotent (pCore 2 N) := pCore_isPGroup.isNilpotent
  let g := (QuotientGroup.mk' (pCore 2 N)).comp rN
  have hgker : g.ker = (pCore 2 N).comap rN := by
    ext x
    exact QuotientGroup.eq_one_iff (rN x)
  let : Group.IsSolvable g.ker := hgker.symm ▸ isSolvable_comap_of_solvable_ker rN (pCore 2 N)
  exact residual_surjective_levi eF eN g

/-- The actual intersection M∩K in the star quotient is this whole endpoint
parabolic, not just an abstract group with the same Levi quotient. -/
theorem doubledFour_constrained_five_starM
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (eF : (F ⧸ pCore 2 F) ≃* alternatingGroup (Fin 8))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) :
    let a := doubledFour_constrained_five_coordinates h K hK hq hout hfK e
    let P := (coreCentralIntersectionImage K (R.subgroupOf H)).map a.toMonoidHom
    ((starM (K.map H.subtype) R M).subgroupOf
      (starImage (K.map H.subtype) R (K.map H.subtype))).map
      (e.trans (slEquivLinear 5)).toMonoidHom = normalizer (P : Set (LinearGroup 5)) := by
  dsimp only
  let Kg := K.map H.subtype
  let a := doubledFour_constrained_five_coordinates h K hK hq hout hfK e
  let P := (coreCentralIntersectionImage K (R.subgroupOf H)).map a.toMonoidHom
  let I := (starImage Kg R R).subgroupOf (starImage Kg R Kg)
  let Z := (starM Kg R M).subgroupOf (starImage Kg R Kg)
  let b := e.trans (slEquivLinear 5)
  let s := h.constrained_source_input K hK hq hout hfK
  obtain ⟨_,_,_,⟨c,i,hi,hN⟩,_⟩ := doubledFour_constrained_five_parabolic h hn eF K hK hq hout hfK e
  have hlarge : 40320 < Nat.card (starImage Kg R Kg) := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr Representation.SL5TenDimensional.projectiveEquiv.toEquiv]
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    norm_num only [Nat.card_zmod,Fin.prod_univ_succ,Fin.val_zero,Fin.val_succ,
      Fin.prod_univ_zero,mul_one] at hc
    rw [hc]
    decide
  have hNZ : normalizer (P : Set (LinearGroup 5)) ≤ Z.map b.toMonoidHom := by
    have hh := ChapterC.C27Source.star_intersection_placement_from_source_of_large_order s hlarge
    rw [show P = I.map b.toMonoidHom from doubledFour_constrained_five_intersection h K hK hq hout hfK e,
      ←map_equiv_normalizer_eq I b]
    exact map_mono hh.2
  have hZ : Z.map b.toMonoidHom ≠ ⊤ := by
    intro ht
    have hZtop : Z = ⊤ := map_injective b.injective
      (ht.trans (map_top_of_surjective _ b.surjective).symm)
    exact (ChapterC.C27Source.star_thompson_intersection_from_source s).2.not_ge
      (subgroupOf_eq_top.mp hZtop)
  have hco : IsCoatom (normalizer (P : Set (LinearGroup 5))) :=
    hN ▸ BinaryLinear.FiveFlagGeometry.MaximalOvergroups.singleton_flag_isCoatom c i
  exact (hco.le_iff_eq hZ).mp hNZ

open Chapter4.Section02.RankOneReciprocalEscape

/-- A marked endpoint parabolic obtained from the actual pushing-up witness.
The residual action is specified by conjugation on the original core-central
quotient, and covers the complete Levi quotient. -/
@[expose] def FourPushingUpParabolic (L V A J H U : Subgroup G)
    (hw : Witness L V A J H U) : Prop :=
  ∃ (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
      (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
      (hfK : generalizedFitting K = pCore 2 K)
      (e : starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2)),
    let hc := hw.2.2.2.2.2.2.1
    let hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hw.2.2.2.2.2.2.2.2.1
    let a := doubledFour_constrained_five_coordinates hc K hK hq hout hfK e
    let P := (coreCentralIntersectionImage K ((J.pCoreIn 2).subgroupOf H)).map a.toMonoidHom
    let N := normalizer (P : Set (LinearGroup 5))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    K.Normal ∧ IsPRadical 2 P ∧ Nat.card P = 16 ∧
      (∃ (b : BinaryLinear.FiveFlagGeometry.FiveBasis) (i : Fin 4),
        (i = 0 ∨ i = 3) ∧ N = BinaryLinear.FiveFlagGeometry.flagStabilizer b {i}) ∧
      ((starM (K.map H.subtype) (J.pCoreIn 2) (H ⊓ normalizer (L : Set G))).subgroupOf
        (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype))).map
        (e.trans (slEquivLinear 5)).toMonoidHom = N ∧
      ∃ r : F →* N, Group.IsSolvable r.ker ∧
        (∀ x : F, MulAut.conj (r x : LinearGroup 5) =
          MulAut.congr a (doubledFour_normalized_actor hc hn K hK hq x)) ∧
        Function.Surjective ((QuotientGroup.mk' (pCore 2 N)).comp r)

/-- The literal SL₅(2) branch of the original witness has the stated marked
parabolic structure. No extra action or surjectivity premise is required. -/
theorem doubledFour_witness_parabolic
    {T : Sylow 2 G} {L V A J H U : Subgroup G}
    (B : DoubledBranch T L V 4) (hw : Witness L V A J H U)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2)) :
    FourPushingUpParabolic L V A J H U hw := by
  have hc := hw.2.2.2.2.2.2.1
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hw.2.2.2.2.2.2.2.2.1
  obtain ⟨eF,_⟩ := hw.2.2.2.2.2.2.2.2.2.2.2.1
  let aF := eF.trans (B.component.trans doubledFour_linearEquiv)
  obtain ⟨hKN,hP,hcard,hpar,hr⟩ := doubledFour_constrained_five_parabolic hc hn aF K hK hq hout hfK e
  exact ⟨K,hK,hq,hout,hfK,e,hKN,hP,hcard,hpar,
    doubledFour_constrained_five_starM hc hn aF K hK hq hout hfK e,hr⟩

variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
include D h in
/-- The original doubled branch produces the marked endpoint parabolic,
retaining the whole orbit, the original residual and the actual C.2.8 witness. -/
theorem doubledFour_pushingUp_parabolic_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ (J H U : Subgroup G) (hw : Witness L V A J H U),
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      FourPushingUpParabolic L V A J H U hw := by
  obtain ⟨J,H,U,hw,hWU,hWJ,K,hK,hq,hout,hfK,⟨e⟩⟩ :=
    D.doubledFour_pushingUp_linear_five_of_many h hmany B A hA ho hnot
  exact ⟨J,H,U,hw,hWU,hWJ,doubledFour_witness_parabolic B hw K hK hq hout hfK e⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
