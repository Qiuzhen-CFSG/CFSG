module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourLinear
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarNormalizerAction
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.Representation.BinaryNaturalDual.MovedEmbedding

/-!
# The original doubled module in the constrained SL₅(2) star

The whole parabolic image realizes every residual actor inside M ∩ K.
If the original perfect residual escaped K, its intersection with K would
be solvable, contradicting its nontrivial perfect action. Thus the original
residual lies in K, with its original quotient map onto GL₄(2).

The source module lies in Ω₁(Z(O₂(KR))). Its natural-plus-dual coordinates
embed equivariantly in the literal star representation, fixed by the original
radical. Full commutator generation and absence of fixed vectors place it
injectively in the actual B.5.1 moved central quotient. The classified module,
its central projection, and the original residual action are retained.

The remaining endpoint-module exclusion is not asserted here. The actual
odd-normalizer application is in DoubleNaturalExcludedFourOddNormalizers.
Source: Aschbacher--Smith C.4.5 and C.4.8, printed pp.152--154, and 12.1.9,
printed p.793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter12.Section01.DoubleNaturalSource
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H M F R U : Subgroup G}

/-- The original C.2.8 module lies in the ambient image of Ω₁(Z(O₂(KR))). -/
theorem constrained_module_le_starV
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R U)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) [K.Normal] :
    U ≤ (starV (K.map H.subtype) R).map (K.map H.subtype ⊔ R).subtype := by
  let Kg := K.map H.subtype
  let J := Kg ⊔ R
  have s := h.constrained_source_input K hK hq hout hfK
  have hRH : R ≤ H := h.radical_le.trans h.local_le
  have hRmap : (R.subgroupOf H).map H.subtype = R := map_subgroupOf_eq_of_le hRH
  have hjoin : (K ⊔ R.subgroupOf H).map H.subtype = J := by
    rw [Subgroup.map_sup,hRmap]
  have hQR : J.pCoreIn 2 ≤ R := by
    have hh := map_mono (f := H.subtype)
      (ChapterC.C27Source.joinCore_le_radical K (R.subgroupOf H) h.isRadical)
    rwa [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,hjoin,hRmap] at hh
  have hc : centralizer (pCore 2 Kg : Set Kg) ≤ pCore 2 Kg := by
    rw [←s.fitting]
    exact centralizer_generalizedFitting_le Kg
  have hJc := centralizer_pCore_sup_le 2 Kg R hc h.radical_isTwoGroup s.normalizes
  let := h.module_elementary
  intro u hu
  obtain ⟨z,hz,he⟩ := h.module_le_center_radical hu
  have huR : u ∈ R := he ▸ z.property
  have huc : u ∈ centralizer (R : Set G) := by
    rw [←he]
    intro r hr
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨r,hr⟩)
  let x : J := ⟨u,mem_sup_right huR⟩
  have hxC : x ∈ centralizer (pCore 2 J : Set J) := by
    intro q hq
    exact Subtype.ext (huc q (hQR (mem_map_of_mem J.subtype hq)))
  refine ⟨x,?_,rfl⟩
  change x ∈ Subgroup.omegaCenterIn (pCore 2 J)
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨hJc hxC,hxC,Subtype.ext (elemPow_eq_one_of_isElementaryAbelian u hu)⟩

omit [Finite G] in
private theorem coreCentralAction_inner (K : Subgroup H) (k : K) :
    normalizerCoreCentralAction K ⟨k,K.le_normalizer k.property⟩ =
      MulAut.conj (coreCentralProjection K k) := by
  ext x
  obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)) x
  obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) q
  change normalizerCoreCentralAction K ⟨k,K.le_normalizer k.property⟩ (coreCentralProjection K j) =
    MulAut.conj (coreCentralProjection K k) (coreCentralProjection K j)
  rw [normalizerCoreCentralAction_apply,MulAut.conj_apply,←map_inv,←map_mul,←map_mul]
  rfl

/-- Every residual actor on the full core-central quotient is realized in M ∩ K. -/
theorem doubledFour_constrained_five_actor_le_intersection
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R U)
    (hn : M ≤ normalizer (F : Set G))
    (eF : (F ⧸ pCore 2 F) ≃* alternatingGroup (Fin 8))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    coreCentralActorImage K (F.subgroupOf H) ≤
      coreCentralActorImage K (M.subgroupOf H ⊓ K) := by
  let Kg := K.map H.subtype
  let a := doubledFour_constrained_five_coordinates h K hK hq hout hfK e
  let b := e.trans (BinaryLinear.OuterCyclic.slEquivLinear 5)
  let Z := (starM Kg R M).subgroupOf (starImage Kg R Kg)
  obtain ⟨_,_,_,_,r,_,hconj,_⟩ :=
    doubledFour_constrained_five_parabolic h hn eF K hK hq hout hfK e
  have hZ := doubledFour_constrained_five_starM h hn eF K hK hq hout hfK e
  rintro _ ⟨x,hx,rfl⟩
  let f : F := ⟨x.val.val,hx⟩
  have hm : (r f : BinaryLinear.OuterCyclic.LinearGroup 5) ∈ Z.map b.toMonoidHom :=
    hZ.symm ▸ (r f).property
  obtain ⟨z,hz,hze⟩ := hm
  obtain ⟨k,hk,hke⟩ := hz
  let kg : Kg := ⟨k.val,hk.2⟩
  let t := K.equivMapOfInjective H.subtype H.subtype_injective
  let k₀ : K := t.symm kg
  have heq : ((k₀ : H) : G) = (k : G) := congrArg Subtype.val (t.apply_symm_apply kg)
  have hcoord : a (coreCentralProjection K k₀) = (r f : BinaryLinear.OuterCyclic.LinearGroup 5) := by
    rw [doubledFour_constrained_five_coordinates_apply]
    change b (toStarImage Kg R (t (t.symm kg))) = _
    rw [t.apply_symm_apply]
    have hkz : toStarImage Kg R kg = z := by
      apply Subtype.ext
      exact hke
    exact (congrArg b hkz).trans hze
  have hact : normalizerCoreCentralAction K ⟨k₀,K.le_normalizer k₀.property⟩ =
      normalizerCoreCentralAction K x := by
    rw [coreCentralAction_inner]
    apply (MulAut.congr a).injective
    have he : MulAut.congr a (MulAut.conj (coreCentralProjection K k₀)) =
        MulAut.conj (a (coreCentralProjection K k₀)) := by
      ext y
      simp [MulAut.congr_apply,MulAut.conj_apply]
    rw [he,hcoord,hconj]
    rfl
  refine ⟨⟨k₀,K.le_normalizer k₀.property⟩,?_,hact⟩
  change ((k₀ : H) : G) ∈ M ∧ (k₀ : H) ∈ K
  exact ⟨by rw [heq]; exact hk.1,k₀.property⟩

/-- The original perfect residual lies in the same constrained component K. -/
theorem doubledFour_constrained_five_contains_residual
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R U)
    (hn : M ≤ normalizer (F : Set G))
    (eF : (F ⧸ pCore 2 F) ≃* alternatingGroup (Fin 8))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    F.subgroupOf H ≤ K := by
  let := doubledFour_constrained_five_normal h K hK hq hout hfK e
  let : Group.IsPerfect F := (h.normalized_span_eq hn) ▸ h.span_perfect
  have hFH : F ≤ H := h.component_le.trans h.local_le
  let A := F.subgroupOf H
  let I := M.subgroupOf H ⊓ K
  let C := ⁅A,I⁆
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hFH).symm.surjective
  have hMA : M.subgroupOf H ≤ normalizer (A : Set H) := by
    intro m hm f
    exact hn hm (f : G)
  have hCA : C ≤ A := le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hMA)
  have hCK : C ≤ K := (commutator_mono le_rfl inf_le_right).trans
    (le_normalizer_iff_commutator_le_right.mp (show A ≤ normalizer (K : Set H) by
      rw [normalizer_eq_top]; exact le_top))
  let B := coreCentralActorImage K A
  have hAN : A ≤ normalizer (K : Set H) := by rw [normalizer_eq_top]; exact le_top
  have hIN : I ≤ normalizer (K : Set H) := by rw [normalizer_eq_top]; exact le_top
  have hCN : C ≤ normalizer (K : Set H) := hCA.trans hAN
  let : Group.IsPerfect B := coreCentralActorImage_perfect K A hAN
  have hBne : B ≠ ⊥ := by
    simpa only [h.normalized_span_eq hn] using h.constrained_span_action_nontrivial K hK hq hout
  let : Nontrivial B := (nontrivial_iff_ne_bot _).mpr hBne
  have hBI : B ≤ coreCentralActorImage K I :=
    doubledFour_constrained_five_actor_le_intersection h hn eF K hK hq hout hfK e
  have hBC : B ≤ coreCentralActorImage K C := by
    change B ≤ (C.subgroupOf (normalizer (K : Set H))).map (normalizerCoreCentralAction K)
    rw [show C = ⁅A,I⁆ from rfl,
      Theory.GroupTheory.SubgroupTransport.subgroupOf_commutator A I hAN hIN,map_commutator]
    exact (show B = ⁅B,B⁆ from commutator_eq_self.symm).le.trans (commutator_mono le_rfl hBI)
  by_contra hnot
  let q : F →* H ⧸ K := (QuotientGroup.mk' K).comp (inclusion hFH)
  have hqne : q ≠ 1 := by
    intro he
    apply hnot
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mp (DFunLike.congr_fun he (⟨x.val,hx⟩ : F))
  let π := eF.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hπ : Function.Surjective π := eF.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = pCore 2 F :=
    (MonoidHom.ker_comp_of_injective _ _ eF.injective).trans (QuotientGroup.ker_mk' _)
  let : Group.IsNilpotent (pCore 2 F) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable π.ker := hπker.symm ▸ inferInstance
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsSolvable q.ker := solvable_ker_of_nontrivial_hom_of_simple_quotient π hπ q hqne
  let j : C →* q.ker := {
    toFun x := ⟨⟨x.val.val,hCA x.property⟩,(QuotientGroup.eq_one_iff x.val).mpr (hCK x.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : q.ker => ((z : F) : G)) he))
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective hj
  let : Group.IsSolvable (C.subgroupOf (normalizer (K : Set H))) :=
    Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hCN).symm.toMonoidHom)
      (subgroupOfEquivOfLe hCN).symm.surjective
  let : Group.IsSolvable (coreCentralActorImage K C) :=
    Group.isSolvable_of_surjective ((normalizerCoreCentralAction K).subgroupMap_surjective _)
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (inclusion_injective hBC)
  exact Group.IsPerfect.not_isSolvable B inferInstance

variable {W K₀ : Subgroup G} [IsElementaryAbelian 2 W]

private def starInclusion
    (hW : W ≤ (starV K₀ R).map (K₀ ⊔ R).subtype) :
    Additive W →ₗ[ZMod 2] Additive (starV K₀ R) :=
  (((starV K₀ R).equivMapOfInjective (K₀ ⊔ R).subtype
    (K₀ ⊔ R).subtype_injective).symm.toMonoidHom.comp
      (inclusion hW)).toAdditive.toZModLinearMap 2

omit [Finite G] in
private theorem starInclusion_coe
    (hW : W ≤ (starV K₀ R).map (K₀ ⊔ R).subtype) (w : Additive W) :
    (((starInclusion hW w).toMul : (K₀ ⊔ R : Subgroup G)) : G) = w.toMul := by
  let e := (starV K₀ R).equivMapOfInjective (K₀ ⊔ R).subtype (K₀ ⊔ R).subtype_injective
  exact congrArg Subtype.val (e.apply_symm_apply (inclusion hW w.toMul))

omit [Finite G] in
private theorem starInclusion_injective
    (hW : W ≤ (starV K₀ R).map (K₀ ⊔ R).subtype) :
    Function.Injective (starInclusion hW) := by
  intro x y he
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (starInclusion_coe hW x).symm.trans
    ((congrArg (fun v : Additive (starV K₀ R) => ((v.toMul : (K₀ ⊔ R : Subgroup G)) : G)) he).trans
      (starInclusion_coe hW y))

omit [Finite G] in
private theorem starInclusion_fixed
    (hW : W ≤ (starV K₀ R).map (K₀ ⊔ R).subtype)
    (hWR : W ≤ centralizer (R : Set G)) :
    (starInclusion hW).range ≤ Representation.BinaryOffender.fixedSpace
      (starRepresentation K₀ R) (starImage K₀ R R) := by
  rintro _ ⟨w,rfl⟩ ⟨x,⟨r,hr,rfl⟩⟩
  change starRepresentation K₀ R (QuotientGroup.mk' (starKernel K₀ R) r) (starInclusion hW w) = _
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [starRepresentation_apply]
  change (r : G) * (((starInclusion hW w).toMul : (K₀ ⊔ R : Subgroup G)) : G) * (r : G)⁻¹ = _
  rw [starInclusion_coe]
  exact mul_inv_eq_of_eq_mul (hWR w.toMul.property r hr)

/-- The ambient inclusion of a source submodule is linear, injective and radical-fixed. -/
theorem constrained_module_star_fixed_embedding
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R U)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) [K.Normal]
    (hWU : W ≤ U) :
    ∃ f : Additive W →ₗ[ZMod 2] Additive (starV (K.map H.subtype) R),
      Function.Injective f ∧
      (∀ w, (((f w).toMul : (K.map H.subtype ⊔ R : Subgroup G)) : G) = w.toMul) ∧
      f.range ≤ Representation.BinaryOffender.fixedSpace
        (starRepresentation (K.map H.subtype) R) (starImage (K.map H.subtype) R R) := by
  have hW := hWU.trans (constrained_module_le_starV h K hK hq hout hfK)
  refine ⟨starInclusion hW,starInclusion_injective hW,starInclusion_coe hW,starInclusion_fixed hW ?_⟩
  intro w hw r hr
  obtain ⟨z,hz,he⟩ := h.module_le_center_radical (hWU hw)
  rw [←he]
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨r,hr⟩)

omit [Finite G] in
/-- An ambient-preserving embedding intertwines the literal normalizer actions. -/
theorem star_embedding_equivariant
    (f : Additive W →ₗ[ZMod 2] Additive (starV K₀ R))
    (hf : ∀ w, (((f w).toMul : (K₀ ⊔ R : Subgroup G)) : G) = w.toMul)
    (a : G) (hW : a ∈ normalizer (W : Set G))
    (hK : a ∈ normalizer (K₀ : Set G)) (hR : a ∈ normalizer (R : Set G))
    (w : Additive W) :
    f (Additive.ofMul (W.normalizerMonoidHom ⟨a,hW⟩ w.toMul)) =
      ChapterC.C27Source.starVectorAut K₀ R a hK hR (f w) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [hf,ChapterC.C27Source.starVectorAut_apply,hf]
  rfl

variable {T : Sylow 2 G} {L V A J : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)

include D h in
/-- The actual radical-fixed star space contains the original eight-dimensional orbit. -/
theorem doubledFour_witness_star_fixed_rank
    (B : DoubledBranch T L V 4) (hw : Witness L V A J H U)
    (hWU : componentOrbit V (T : Subgroup G) ≤ U)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    8 ≤ Module.finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace
      (starRepresentation (K.map H.subtype) (J.pCoreIn 2))
      (starImage (K.map H.subtype) (J.pCoreIn 2) (J.pCoreIn 2))) := by
  let := D.doubledOrbit_elementary h
  have hc := hw.2.2.2.2.2.2.1
  let := doubledFour_constrained_five_normal hc K hK hq hout hfK e
  obtain ⟨f,hf,_,hfixed⟩ := constrained_module_star_fixed_embedding hc K hK hq hout hfK hWU
  let g := f.codRestrict _ (fun w => hfixed ⟨w,rfl⟩)
  have hg : Function.Injective g := fun x y he => hf (congrArg Subtype.val he)
  have hd := LinearMap.finrank_le_finrank_of_injective hg
  rw [B.finrank_eq] at hd
  exact hd

include D h in
/-- The original residual projection and doubled coordinates intertwine the actual star action. -/
theorem doubledFour_witness_star_coordinates
    (B : DoubledBranch T L V 4) (hw : Witness L V A J H U)
    (hWU : componentOrbit V (T : Subgroup G) ≤ U)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let p : F →* BinaryLinear.OuterCyclic.LinearGroup 4 :=
      B.componentProjection.comp (inclusion ((map_subtype_le _).trans inf_le_left))
    ∃ hFK : F ≤ K.map H.subtype,
      Function.Surjective p ∧
      ∃ f : BinaryNaturalDual.CoordinateSpace 4 →ₗ[ZMod 2]
          Additive (starV (K.map H.subtype) (J.pCoreIn 2)),
        Function.Injective f ∧
        (∀ v, (((f v).toMul : (K.map H.subtype ⊔ J.pCoreIn 2 : Subgroup G)) : G) =
          (B.coordinates.symm (Multiplicative.ofAdd v) : G)) ∧
        f.range ≤ Representation.BinaryOffender.fixedSpace
          (starRepresentation (K.map H.subtype) (J.pCoreIn 2))
          (starImage (K.map H.subtype) (J.pCoreIn 2) (J.pCoreIn 2)) ∧
        ∀ (x : F) v,
          f (BinaryNaturalDual.naturalDualRepresentation (p x) v) =
            starRepresentation (K.map H.subtype) (J.pCoreIn 2)
              (toStarImage (K.map H.subtype) (J.pCoreIn 2) (inclusion hFK x)) (f v) := by
  dsimp only
  let := D.doubledOrbit_elementary h
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := hw.2.2.2.2.2.2.1
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hw.2.2.2.2.2.2.2.2.1
  obtain ⟨eF,heF⟩ := hw.2.2.2.2.2.2.2.2.2.2.2.1
  let := doubledFour_constrained_five_normal hc K hK hq hout hfK e
  have hFK : F ≤ K.map H.subtype := by
    have hh := map_mono (f := H.subtype) (doubledFour_constrained_five_contains_residual hc hn
      (eF.trans (B.component.trans doubledFour_linearEquiv)) K hK hq hout hfK e)
    rwa [map_subgroupOf_eq_of_le (hc.component_le.trans hc.local_le)] at hh
  let p : F →* BinaryLinear.OuterCyclic.LinearGroup 4 :=
      B.componentProjection.comp (inclusion ((map_subtype_le _).trans inf_le_left))
  have hp : p = (eF.trans B.component).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F)) := by
    ext x : 1
    change B.component (QuotientGroup.mk' (pCore 2 L) (inclusion _ x)) =
      B.component (eF (QuotientGroup.mk' (pCore 2 F) x))
    rw [heF]
  obtain ⟨j,hj,hjcoe,hjfixed⟩ := constrained_module_star_fixed_embedding hc K hK hq hout hfK hWU
  let f := j.comp B.linearCoordinates.symm.toLinearMap
  have hfcoe (v) : (((f v).toMul : (K.map H.subtype ⊔ J.pCoreIn 2 : Subgroup G)) : G) =
      (B.coordinates.symm (Multiplicative.ofAdd v) : G) := hjcoe _
  refine ⟨hFK,?_,f,hj.comp B.linearCoordinates.symm.injective,hfcoe,?_,?_⟩
  · change Function.Surjective p
    rw [hp]
    exact (eF.trans B.component).surjective.comp (QuotientGroup.mk'_surjective _)
  · rintro _ ⟨v,rfl⟩
    exact hjfixed ⟨B.linearCoordinates.symm v,rfl⟩
  · intro x v
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    rw [hfcoe]
    change (B.coordinates.symm (Multiplicative.ofAdd (BinaryNaturalDual.naturalDualRepresentation (p x) v)) : G) =
      (((starRepresentation (K.map H.subtype) (J.pCoreIn 2)
        (QuotientGroup.mk' (starKernel (K.map H.subtype) (J.pCoreIn 2))
          ⟨x,mem_sup_left (hFK x.property)⟩) (f v)).toMul :
            (K.map H.subtype ⊔ J.pCoreIn 2 : Subgroup G)) : G)
    rw [starRepresentation_apply]
    change _ = (x : G) * (((f v).toMul : (K.map H.subtype ⊔ J.pCoreIn 2 : Subgroup G)) : G) * (x : G)⁻¹
    rw [hfcoe]
    simpa only [p,DoubledBranch.componentProjection,MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom,Subgroup.coe_inclusion,B.coordinates.apply_symm_apply,toAdd_ofAdd] using
      B.component_action (inclusion ((map_subtype_le _).trans inf_le_left) x)
        (B.coordinates.symm (Multiplicative.ofAdd v))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule


open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter1.RadicalExclusions.ModelReduction
open ChapterB.QuasisimpleSource Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A J H U : Subgroup G}

/-- The original doubled module inside the actual star representation. -/
structure FourStarModuleCoordinates (B : DoubledBranch T L V 4)
    (J H : Subgroup G) (K : Subgroup H) where
  residual_le : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype ≤ K.map H.subtype
  residual_surjective : Function.Surjective
    (B.componentProjection.comp (inclusion ((map_subtype_le (solvableResidual (L ⊓ H : Subgroup G))).trans inf_le_left)))
  embedding : BinaryNaturalDual.CoordinateSpace 4 →ₗ[ZMod 2]
    Additive (starV (K.map H.subtype) (J.pCoreIn 2))
  injective : Function.Injective embedding
  ambient : ∀ v, (((embedding v).toMul : (K.map H.subtype ⊔ J.pCoreIn 2 : Subgroup G)) : G) =
    (B.coordinates.symm (Multiplicative.ofAdd v) : G)
  radical_fixed : embedding.range ≤ fixedSpace
    (starRepresentation (K.map H.subtype) (J.pCoreIn 2))
    (starImage (K.map H.subtype) (J.pCoreIn 2) (J.pCoreIn 2))
  intertwines : ∀ (x : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) v,
    embedding (BinaryNaturalDual.naturalDualRepresentation
      (B.componentProjection (inclusion ((map_subtype_le _).trans inf_le_left) x)) v) =
      starRepresentation (K.map H.subtype) (J.pCoreIn 2)
        (toStarImage (K.map H.subtype) (J.pCoreIn 2) (inclusion residual_le x)) (embedding v)
  moved : embedding.range ≤ subspaceCommutator
    (starRepresentation (K.map H.subtype) (J.pCoreIn 2)) ⊤
    (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype))
  fixed_disjoint : Disjoint embedding.range (fixedSpace
    (starRepresentation (K.map H.subtype) (J.pCoreIn 2))
    (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)))

variable (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
include D h in
/-- Construct the moved and fixed-disjoint embedding from the original witness. -/
theorem doubledFour_witness_star_module
    (B : DoubledBranch T L V 4) (hw : Chapter4.Section02.RankOneReciprocalEscape.Witness L V A J H U)
    (hWU : componentOrbit V (T : Subgroup G) ≤ U)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    Nonempty (FourStarModuleCoordinates B J H K) := by
  obtain ⟨hFK,hp,f,hf,hambient,hfixed,he⟩ :=
    D.doubledFour_witness_star_coordinates h B hw hWU K hK hq hout hfK e
  let q := (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)).subtype.comp
    ((toStarImage (K.map H.subtype) (J.pCoreIn 2)).comp (inclusion hFK))
  obtain ⟨hm,hd⟩ := BinaryNaturalDual.embedding_le_moved_and_disjoint_fixed (by decide : 2 ≤ 4)
    (starRepresentation (K.map H.subtype) (J.pCoreIn 2))
    (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype))
    _ hp q (fun x => (toStarImage _ _ (inclusion hFK x)).property) f hf he
  exact ⟨⟨hFK,hp,f,hf,hambient,hfixed,he,hm,hd⟩⟩

omit [Finite G] in
private theorem movedSection_quotient_injective
    {E Y Z : Type*} [Group E] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    {ρ : Representation (ZMod 2) E Y} {C : Subgroup E}
    (s : MovedSection ρ C) (f : Z →ₗ[ZMod 2] Y) (hf : Function.Injective f)
    (hm : f.range ≤ s.space.toSubmodule) (hd : Disjoint f.range (fixedSpace ρ C)) :
    Function.Injective (s.central.toSubmodule.mkQ.comp
      (f.codRestrict s.space.toSubmodule (fun v => hm ⟨v,rfl⟩))) := by
  let i := f.codRestrict s.space.toSubmodule (fun v => hm ⟨v,rfl⟩)
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro v hv
  change s.central.toSubmodule.mkQ (i v) = 0 at hv
  have hc : i v ∈ s.central.toSubmodule := (Submodule.Quotient.mk_eq_zero _).mp hv
  rw [s.central_eq] at hc
  have hc' : f v ∈ fixedSpace ρ C := fun x => congrArg Subtype.val (hc x)
  have hz : f v = 0 := Submodule.disjoint_def.mp hd (f v) ⟨v,rfl⟩ hc'
  exact hf (hz.trans f.map_zero.symm)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter1.RadicalExclusions.ModelReduction
open ChapterB.QuasisimpleSource Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A J H U : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)

/-- The actual B.5.1 moved section contains the original module, and the
literal central projection remains injective and intertwines the residual action. -/
@[expose] def FourStarModuleCoordinates.Classified
    {B : DoubledBranch T L V 4} {K : Subgroup H}
    (d : FourStarModuleCoordinates B J H K) : Prop :=
    let ρ := starRepresentation (K.map H.subtype) (J.pCoreIn 2)
    let O := offenderSubgroup ρ
    let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
    ∃ hCO : C ≤ O,
        ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (ρ.comp O.subtype) (C.subgroupOf O),
          ∃ i : BinaryNaturalDual.CoordinateSpace 4 →ₗ[ZMod 2] c.sectionData.space.toSubmodule,
            (∀ v, (i v : Additive (starV (K.map H.subtype) (J.pCoreIn 2))) = d.embedding v) ∧
            let g := c.sectionData.central.toSubmodule.mkQ.comp i
            Function.Injective g ∧
            g.range ≤ fixedSpace c.sectionData.central.quotientRepresentation
              ((starImage (K.map H.subtype) (J.pCoreIn 2) (J.pCoreIn 2)).subgroupOf O) ∧
            ∀ (x : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) v,
              g (BinaryNaturalDual.naturalDualRepresentation
                (B.componentProjection (inclusion ((map_subtype_le _).trans inf_le_left) x)) v) =
                c.sectionData.central.quotientRepresentation
                  ⟨toStarImage (K.map H.subtype) (J.pCoreIn 2) (inclusion d.residual_le x),
                    hCO (toStarImage _ _ (inclusion d.residual_le x)).property⟩ (g v)

include D h in
/-- Apply B.5.1 to the original star action and embed the original module through its central projection. -/
theorem doubledFour_witness_classified_star_module
    (B : DoubledBranch T L V 4) (hw : Chapter4.Section02.RankOneReciprocalEscape.Witness L V A J H U)
    (hWU : componentOrbit V (T : Subgroup G) ≤ U)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    ∃ d : FourStarModuleCoordinates B J H K, d.Classified := by
  obtain ⟨d⟩ := D.doubledFour_witness_star_module h B hw hWU K hK hq hout hfK e
  refine ⟨d,?_⟩
  have hc := hw.2.2.2.2.2.2.1
  obtain ⟨hCO,⟨c⟩⟩ := ChapterC.C27Source.star_moved_section_from_source
    (hc.constrained_source_input K hK hq hout hfK)
  dsimp only [FourStarModuleCoordinates.Classified]
  have hm : d.embedding.range ≤ c.sectionData.space.toSubmodule := by
    rw [c.sectionData.space_eq]
    change d.embedding.range ≤ subspaceCommutator _ ⊤ _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCO]
    exact d.moved
  have hd : Disjoint d.embedding.range (fixedSpace
      ((starRepresentation (K.map H.subtype) (J.pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation (K.map H.subtype) (J.pCoreIn 2))).subtype)
      ((starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (K.map H.subtype) (J.pCoreIn 2))))) := by
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hCO]
    exact d.fixed_disjoint
  let i := d.embedding.codRestrict c.sectionData.space.toSubmodule (fun v => hm ⟨v,rfl⟩)
  refine ⟨hCO,c,i,fun _ => rfl,movedSection_quotient_injective c.sectionData
    d.embedding d.injective hm hd,?_,?_⟩
  · rintro _ ⟨v,rfl⟩ a
    change c.sectionData.central.toSubmodule.mkQ (c.sectionData.space.toRepresentation a (i v)) =
      c.sectionData.central.toSubmodule.mkQ (i v)
    congr 1
    apply Subtype.ext
    exact d.radical_fixed ⟨v,rfl⟩ ⟨a.val.val,a.property⟩
  · intro x v
    change c.sectionData.central.toSubmodule.mkQ (i _) =
      c.sectionData.central.toSubmodule.mkQ (c.sectionData.space.toRepresentation _ (i v))
    congr 1
    apply Subtype.ext
    exact d.intertwines x v

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
