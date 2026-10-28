module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.ProjectiveTwoFour
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.NativeSource
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.FiveExclusion
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal.RankSourceActions
public import Theory.SpecificGroups.SymmetricFive.RadicalRange
public import Theory.SpecificGroups.SymmetricFive.LocalTwoCore
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality

/-!
# The original PSL₂(4) terminal contradiction

The contained component gives compatible K*≃A₅ and H*≃S₅ markings. A
transvection has nonsolvable normal closure, so native G.6.4 supplies an
actual natural component section. Perfectness and the S₅ commutator identify
this component with K; orders leave only the five-letter natural section.
The original seed-plane exclusion rules it out. Thus the selected critical
pair has rank greater than one.

The local two-core is even in the marked S₅ action, placing the same critical
actor inside a Sylow four-group of K*. On the literal V_H/U_H section the
original source supplies a noncentral permutation-module surjection and
quadraticity. The genuine five-point overlap coordinates then give the
contradiction. All quotient actions and the component inclusion are retained.

The unrestricted-overgroup application reduces internally to KL₁T. Only
full SL₃(4) remains in the higher-field catalogue. Its natural-plus-dual
recognition and critical-subspace contradiction, the whole binary quotient
exclusion and 13.8.19–21 assembly remain with qt-d-138-fields-source. Earlier
original inputs retain their producers through qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.20, printed p.955, using G.6.4, 13.7.6(3),
13.8.4(5–6), 13.8.8(2) and 13.8.18(4).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExternalModules
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem twoFour_unique_component
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eA : Source.starImage H K ≃* alternatingGroup (Fin 5))
    (eH : Source.Hstar H ≃* Equiv.Perm (Fin 5))
    (he : ∀ k : Source.starImage H K, eH k = eA k)
    {J : Subgroup G} (hJH : J ≤ H) (hJ : (J.subgroupOf H).IsCComponent) : J = K := by
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hJs : (Source.starImage H J).IsCComponent := hJ.map_quotient (pCore 2 H)
  have hKs : (Source.starImage H K).IsCComponent := hK.map_quotient (pCore 2 H)
  have hmap := hJs.map_equiv eH
  let := hmap.perfect
  have hle : (Source.starImage H J).map eH.toMonoidHom ≤ alternatingGroup (Fin 5) := by
    rw [←alternatingGroup.commutator_perm_eq (by simp),
      ←Subgroup.commutator_eq_self (H := (Source.starImage H J).map eH.toMonoidHom)]
    exact commutator_mono le_top le_top
  have hJK : Source.starImage H J ≤ Source.starImage H K := by
    intro x hx
    have ha := hle (mem_map_of_mem eH.toMonoidHom hx)
    obtain ⟨k,hk⟩ := eA.surjective ⟨eH x,ha⟩
    have hek : eH k = eH x := (he k).trans (congrArg Subtype.val hk)
    exact eH.injective hek ▸ k.property
  have hs := hJs.eq_of_le hKs hJK
  have hj := hJ.eq_of_map_quotient_eq hK (pCore 2 H) hs
  have hm := congrArg (Subgroup.map H.subtype) hj
  simpa only [map_subgroupOf_eq_of_le hJH,map_subgroupOf_eq_of_le hKH] using hm

/-- Native G.6.4 and the original seed plane exclude transvections in the
contained PSL₂(4) case, without a plane-rank premise from 13.7.6. -/
theorem source_projectiveTwo_four_not_transvection
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hm : ClassicalGroup.IsPSL (Source.starImage H K) 2 4)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (act : LinearThree.SourceAction H V₃ V₁) (t : Source.Hstar H) :
    ¬ IsTransvection act.representation t := by
  intro ht
  obtain ⟨hLK,_,_,_,eA,eH,he⟩ := source_projectiveTwo_four_structure c hm
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hH := c.component.local_overgroup
  have hF9 := c.f9 H hH
  have hns : ¬ Group.IsSolvable (normalClosure ({t} : Set (Source.Hstar H))) := by
    intro hsol
    let := hsol
    have hle := Theory.SpecificGroups.FivePointSylowParabolic.solvable_normal_le_ker
      eH.toMonoidHom (by rw [MonoidHom.range_eq_top.mpr eH.surjective]; exact le_top)
      (normalClosure ({t} : Set (Source.Hstar H)))
    have hm := hle (subset_normalClosure (Set.mem_singleton t))
    exact ht.ne_one (eH.injective (hm.trans (map_one eH).symm))
  have hV₁ : V₁ ≠ ⊥ := by
    intro hb
    have hc := c.localSetup.line_card
    rw [hb,card_bot] at hc
    omega
  have hpV₁ : IsPGroup 2 V₁ :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one] using c.localSetup.line_card)
  have hc : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H := by
    intro x hx
    change x ∈ (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).QH
    rw [←hF9.kernel_UH_eq_QH]
    apply (hF9.mem_kernel_iff hF9.UH_le_H).mpr
    refine ⟨commutatorPreimage_le _ _ _ hx,?_⟩
    intro u hu
    rw [←commutatorElement_inv]
    apply V₁.inv_mem
    exact commutator_commutatorPreimage_le H (Source.UH H V₃) V₁
      (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
      (commutator_mem_commutator hx hu)
  obtain ⟨J,hJH,hJ,_,_,_,_,hsection⟩ :=
    exists_component_natural_section c.localSetup.counterexample.qtke
      LinearThree.OriginalExclusion.g64_source_knownSimple
      H (one L T V₁) T G₁ M V₁ V₃ V₁ hH hV₁ hpV₁ c.localSetup.first_normalizer
      act.representation act.conjugation hc t ht hns
  have hJK := twoFour_unique_component hKH c.component.component eA eH he hJH hJ
  subst J
  have hcard : Nat.card (Source.starImage H K) = 60 := by
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rcases hsection with ⟨n,hn,hb,e,hs⟩ | ⟨n,hn,hb,e,hs⟩
  · have hd : Nat.card (BinaryLinear.GL (Fin n → ZMod 2)) = BinaryLinear.order n :=
      BinaryLinear.card_GL_of_finrank (by simp)
    rw [Nat.card_congr e.toEquiv,hd] at hcard
    interval_cases n <;> norm_num [BinaryLinear.order,Fin.prod_univ_succ] at hcard
  · let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hn5 : n = 5 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hcard
      by_contra hne
      have hns : n = 6 ∨ n = 7 ∨ n = 8 := by omega
      rcases hns with rfl | rfl | rfl <;> norm_num [Nat.factorial] at hcard
    subst n
    exact Section07.ModelExclusions.not_five_natural_of_one_le
      (localNaturalSetup c.localSetup) hH hF9 hJH hJ hLK act.representation act.conjugation
      ((Components.componentStarEquiv H K hJH hJ).trans e) hs

private theorem twoFour_transvection_of_rank_one
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) A E) (a : A)
    (hc : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) : IsTransvection ρ a := by
  let e := LinearEquiv.ofBijective (ρ a) (ρ.apply_bijective a)
  have hr : Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) = 1 :=
    hc
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr hr.le
  have hformula (w : E) : ρ a w = w + f w • v :=
    congrArg (fun l : E →ₗ[ZMod 2] E => l w) he
  have hne : ρ a ≠ LinearMap.id := by
    intro hh
    have hz : e.toLinearMap - LinearMap.id = 0 := sub_eq_zero.mpr hh
    rw [hz, LinearMap.range_zero, finrank_bot] at hr
    omega
  have hf : f ≠ 0 := by
    intro hz
    apply hne
    ext w
    simpa only [hz, LinearMap.zero_apply, zero_smul, add_zero, LinearMap.id_apply] using hformula w
  have hv : v ≠ 0 := by
    intro hz
    apply hne
    ext w
    simpa only [hz, smul_zero, add_zero, LinearMap.id_apply] using hformula w
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with hz | ho
    · exact hz
    have hev : e v = 0 := by
      change ρ a v = 0
      rw [hformula, ho, one_smul, ZModModule.add_self]
    exact (hv (e.map_eq_zero_iff.mp hev)).elim
  exact ⟨f, v, hf, hv, hfv, hformula⟩


/-- No element of the original actor has displacement rank one. -/
theorem source_projectiveTwo_four_no_rank_one
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hm : ClassicalGroup.IsPSL (Source.starImage H K) 2 4)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (act : LinearThree.SourceAction H V₃ V₁) (t : Source.Hstar H) :
    Module.finrank (ZMod 2) (LinearMap.range (act.representation t - LinearMap.id)) ≠ 1 := by
  intro ht
  exact source_projectiveTwo_four_not_transvection c hm act t
    (twoFour_transvection_of_rank_one act.representation t ht)

private theorem twoFour_core_le_component
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hm : ClassicalGroup.IsPSL (Source.starImage H K) 2 4)
    (eA : Source.starImage H K ≃* alternatingGroup (Fin 5))
    (eH : Source.Hstar H ≃* Equiv.Perm (Fin 5))
    (he : ∀ k : Source.starImage H K, eH k = eA k) :
    (Source.starImage H (one L T V₁) ⊔ Source.starImage H (T : Subgroup G)).pCoreIn 2 ≤
      Source.starImage H K := by
  obtain ⟨hLK,hord,_,_,_⟩ := source_projectiveTwo_four_structure c hm
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hLH := hLK.trans hKH
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans c.component.local_overgroup.1.2
  let A := Source.starImage H (one L T V₁) ⊔ Source.starImage H (T : Subgroup G)
  let S := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hS : (S : Subgroup (Source.Hstar H)) = Source.starImage H (T : Subgroup G) := rfl
  have h3 : 3 ∣ Nat.card (Source.starImage H (one L T V₁)) := by
    rw [←LocalFitting.ordinary_core_card c.localSetup hord,
      Nat.card_congr (starCoreQuotientEquiv H (one L T V₁) hLH).toEquiv]
    exact card_quotient_dvd_card _
  have h3A : 3 ∣ Nat.card (A.map eH.toMonoidHom) := by
    rw [←Nat.card_congr (A.equivMapOfInjective eH.toMonoidHom eH.injective).toEquiv]
    exact h3.trans (card_dvd_of_le (show Source.starImage H (one L T V₁) ≤ A from le_sup_left))
  have hcore := Theory.SpecificGroups.SymmetricFive.LocalTwoCore.core_le_alternating
    (A.map eH.toMonoidHom) (S.mapSurjective eH.surjective)
    (by rw [Sylow.coe_mapSurjective,hS]; exact map_mono le_sup_right) h3A
  have him := Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le eH.toMonoidHom A
  intro x hx
  have ha := hcore (him (mem_map_of_mem eH.toMonoidHom hx))
  obtain ⟨k,hk⟩ := eA.surjective ⟨eH x,ha⟩
  have hek : eH k = eH x := (he k).trans (congrArg Subtype.val hk)
  exact eH.injective hek ▸ k.property

/-- The genuine PSL₂(4) branch contradicts quadraticity on the literal
V_H/U_H. The source action, coset surjection, conjugator and rank are constructed. -/
theorem source_projectiveTwo_four_false
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hm : ClassicalGroup.IsPSL (Source.starImage H K) 2 4) : False := by
  classical
  let : (K.subgroupOf H).Normal := c.component.normal
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have hH := c.component.local_overgroup
  have hF9 := c.f9 H hH
  let : IsElementaryAbelian 2 (Source.UH H V₃) := c.localSetup.uh_elementary hH
  let act := Comparison.conjugationAction (c.localSetup.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  have hqs := (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
    c.centralizer c.noncentral_core c.earlier1339 hH K c.component.component).2
  obtain ⟨w⟩ := CriticalSource.exists_selected_witness c.localSetup hH hF9
    (by rw [←c.component.generated,sup_assoc]) c.component.component c.component.normal hqs
    c.centralizer c.noncentral_core act.representation act.conjugation
    (source_projectiveTwo_four_no_rank_one c hm act)
  obtain ⟨eA,eH,he,d,hd⟩ := source_projectiveTwo_four_point_coordinates c hm
  have hLH : one L T V₁ ≤ H := le_sup_left.trans hH.1.2
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  let A := Source.starImage H (one L T V₁) ⊔ Source.starImage H (T : Subgroup G)
  have hcore := twoFour_core_le_component c hm eA eH he
  have hp : IsPGroup 2 ((A.pCoreIn 2).subgroupOf (Source.starImage H K)) :=
    (isPGroup_pCoreIn 2 A).comap_subtype
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hplace : Source.starImage H w.alpha ≤
      (P : Subgroup (Source.starImage H K)).map (Source.starImage H K).subtype := by
    have hle := map_mono (f := (Source.starImage H K).subtype) hP
    rw [map_subgroupOf_eq_of_le hcore] at hle
    exact (w.alpha_star_le_core hLH hTH).trans hle
  have hconj : (Source.starImage H w.pair.Vgamma).map
      (MulAut.conj (QuotientGroup.mk' (pCore 2 H) w.conjugator)).toMonoidHom =
      Source.starImage H w.alpha :=
    (AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.starImage_conjugate
      w.pair.Vgamma w.actor_le w.conjugator).symm
  have hrank : 2 ≤ rank (Source.starImage H w.alpha) := by
    rw [←hconj,rank_map_conj]
    exact w.rank_gt_one
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := c.localSetup.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  obtain ⟨a,ha⟩ := Terminal.exists_rank_section_action c.localSetup hF9 hH.2.1 c.noncentral_core
  let ρ := SolvableExclusion.Three.Supercritical.Offenders.linearAction a
  have hear := CriticalSource.earlier_inputs c.localSetup hH hF9 c.centralizer
    c.noncentral_core act.representation act.conjugation
  have hnorm : H ⊓ M ≤ normalizer (V : Set G) := by
    rw [source_overlap_normalizer c]
    exact inf_le_right
  let : Fintype (Source.Hstar H ⧸ Source.starImage H (H ⊓ M)) := Fintype.ofFinite _
  obtain ⟨f,hf⟩ := source_13_8_4_permutation_surjection H M V V₃ c.localSetup.seed_le
    hear.flag_index hear.noncentral hnorm ρ ha
  have hquad := Terminal.rank_section_quadratic c.localSetup hF9 a w.pair (1 : H)
  have hquad' : IsQuadratic ρ (Source.starImage H w.pair.Vgamma) := by
    have he : w.pair.Vgamma.map (MulAut.conj ((1 : H) : G)).toMonoidHom = w.pair.Vgamma := by
      change w.pair.Vgamma.map (MulAut.conj (1 : G)).toMonoidHom = _
      rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from by ext x; simp]
      exact Subgroup.map_id _
    rw [he] at hquad
    exact hquad
  exact ExceptionalFields.linear_two_four_permutation_contradiction H K M V V₃
    w.alpha w.pair.Vgamma eA eH he ρ d hd f.toLinearMap hf
    (fun h v => LinearMap.congr_fun (f.isIntertwining' h) v)
    (A6Endgame.MarkedQuotient.noncentral H V V₃ ρ ha hear.noncentral) P
    (QuotientGroup.mk' (pCore 2 H) w.conjugator) hconj hplace hrank hquad'

/-- The intrinsic PSL₂(4) component quotient is excluded by the same source proof. -/
theorem source_not_projectiveTwo_four
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 := by
  intro hm
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  exact source_projectiveTwo_four_false c
    (hm.of_mulEquiv (Components.componentStarEquiv H K hKH c.component.component).symm)


/-- Only full SL₃(4), retaining its scalar center, remains in the original
higher-field catalogue. Its terminal module contradiction is still required. -/
theorem source_higher_field_specialLinear_four
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4 :=
  (source_higher_field_linear_list c hfield).resolve_left (source_not_projectiveTwo_four c)

/-- The original PSL₂(4) exclusion applies to a component of any unrestricted
overgroup: reduction to KL₁T preserves the literal intrinsic quotient. -/
theorem original_no_projectiveTwo_four
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  exact source_not_projectiveTwo_four (Overgroups.reducedContext c K hKH hK)

/-- Every higher-field component of an unrestricted original overgroup would
be full SL₃(4). The preceding component source remains with its original producer. -/
theorem original_higher_field_specialLinear_four
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4 := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  exact source_higher_field_specialLinear_four (Overgroups.reducedContext c K hKH hK) hfield

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
