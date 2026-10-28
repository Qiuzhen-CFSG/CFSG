module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.AmbientComparison
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Fitting.Orders
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Assembly
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedGeneration
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Original local planes and the forced augmentation cover

In the full-denominator case of 13.8.33, a natural four-dimensional
U_H/V₁ supplies the two literal local planes in U_L/V. We construct the
section action, its two S₃ parabolics, commutator generation and the
rank-six second local span from the earlier source hypotheses. The
ambient displacement comparison then excludes this branch. Consequently
U_L is abelian and U_H/V₁ is the whole five-dimensional augmentation
cover, with its seed marking and constant line retained.

The component marking is derived from the actual component supplement
H = KT and the prescribed S₆ marking of H/O₂(H); no independent compatible
component marking is assumed in the resulting cover theorem.

The earlier ordinary component and marked-section setup remains with
qt-d-138-six-g2-source. The earlier 13.5.4 and 13.7.6 inputs are explicit;
the original-source assembly must discharge them. The cover permutation
argument, 13.4.1 application, strict denominators and terminal assembly
remain with qt-d-138-a6-endgame-source. This is not full 13.8.33.

Source: Aschbacher--Smith, 13.8.6 and the proof of 13.8.33,
printed pp.948 and 966--967.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open TransvectionParabolic
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

private theorem standingFlag (d : LocalSetup T L V V₁ V₂ V₃ M G₁) :
    Marking.StandingFlag T L V V₁ V₂ V₃ :=
  ⟨d.normalizes_L,d.normalizes_V,d.line_le_plane,d.plane_le_seed,d.seed_le,
    ⟨d.line_card,d.plane_card,d.seed_card⟩,d.line_stable,d.plane_stable,d.seed_stable⟩

private theorem standingNatural (d : LocalSetup T L V V₁ V₂ V₃ M G₁) :
    Marking.StandingNatural L V (le_sup_left.trans d.normalizes_V) := by
  exact ⟨6,Or.inr rfl,d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _),
    d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _),d.coordinate,d.conjugation⟩

private theorem fixed_bot (d : LocalSetup T L V V₁ V₂ V₃ M G₁) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro x hx
  have hx' : (⟨x,hx.1⟩ : V) ∈ (centralizer (L : Set G)).comap V.subtype := hx.2
  rw [local_centralizer_bot d] at hx'
  exact congrArg Subtype.val hx'

private theorem ordinary_inputs (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    Nonempty (ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.NaturalSetup
      L (T : Subgroup G) V V₁) := by
  rcases local_quotient_alternatives d with ⟨e,he⟩ | ⟨e,he⟩
  · exact LocalFitting.ordinary_natural d e he
  · have hc := Nat.card_congr (centerCongr (e.symm.trans eL)).toEquiv
    rw [Representation.Hexacode.even_center_card,
      alternatingGroup.center_eq_bot (by simp),card_bot] at hc
    omega

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

private noncomputable def sourceSection
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁) :
    ConjugationSection H (Source.UH H V₃) V₁ (tildeRepresentation H _ V₁ a) where
  le := h.UH_le_H
  normalizes := le_normalizer_conjugateSpanBy V₃ H
  centralizes := h.H_centralizes
  line_le := d.line_le_uh H
  quotient := {
    toFun := fun u => Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  surjective := QuotientGroup.mk'_surjective _
  kernel := QuotientGroup.ker_mk' _
  conjugates := fun h u => congrArg Additive.ofMul (a.conjugation h u)

private theorem section_image
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁) (B : Subgroup G) :
    (sourceSection d h a).image B = quotientSpace (Source.UH H V₃) V₁ B := rfl

private theorem full_commutator
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (hL : sourceOne L T V₁ ≤ H)
    (hg : Coinvariants.ker ((tildeRepresentation H _ V₁ a).comp
      ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hL))) = ⊤) :
    Source.UH H V₃ = ⁅Source.UH H V₃, sourceOne L T V₁⁆ := by
  let s := sourceSection d h a
  have hline : V₁ ≤ ⁅Source.UH H V₃,sourceOne L T V₁⁆ := by
    exact (d.line_le_plane.trans d.plane_le_seed).trans
      ((Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup d)).symm.le.trans
        (commutator_mono (le_conjugateSpanBy _ _) le_rfl))
  have hc : Coinvariants.ker ((tildeRepresentation H _ V₁ a).comp
      ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hL))) ≤
        s.image ⁅Source.UH H V₃,sourceOne L T V₁⁆ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨l,v⟩,rfl⟩
    obtain ⟨u,rfl⟩ := s.surjective (Multiplicative.ofAdd v)
    change tildeRepresentation H _ V₁ a (QuotientGroup.mk' (pCore 2 H)
      (inclusion hL l)) (s.quotient u).toAdd - (s.quotient u).toAdd ∈ _
    rw [s.displacement]
    refine ⟨_,?_,rfl⟩
    rw [commutator_comm]
    exact commutator_mem_commutator l.property u.property
  apply le_antisymm _ (le_normalizer_iff_commutator_le_left.mp
    (hL.trans (le_normalizer_conjugateSpanBy _ _)))
  intro u hu
  apply (s.quotient_mem_image_iff _ hline ⟨u,hu⟩).mp
  exact hc (hg.symm ▸ Submodule.mem_top)

/-- Construct both literal local planes in the four-dimensional branch. -/
theorem natural_source_planes
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hF : ∀ (k : Source.starImage H K) v,
      F (tildeRepresentation H _ V₁ a k v) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (eK k) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.canonicalPlane)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁) :
    ∃ s : SectionStructure.Data L H (T : Subgroup G) (sourceOne L T V₁)
      (EarlierCore.localResidual L V₂) V V₂ V₃,
      ∃ e₁ : (((((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict) ⧸
        pCore 2 ((((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
          (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3),
      ∃ e₂ : ((((EarlierCore.localResidual L V₂ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map
        (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict) ⧸
        pCore 2 (((EarlierCore.localResidual L V₂ ⊔ (T : Subgroup G)).subgroupOf
          (L ⊔ (T : Subgroup G))).map
          (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3),
        SourceLocalPlanes s e₁ e₂ := by
  let _ := local_elementary d
  let _ := d.abelian_span
  let _ := SectionStructure.VH_commutative_of_global_span G₁ H V hHz.2.1
  let ρ := tildeRepresentation H _ V₁ a
  have hρ : TransvectionRecognition.IsConjugation H V₃ V₁ ρ :=
    fun x u => congrArg Additive.ofMul (a.conjugation x u)
  let sec := sourceSection d h a
  obtain ⟨n⟩ := ordinary_inputs d eL
  let flag := standingFlag d
  let en := (flag.componentSetup (Marking.standing_natural_earlier (standingNatural d)) ⟨eL⟩).extend
  have h₁ : sourceOne L T V₁ = EarlierCore.localResidual L V₁ :=
    EarlierCore.residual_relative_normalizer_eq L T V₁ T.isPGroup' d.normalizes_L d.line_stable
  have h₂ : EarlierCore.localResidual L V₂ = BarQuotients.sourceResidual L T V₂ :=
    en.plane_residual_eq.symm
  have hHz' : H ∈ Source.Hz (EarlierCore.localResidual L V₁) T (normalizer (V₁ : Set G)) M := by
    rw [← h₁,← d.first_normalizer]
    exact hHz
  obtain ⟨_,_,_,hmark,_,_,hI,hres,_,hL₂,hgen,_,_,hcomm₂,hU₂⟩ :=
    Marking.source_marking_and_core T L V V₁ V₂ V₃ M H K flag (standingNatural d)
      earlier1376 earlier1354 hHz' hK hprod ρ hρ eK (Or.inl ⟨F,hF⟩)
  let ld := SourceAssembly.localData_of_naturalSetup (H := H) en earlier1354 h.T_le_H
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) ρ hρ
  obtain ⟨lm⟩ := LocalMarking.nonempty_compatibleMarking en ld
  have hrank : Module.finrank (ZMod 2) (Additive (Source.U2 H V V₂)) = 6 := by
    have hr := RankDoubling.source_rank_reduction_of_source_data H V V₂ V₃ V₁
      (EarlierCore.localI L V₁ V₂) (EarlierCore.localResidual L V₂) ld lm
      (SourceAssembly.seed_core_commutator (H := H) en h.T_le_H)
      (SourceAssembly.flag_index_two d.plane_le_seed (by decide : (4 : ℕ) ≠ 0)
        d.plane_card d.seed_card) d.plane_card
    rcases SourceAssembly.orbitMarking_of_markedParabolic K T ρ hρ hmark with hm | hm
    · obtain ⟨m⟩ := hm
      rw [RankDoubling.MarkedOrbit.natural_finrank (V := V) d.line_le_plane
        d.plane_le_seed d.seed_le m] at hr
      exact hr
    · obtain ⟨m⟩ := hm
      have hf : Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 4 :=
        F.finrank_eq.trans (by simpa using BinaryPermutation.finrank_natural_even (Fin 6) (by decide))
      have hm : Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 5 :=
        m.equiv.finrank_eq.trans (by simpa using BinaryPermutation.finrank_core (Fin 6))
      omega
  have hKH : K ≤ H := by
    intro k hk
    change k ∈ (H : Set G)
    rw [hprod]
    exact ⟨k,hk,1,(T : Subgroup G).one_mem,mul_one k⟩
  let _ := SectionStructure.component_normal_of_product H K T hKH h.T_le_H hK T.isPGroup'
    (by
      intro x
      have hx : (x : G) ∈ (K : Set G) * (T : Set G) := hprod ▸ x.property
      exact hx)
  let _ : (Source.starImage H K).Normal :=
    Subgroup.Normal.map (inferInstance : (K.subgroupOf H).Normal)
      (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  have hker : ∀ x : H, (∀ u : Source.UH H V₃, ⁅(x : G),(u : G)⁆ ∈ V₁) → x ∈ pCore 2 H := by
    intro x hx
    have hk := (h.mem_kernel_iff h.UH_le_H).mpr ⟨x.property,fun u hu => by
      change ⁅u,(x : G)⁆ ∈ V₁
      rw [← commutatorElement_inv]
      exact V₁.inv_mem (hx ⟨u,hu⟩)⟩
    rw [h.kernel_UH_eq_QH] at hk
    exact (mem_map_iff_mem H.subtype_injective).mp hk
  have hseed := (SectionStructure.UH_barKernel_commutator L H K T V V₁ V₃ n
    h.sylow_centralizer h.T_le_H (d.line_le_plane.trans d.plane_le_seed) d.seed_le
    ρ sec hker eK F hF hp).trans d.seed_le
  have hVL := SectionStructure.original_V_generated L T V V₁ V₃ n (fixed_bot d) d.seed_le
    (by intro he; have hc := d.seed_card; rw [he,card_bot] at hc; contradiction)
  have hUP := Section07.span_UH_L_le_core (localNaturalSetup d) h
    (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  have hnormal := SectionStructure.V_normal_in_UL L H V V₃ d.seed_le hVL
  let _ := hnormal
  have helem := SectionStructure.ULsection_elementary_of_UH L H T V V₃ d.seed_le
    d.normalizes_V (hUP.trans (pCoreIn_le 2 _)) hseed
  let _ := helem
  have hn := SectionStructure.LT_normalizes_UL L H T V₃ h.T_le_H d.normalizes_L
  have hcomm := SectionStructure.UL_barKernel_commutator_of_UH L H T V V₃
    d.normalizes_V (hUP.trans (pCoreIn_le 2 _)) hseed
  let _ := barKernel_normal (L ⊔ (T : Subgroup G)) V d.normalizes_V
  obtain ⟨τ,hτ⟩ := exists_section_representation (L ⊔ (T : Subgroup G)) (Source.UL L H V₃) V
    (barKernel (L ⊔ (T : Subgroup G)) V) hn d.normalizes_V hcomm
  obtain ⟨σ,hσ⟩ := SectionStructure.bar_action_on_image (L ⊔ (T : Subgroup G)) (Source.UL L H V₃) V
    hn d.normalizes_V τ hτ
  have hKL : Source.K2 H V₂ ≤ normalizer (EarlierCore.localResidual L V₂ : Set G) :=
    ((Source.K2_le_centralizer H V₂).trans inf_le_right).trans
      ((Subgroup.centralizer_le_normalizer _).trans
        (local_normality (EarlierCore.localI L V₁ V₂) _ _ V₂ hI hres.symm))
  let s : SectionStructure.Data L H T (sourceOne L T V₁) (EarlierCore.localResidual L V₂) V V₂ V₃ := {
    contains := SectionStructure.V_le_UL L H V V₃ hVL
    normal := hnormal
    elementary := helem
    normalizes_UL := hn
    normalizes_V := d.normalizes_V
    normalizes_UH := SectionStructure.L1T_normalizes_UH H T _ V₃ (le_sup_left.trans hHz.1.2) h.T_le_H
    normalizes_U2 := SectionStructure.L2T_normalizes_U2 H T _ V V₂ h.T_le_H d.plane_stable
      (le_sup_right.trans d.normalizes_V) ((hL₂.trans le_sup_left).trans d.normalizes_V) hKL
    kernel_commutator := hcomm
    action := σ
    conjugation := hσ }
  obtain ⟨eb⟩ := exists_full_denominators_bar_equiv d h c hDH hDg
  obtain ⟨q₁,q₂,_⟩ := BarQuotients.source_quotients_and_generation_of_card n (fixed_bot d) eb
    V₂ V₃ (sourceOne L T V₁) (EarlierCore.localResidual L V₂) d.plane_le_seed d.seed_le
    d.plane_card d.plane_stable
    (SourceAssembly.flag_index_two d.seed_le (by decide : (8 : ℕ) ≠ 0) d.seed_card
      en.natural_order) rfl h₂
  have hdiff := ChiefGeneration.coinvariants_eq_top_of_earlier (sourceOne L T V₁) T G₁ M H K V₃ V₁
    chief hHz hKH hK ρ sec eK F hF
  have hcomm₁ := full_commutator d h a (le_sup_left.trans hHz.1.2) hdiff
  exact ⟨s,q₁.some,q₂.some,local_planes_of_source_commutators L H T (sourceOne L T V₁)
    (EarlierCore.localResidual L V₂) V V₁ V₂ V₃ _ s.normalizes_UL s.action s.conjugation
    s.normalizes_UH s.normalizes_U2 n (fixed_bot d) (BarQuotients.sourceResidual_le_L n V₁) hL₂
    ρ sec (d.line_le_plane.trans d.plane_le_seed) F hp
    (seed_intersection d h c hDH hDg) hU₂ hrank hcomm₁ hcomm₂ q₁.some q₂.some hgen hKL⟩

/-- The set-product supplement identifies the actual component image with
A₆ under any prescribed S₆ marking of H/O₂(H). -/
private theorem original_component_marking
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hTH : (T : Subgroup G) ≤ H)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6)) :
    ∃ eK : Source.starImage H K ≃* alternatingGroup (Fin 6),
      ∀ k : Source.starImage H K, e k = (eK k).val := by
  have hKH : K ≤ H := by
    intro k hk
    change k ∈ (H : Set G)
    rw [hprod]
    exact ⟨k,hk,1,(T : Subgroup G).one_mem,mul_one k⟩
  let _ := hK.perfect
  have hp : IsPPerfect 2 (K.subgroupOf H) := by
    intro N hN hq
    let _ := hN
    have hs : Subsingleton ((K.subgroupOf H) ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent ((K.subgroupOf H) ⧸ N) hq.isNilpotent
    apply eq_top_iff.mpr
    intro k _
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  have hr : pResidual 2 H = K.subgroupOf H :=
    pResidual_eq_of_subnormal_product (K.subgroupOf H) ((T : Subgroup G).subgroupOf H)
      hK.subnormal hp T.isPGroup'.comap_subtype (by
        intro x
        have hx : (x : G) ∈ (K : Set G) * (T : Set G) := hprod ▸ x.property
        obtain ⟨k,hk,t,ht,he⟩ := hx
        exact ⟨⟨k,hKH hk⟩,hk,⟨t,hTH ht⟩,ht,Subtype.ext he⟩)
  have hi : (Source.starImage H K).map e.toMonoidHom = alternatingGroup (Fin 6) := by
    change ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).map e.toMonoidHom = _
    rw [← hr,map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),
      map_pResidual_of_surjective 2 _ e.surjective,Equiv.Perm.twoResidual_eq_alternating]
  refine ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr hi),fun _ => rfl⟩

/-- Full denominators force the whole five-dimensional cover and abelianness
of U_L. The local planes, their ranks, markings and section action are
constructed, not assumed. The covering constant line is retained. -/
theorem full_denominators_abelian_cover
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁) :
    IsMulCommutative (Source.UL L H V₃) ∧
      ∃ F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6),
        (∀ g v, F (tildeRepresentation H _ V₁ a g v) =
          BinaryPermutation.coreRepresentation (Fin 6) (e g) (F v)) ∧
        (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
          Representation.SixLetterRadicalDisplacement.W := by
  obtain ⟨eK,hKmark⟩ := original_component_marking K hK h.T_le_H hprod e
  have h₂ : EarlierCore.localResidual L V₂ = BarQuotients.sourceResidual L T V₂ :=
    (EarlierCore.residual_relative_normalizer_eq L T V₂ T.isPGroup'
      d.normalizes_L d.plane_stable).symm
  have hno (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
      (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
        BinaryPermutation.naturalRepresentation (Fin 6) (e g) (F v))
      (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.canonicalPlane) : False := by
    have hfK : ∀ (k : Source.starImage H K) v,
        F (tildeRepresentation H _ V₁ a k v) =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (eK k) (F v) := by
      intro k v
      rw [hF,hKmark]
      rfl
    obtain ⟨s,e₁,e₂,hplanes⟩ := natural_source_planes d h c hDH hDg hHz K hK hprod eL
      a eK F hfK hp earlier1354 earlier1376 chief
    exact original_local_planes_impossible d h c hH hDH hDg hcentral a e model eL
      s e₁ e₂ hplanes h₂
  have hab : IsMulCommutative (Source.UL L H V₃) := by
    classical
    by_contra hn
    obtain ⟨F,hF,hp⟩ := natural_model_of_nonabelian d h c hDH hDg hcentral a e model hn
    exact hno F hF hp
  refine ⟨hab,?_⟩
  rcases model.marked_cases a e with ⟨F,hF,hp⟩ | hc
  · exact (hno F hF hp).elim
  · exact hc

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
