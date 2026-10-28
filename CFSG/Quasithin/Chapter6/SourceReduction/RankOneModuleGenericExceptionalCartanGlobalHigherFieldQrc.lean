module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldSpan
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeConstruction
public import CFSG.Quasithin.Chapter3.Section02.QrcInput
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalNormalReduction
public import CFSG.Quasithin.Chapter3.Section01.SourceDualNumerical
public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# The original Hermitian torus qrc configuration and cubic bound

The plus-torus/Sylow join has order |D||T|. Faithfulness of D on the
reduced omega-span makes its full centralizer a two-group, identifying
that centralizer with the join's two-core. The original H-intersection
normalizes the span because its Hall complement normalizes the Cartan
and centralizes omega. These are precisely Hypothesis 3.1.5, case (II).
Zero core of the literal DH join directly excludes common normal
subgroups, giving D.1.1 without uniqueness over the smaller DT join.

The numerical argument uses this actual common-normal exclusion.
In the inside-core case the multiple-chief-factor and dual-FF bounds
apply; the remaining unique-factor branch gives a residual Sylow and
contradicts the proved common-normal theorem. In the outside-core case,
normalization by H's actual maximal subgroup gives the E.2.13 bound.
Thus the cubic ratio of the literal DT action on its omega-span is at
most two. The semilinear lower bound and selection of the Hermitian
model remain distinct source obligations.

Source: Aschbacher--Smith 3.1.6, pp.573--575, and 5.1.6(4),
pp.632--633 (`refs/quasithin.pdf`). The numerical proof adapts the
existing Chapter3 SourceNumericalReduction/NormalReduction and
ReducedModuleSylow arguments, replacing only their uniqueness-based
common-normal exclusion by the actual zero-core one.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open Representation.OrthogonalFourMinus.FiniteModel
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
local instance (s : ℕ) : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

private theorem torus_join_card
    {T : Sylow 2 G} {L H A B D : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hDA : D ≤ A) :
    Nat.card (D ⊔ (T : Subgroup G) : Subgroup G) = Nat.card D * Nat.card T := by
  let U := (T : Subgroup G) ⊓ L
  have hDU : D ≤ normalizer (U : Set G) := hDA.trans (c.left_le.trans inf_le_right)
  have hDL : D ≤ L := hDA.trans (c.left_le.trans inf_le_left)
  have hUT : (U ⊔ D) ⊓ (T : Subgroup G) = U := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans (sup_le inf_le_right hDL))
    · exact le_inf le_sup_left inf_le_left
  have he : (U ⊔ D) ⊔ (T : Subgroup G) = D ⊔ (T : Subgroup G) := by
    exact le_antisymm (sup_le (sup_le (inf_le_left.trans le_sup_right) le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hTB : (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) :=
    (le_inf hTL ((le_inf (T : Subgroup G).le_normalizer hTL).trans
      inf_normalizer_le_normalizer_inf |>.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ normalizer ((U ⊔ D : Subgroup G) : Set G) :=
    hTB.trans (Prime.cartan_subgroup_preimage_normalized c hTL hpsl hDA)
  have hodd : Odd (Nat.card D) :=
    (OddHall.odd_hall_odd c.left_hall).of_dvd_nat (by
      have hd := card_dvd_of_le hDA
      rw [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv] at *
      exact hd)
  obtain ⟨k,hk⟩ := (T.isPGroup'.to_le (show U ≤ (T : Subgroup G) from inf_le_left)).exists_card_eq
  have hdis : Disjoint U D := disjoint_of_coprime_natCard (by
    rw [hk]
    exact hodd.coprime_two_left.pow_left k)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (U ⊔ D) (T : Subgroup G) hTN
  rw [card_sup_eq_mul_of_normalizes_of_disjoint U D hDU hdis,hUT,he,mul_assoc] at hc
  exact (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := U)) hc).symm

private theorem reduced_torus_centralizer
    {T : Sylow 2 G} {D V : Subgroup G}
    (hr : V ∈ reducedFamily (D ⊔ (T : Subgroup G)))
    (hc : Nat.card (D ⊔ (T : Subgroup G) : Subgroup G) = Nat.card D * Nat.card T)
    (hfaith : D ⊓ centralizer (V : Set G) = ⊥) :
    (D ⊔ (T : Subgroup G)).pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  let J := D ⊔ (T : Subgroup G)
  let C := J ⊓ centralizer (V : Set G)
  have hJN : J ≤ normalizer (V : Set G) := reduced_normalizes hr
  have hCN : J ≤ normalizer (C : Set G) :=
    (le_inf J.le_normalizer (hJN.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hDC : Disjoint C D := by
    apply disjoint_iff.mpr
    apply bot_unique
    rw [←hfaith]
    exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
  have hmul := card_sup_eq_mul_of_normalizes_of_disjoint C D (le_sup_left.trans hCN) hDC
  have hdiv : Nat.card C ∣ Nat.card T := by
    have hd := card_dvd_of_le (show C ⊔ D ≤ J from sup_le inf_le_left le_sup_left)
    rw [hmul,hc,mul_comm (Nat.card C)] at hd
    exact (Nat.mul_dvd_mul_iff_left (Nat.card_pos (α := D))).mp hd
  have hCP : IsPGroup 2 C := by
    obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
    exact isPGroup_iff_card_dvd_pow.mpr ⟨k,hdiv.trans (dvd_of_eq hk)⟩
  have hCcore : C ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes hCP inf_le_left hCN
  have hcoreT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)]
      using pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
  let := hr.2.1
  have hcoreC : J.pCoreIn 2 ≤ centralizer (V : Set G) := by
    have hh := (show IsPReduced 2 (V.subgroupOf J) from ⟨hr.2.2.choose,IsElementaryAbelian.subgroupOf hr.1,hr.2.2.choose_spec⟩).le_centralizer_pCore
    intro x hx v hv
    obtain ⟨q,hq,rfl⟩ := hx
    exact congrArg J.subtype (le_centralizer_iff.mp hh hq ⟨v,hr.1 hv⟩ hv)
  exact le_antisymm (le_inf hcoreT hcoreC)
    ((inf_le_inf_right _ (show (T : Subgroup G) ≤ J from le_sup_right)).trans hCcore)

/-- The original Hermitian plus torus and omega-span satisfy the actual
Hypothesis 3.1.5, in its intersection-normalizes-module case. -/
theorem Input.hermitian_plus_qrc_hypotheses
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s] (hs : 1 < s)
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s))
    (hDA : D ≤ A) (hDc : Nat.card D = 2^s-1) :
    Chapter3.QrcHypotheses T (normalizer (L : Set G))
      (D ⊔ (T : Subgroup G)) H
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) D) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let X := conjugateSpanBy Z D
  let J := D ⊔ (T : Subgroup G)
  have hg := h.hermitian_plus_span c s hm hDA hDc
  obtain ⟨hspan,hr⟩ := h.hermitian_plus_span_reduced c s hm hDA hDc
  let := hr.2.1
  have hJN : J ≤ normalizer (X : Set G) := reduced_normalizes hr
  have hcore := reduced_torus_centralizer hr
    (torus_join_card c h.sylow_normalizes h.linear hDA) hg.2.2.2
  have hHC := h.hermitian_omega_span_centralizes hH s hs hm
  have hBN : B ≤ normalizer (X : Set G) := by
    rw [show X = conjugateSpanBy Z A from hspan]
    exact normalizes_conjugateSpanBy Z A B
      ((c.right_le.trans inf_le_right).trans
        (hHC.trans (Subgroup.centralizer_le_normalizer _))) c.right_normalizes_left
  refine ⟨le_sup_right,
    sup_le (hDA.trans (c.left_le.trans (inf_le_left.trans L.le_normalizer))) h.sylow_normalizes,
    hH,hr.1,hJN,hr.2.1,?_,hcore,Or.inr ?_⟩
  · exact Chapter3.Section02.internalActionImage_core_of_reduced J X hr.1 hJN
      (show IsPReduced 2 (X.subgroupOf J) from ⟨hr.2.2.choose,IsElementaryAbelian.subgroupOf hr.1,hr.2.2.choose_spec⟩)
  · rw [inf_comm,←c.sylow_sup_right h.sylow_normalizes hH.1.1.2]
    exact sup_le (le_sup_right.trans hJN) hBN

/-- Zero core of the literal plus-torus/H join eliminates common normal
subgroups directly. No uniqueness over the smaller torus join is assumed. -/
theorem Input.hermitian_plus_qrc_configuration
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s] (hs : 1 < s)
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s))
    (hDA : D ≤ A) (hDc : Nat.card D = 2^s-1)
    (hz : (D ⊔ H).pCoreIn 2 = ⊥) :
    ChapterD.QRCConfiguration (D ⊔ (T : Subgroup G)) H (T : Subgroup G)
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) D) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hq := h.hermitian_plus_qrc_hypotheses hH c s hs hm hDA hDc
  apply hq.toQRCConfiguration
  rintro ⟨N,hNc,hN,hn⟩
  have hNT : N ≤ (T : Subgroup G) := hNc.trans (hq.core_eq_centralizer ▸ inf_le_left)
  have hgen : Chapter3.generated (D ⊔ (T : Subgroup G)) H = D ⊔ H := by
    rw [Chapter3.generated_eq_sup,sup_assoc,sup_eq_right.mpr hTH]
  have hnorm : D ⊔ H ≤ normalizer (N : Set G) := by
    simpa only [hgen] using (Chapter3.normalIn_iff_le_normalizer.mp hn).2
  have hcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hNT)
    (hNT.trans (hTH.trans le_sup_right)) hnorm
  exact hN (bot_unique (hz ▸ hcore))

open Chapter3 ChapterD ChapterD.UniqueFactor
open Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
section Numerical
variable {T : Sylow 2 G} {M M₀ H V : Subgroup G}

private theorem residual_sylow_of_reduced_module
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hp : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (U : Subgroup H) (hU : IsPReduced 2 U)
    (hj : ¬ elementaryAbelianMaxJ
      ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) ≤ centralizer (U : Set H)) :
    Chapter1.IsSylowIn 2 (M₀.pCoreIn 2)
      ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2) := by
  have hsq := sqtk_of_mem_H hG h.right_mem.1.1.1
  let S := T.subtype h.right_mem.1.1.2
  let := hU.normal
  let := hU.elementary
  rcases ChapterE.ThompsonAction.source_sylow_or_paired_five hsq S hp U hU hj with hs | hpair
  · rcases hs with hs | ⟨S₁,hs,hbs,_,hspan⟩
    · exact h.residual_sylow_of_baumann_sylow hJ hs
    · exact h.residual_sylow_of_baumann_span hJ hp S₁ hs hbs hspan
  obtain ⟨d,t,h₁,h₂,⟨c⟩⟩ := hpair
  obtain ⟨D,hn,hR⟩ := h.exists_normal_sylow_container_in_right
  let R := (M₀.pCoreIn 2).subgroupOf H
  have hRT : M₀.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [h.core_eq_centralizer]
    exact inf_le_left
  have hRS : R ≤ S := fun x hx => hRT hx
  have hnR : M₀ ≤ normalizer (M₀.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 M₀).le_normalizer_map M₀.subtype
  have hSR : (S : Subgroup H) ≤ normalizer (R : Set H) := by
    apply le_trans _ (le_normalizer_comap H.subtype)
    intro x hx
    exact (h.sylow_le.trans hnR) hx
  have hbmap : (ChapterB.baumann (S : Subgroup H)).map H.subtype =
      ChapterB.baumann (T : Subgroup G) := by
    have he := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change (ChapterB.baumann (S : Subgroup H)).map H.subtype =
      ChapterB.baumann ((S : Subgroup H).map H.subtype) at he
    have hm : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
    exact he.trans (congrArg ChapterB.baumann hm)
  have hBR : ChapterB.baumann (S : Subgroup H) ≤ R := by
    intro x hx
    exact (h.baumann_core hJ).2 (hbmap ▸ mem_map_of_mem H.subtype hx)
  have hn' : ChapterB.minimalParabolicMax S hp ≤ normalizer (D : Set H) := by
    rw [h.intrinsic_maximal_eq_intersection hp]
    exact hn
  have hs := ChapterE.ThompsonAction.paired_symmetric_residual_sylow_of_container
    S hp U hU hj _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    d c ⟨t,h₁,h₂⟩ D R hRS hSR hBR hR hn'
  have hm := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hs
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le (hRT.trans h.right_mem.1.1.2)] at hm
private theorem not_uniqueFactor_coreClosure_centralizes
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : ChapterD.QRCConfiguration M₀ H (T : Subgroup G) V)
    (hp : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hV : V ≤ twoCoreIn H) (hu : HasUniqueNoncentralChiefFactor H V) :
    ¬ intersectionClosure M₀ H ≤ centralizer (V : Set G) := by
  intro hc
  let I := ⁅conjugateSpan H V,(pResidual 2 H).map H.subtype⁆
  have hIH : I ≤ H := (residual_module_le_span d).trans
    ((span_le_right_core d hV).trans (twoCore_le H))
  have hJI : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (I : Set G) := by
    intro hj
    apply source_thompson_moves_residual_module d hV hu hc
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ hA => hA.1
    have hJR : elementaryAbelianMaxJ (T : Subgroup G) ≤ twoCoreIn M₀ := by
      rw [show twoCoreIn M₀ = M₀.pCoreIn 2 from rfl, h.core_eq_centralizer]
      exact le_inf hJT hJ
    have he := elementaryAbelianMaxJ_eq_of_intermediate_finite
      (T : Subgroup G) (twoCoreIn M₀) hJR (left_core_le_sylow d)
    exact he ▸ hj
  have hj : ¬ elementaryAbelianMaxJ
      ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) ≤
      centralizer (I.subgroupOf H : Set H) := by
    intro hj
    apply hJI
    have hjmap : (elementaryAbelianMaxJ
        ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      congr 1
      exact map_subgroupOf_eq_of_le h.right_mem.1.1.2
    rw [← hjmap]
    rintro g ⟨j,hjJ,rfl⟩ z hz
    exact congrArg H.subtype (hj hjJ ⟨z,hIH hz⟩ hz)
  have hRne : M₀.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact module_ne_bot hu (bot_unique (d.module_le_core.trans he.le))
  obtain ⟨N,hNR,hN,hn⟩ := h.common_normal_of_residual_sylow
    (source_common_normal_knownSimple hG T) hRne
    (residual_sylow_of_reduced_module h hG hp hJ (I.subgroupOf H)
      (source_residual_module_reduced d hV hu hc) hj)
  exact hN (d.no_common_normal N hNR (by
    simpa only [Chapter3.generated_eq_sup] using (Chapter3.normalIn_iff_le_normalizer.mp hn).2))

private theorem outsideCore_cubicRatio_le_two
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : ChapterD.QRCConfiguration M₀ H (T : Subgroup G) V) (hne : V ≠ ⊥)
    (hBV : H ⊓ M ≤ normalizer (V : Set G)) (hout : ¬ V ≤ H.pCoreIn 2) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 := by
  let := h.module_elementary
  let σ := imageRepresentation M₀ V h.module_normalized
  by_cases hff : IsFFModule σ
  · exact ((isFFModule_iff_cubicRatio_le_one σ).mp hff).trans (by norm_num)
  have hVT : V ≤ (T : Subgroup G) := d.module_le_core.trans (left_core_le_sylow d)
  have hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
    by_contra hj
    exact hff (internalActionImage_isFFModule_of_thompson_not_le T M₀ V h.sylow_le
      hVT h.module_normalized hj)
  let S := T.subtype h.right_mem.1.1.2
  let W := V.subgroupOf H
  have hVH : V ≤ H := hVT.trans h.right_mem.1.1.2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  let hp := source_intrinsic_minimalParabolic_of_notFF d hne hff S
    (map_subgroupOf_eq_of_le h.right_mem.1.1.2)
  have hWS : W ≤ (S : Subgroup H) := fun _ hx => hVT hx
  have hBN : ChapterB.minimalParabolicMax S hp ≤ normalizer (W : Set H) := by
    rw [h.intrinsic_maximal_eq_intersection hp,←subgroupOf_normalizer_eq hVH]
    exact fun _ hx => hBV hx
  have hTV : (S : Subgroup H) ≤ normalizer (W : Set H) :=
    (ChapterB.minimalParabolicMax_spec S hp).2.trans hBN
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hp).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W)
      (hWS.trans (ChapterB.minimalParabolicMax_spec S hp).2) hBN
  have hWout : ¬ W ≤ ChapterB.minimalParabolicCore S hp := by
    intro he
    have hc : W ≤ pCore 2 H := by
      rw [←ChapterB.minimalParabolic_sylow_inf_core S hp]
      exact le_inf hWS he
    apply hout
    have hm := map_mono (f := H.subtype) hc
    change (V.subgroupOf H).map H.subtype ≤ H.pCoreIn 2 at hm
    simpa only [map_subgroupOf_eq_of_le hVH] using hm
  have hfit : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp
        (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) h.right_mem.1.1))
  have hbound := ChapterE.Witnesses.source_normal_cubicRatio_lt_two
    (sqtk_of_mem_H hG h.right_mem.1.1.1) S hp W S hWS hWcore hWout hBN hfit le_rfl hTV
  let := ChapterE.DihedralCubic.centralizer_normal (S : Subgroup H) W hTV
  let ρ := ChapterE.DihedralCubic.canonicalAction (S : Subgroup H) W hTV
  let q := ChapterE.DihedralCubic.projection (S : Subgroup H) W hTV
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  let i : (S : Subgroup H) →* M₀ :=
    (H.subtype.comp (S : Subgroup H).subtype).codRestrict M₀ (fun s => h.sylow_le s.property)
  let f := (actionHom M₀ V h.module_normalized).rangeRestrict.comp i
  have hk : q.ker ≤ f.ker := by
    intro s hs
    have hsC : s ∈ (centralizer (W : Set H)).subgroupOf (S : Subgroup H) :=
      (QuotientGroup.eq_one_iff s).mp hs
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    have hc := congrArg H.subtype (hsC ⟨v,hVH v.property⟩ v.property)
    change (v : G) * (s.val : G) = (s.val : G) * (v : G) at hc
    change (s.val : G) * (v : G) * (s.val : G)⁻¹ = v
    rw [←hc,mul_inv_cancel_right]
  let ψ := q.liftOfSurjective hqs ⟨f,hk⟩
  have hψ (s : (S : Subgroup H)) : ψ (q s) = f s := q.liftOfRightInverse_comp_apply _ _ _ s
  let e := subgroupOfEquivOfLe hVH
  let E : Additive W ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  have he : ∀ a v, E (ρ a v) = σ (ψ a) (E v) := by
    intro a v
    obtain ⟨s,rfl⟩ := hqs a
    rw [hψ]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg H.subtype
      (ChapterE.DihedralCubic.representation_apply (S : Subgroup H) W hTV q hqs
        (QuotientGroup.ker_mk' _) s v)
  have hψi : Function.Injective ψ := by
    intro a b hab
    apply ChapterE.DihedralCubic.representation_injective (S : Subgroup H) W hTV q hqs
      (QuotientGroup.ker_mk' _)
    apply LinearMap.ext
    intro v
    apply E.injective
    change E (ρ a v) = E (ρ b v)
    exact (he a v).trans ((congrArg (fun z => σ z (E v)) hab).trans (he b v).symm)
  exact cubicRatio_le_nat_of_equivariant ρ σ ψ hψi E he 2 hbound.le

private theorem normalized_cubicRatio_le_two
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (d : QRCConfiguration M₀ H (T : Subgroup G) V) (hne : V ≠ ⊥)
    (hBV : H ⊓ M ≤ normalizer (V : Set G)) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 := by
  let := h.module_elementary
  let ρ := imageRepresentation M₀ V h.module_normalized
  by_cases hff : IsFFModule ρ
  · exact ((isFFModule_iff_cubicRatio_le_one ρ).mp hff).trans (by norm_num)
  by_cases hV : V ≤ twoCoreIn H
  · have hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
      by_contra hj
      exact hff (internalActionImage_isFFModule_of_thompson_not_le T M₀ V h.sylow_le
        h.module_le_sylow h.module_normalized hj)
    let S := T.subtype h.right_mem.1.1.2
    have hp := source_intrinsic_minimalParabolic_of_notFF d hne hff S
      (map_subgroupOf_eq_of_le h.right_mem.1.1.2)
    let := source_elementary_span_of_notFF d hV hff
    let U := (conjugateSpan H V).subgroupOf H
    obtain ⟨s⟩ := SeriesOn.exists_series U
    have hn := noncentralCount_ne_zero d hne hV s
    by_cases hc : s.noncentralCount = 1
    · have huf : HasUniqueNoncentralChiefFactor H V := ⟨s,hc⟩
      rcases source_dualFF_or_coreClosure_centralizes d hV huf with hd | hcentral
      · exact h.cubicRatio_le_two_of_dualFF hG hM hd
      · exact (not_uniqueFactor_coreClosure_centralizes h hG d hp hJ hV huf hcentral).elim
    · exact (cubicRatio_le_quadraticRatio ρ).trans
        (source_sqtk_multiple_ratio d hne hV (sqtk_of_mem_H hG h.right_mem.1.1.1) s (by omega))
  · exact outsideCore_cubicRatio_le_two h hG d hne hBV hV
end Numerical

/-- The source cubic bound holds on the literal reduced plus-torus action
when its join with H has zero two-core. -/
theorem Input.hermitian_plus_cubicRatio_le_two
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s] (hs : 1 < s)
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s))
    (hDA : D ≤ A) (hDc : Nat.card D = 2^s-1)
    (hz : (D ⊔ H).pCoreIn 2 = ⊥) :
    let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) D
    let hq := h.hermitian_plus_qrc_hypotheses hH c s hs hm hDA hDc
    letI := hq.module_elementary
    cubicRatio (imageRepresentation (D ⊔ (T : Subgroup G)) X hq.module_normalized) ≤ 2 := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let X := conjugateSpanBy Z D
  let hq := h.hermitian_plus_qrc_hypotheses hH c s hs hm hDA hDc
  let d := h.hermitian_plus_qrc_configuration hH c s hs hm hDA hDc hz
  have hg := h.hermitian_plus_span c s hm hDA hDc
  have hne : X ≠ ⊥ := by
    intro he
    have hh := hg.2.1
    change Nat.card X = 2^s at hh
    rw [he,Subgroup.card_bot] at hh
    have hp : 1 < (2:ℕ)^s := Nat.one_lt_pow (NeZero.ne s) (by decide)
    omega
  have hBV : H ⊓ normalizer (L : Set G) ≤ normalizer (X : Set G) := by
    rw [inf_comm,←c.sylow_sup_right h.sylow_normalizes hH.1.1.2]
    apply sup_le (le_sup_right.trans hq.module_normalized)
    have hspan := (h.hermitian_plus_span_reduced c s hm hDA hDc).1
    change B ≤ normalizer (conjugateSpanBy Z D : Set G)
    rw [hspan]
    exact normalizes_conjugateSpanBy Z A B
      ((c.right_le.trans inf_le_right).trans
        ((h.hermitian_omega_span_centralizes hH s hs hm).trans
          (Subgroup.centralizer_le_normalizer _))) c.right_normalizes_left
  exact normalized_cubicRatio_le_two hq h.qtke h.maximal d hne hBV

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
