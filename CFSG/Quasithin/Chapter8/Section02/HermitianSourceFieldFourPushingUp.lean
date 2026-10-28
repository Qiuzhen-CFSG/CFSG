module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianConstrained
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Ranks
public import Theory.SpecificGroups.PSL3Four.ThreeRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.ModelSeparation
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import CFSG.Quasithin.ChapterC.Section04.A5FiniteNormality
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrainedAction
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.GeometricFlags
public import Theory.GroupTheory.SimpleSectionOrder

/-!
# Field-four Hermitian residuals in the pushing-up configuration

A C-component with central core quotient PSL₃(4) is normal: a nonnormal
component has centerless core quotient, while the actual PSL₃(4) carrier
has cubic rank two. This excludes the contained generalized-Fitting branch
of C.2.8 without assuming that the original central kernel is trivial.

For a constrained escaping component, the original perfect residual gives
a PSL₃(4) section in its inner action. Cubic rank and order eliminate every
C.2.7 star model except SL₅(2); carrier separation distinguishes PSL₃(4)
from the equally sized A₈. In the remaining model the source large-order
placement makes the literal radical intersection nontrivial. Its normalizer
preserves a proper subspace of the binary five-space. The parabolic's full
two-core quotient is too small or is PSL₄(2), so its soluble layers cannot
contain the original PSL₃(4) section. Thus every escaping component is ordinary.

The Chapter 12 FieldFourPushingUp consumer applies this result to the original
chosen-module residual and to each actual extraspecial Sylow center, retaining
all covering maps, kernels and the moved module. Exclusion of the ordinary
component and the residual-uniqueness branch is a separate remaining step.

Source: Aschbacher--Smith C.2.7--13, C.4.4, 4.4.3 and Remark 4.4.2,
printed pp.146--152,619, applied in 8.2.7, printed p.718,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource

private def fieldFourEquiv {E : Type*} [Field E] [Finite E] (hc : Nat.card E = 4) :
    E ≃+* Matrix.PSL3Four.F := by
  let : Fintype E := Fintype.ofFinite E
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hc,Matrix.PSL3Four.card_F])

private theorem field_four_projective_three_rank {E : Type*} [Field E] [Finite E]
    (hc : Nat.card E = 4) : 2 ≤ primeRank 3 PSL(3,E) := by
  rw [primeRank_congr 3 (Atlas.fieldEquivPSL 3 (fieldFourEquiv hc))]
  exact Matrix.PSL3Four.ThreeRank.three_rank_ge_two

/-- Cubic rank forces normality without discarding the original central kernel. -/
theorem field_four_cComponent_normal
    {H E : Type*} [Group H] [Finite H] [Field E] [Finite E]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hc : Nat.card E = 4)
    (K : Subgroup H) (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* PSL(3,E)) : K.Normal := by
  by_contra hn
  have hz := Chapter4.Section02.RankOneReciprocalEscape.coreQuotient_center_eq_bot_of_nonnormal
    hH hK hn
  let q : (K ⧸ pCore 2 K) ≃* (K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)
  have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_congr 3 (q.trans e)]
    exact field_four_projective_three_rank hc
  exact hn (hK.normal_of_centerless_core_threeRank hz hr
    (hH.stronglyQuasithin 3 (by decide) (by decide)))

/-- The original strict C.2.8 pair cannot contain the full generalized-Fitting preimage. -/
theorem field_four_pushingUp_fitting_escape {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) [IsQuasisimple (B ⧸ pCore 2 B)]
    (hc : Nat.card E = 4)
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E)) :
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H := by
  intro hf
  have hBH := h.component_le.trans h.local_le
  let A := B.subgroupOf H
  let N := M.subgroupOf H
  let eB : A ≃* B := subgroupOfEquivOfLe hBH
  let eqB : (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eqB.symm
  let ez : ((A ⧸ pCore 2 A) ⧸ center (A ⧸ pCore 2 A)) ≃* PSL(3,E) :=
    (QuotientGroup.congr _ _ eqB (FixedElementary.map_center eqB)).trans e
  have hN : M ≤ normalizer (B : Set G) := h.normalizes_of_fitting_contained hstrict hf
  have hs : conjugateSpanBy B M = B := h.span_eq_of_fitting_contained hstrict hf
  let : Group.IsPerfect B := hs ▸ h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := eB.symm.toMonoidHom) eB.symm.surjective
  have hNA : N ≤ normalizer (A : Set H) := by
    rw [←subgroupOf_normalizer_eq hBH]
    exact comap_mono hN
  have hAN : A ≤ N := comap_mono h.component_le
  have hQ : pCore 2 H ≤ N := by
    apply le_trans ?_ hf
    simpa only [QuotientGroup.ker_mk'] using
      MonoidHom.ker_le_comap (QuotientGroup.mk' (pCore 2 H)) (generalizedFitting (H ⧸ pCore 2 H))
  have hcore : A.pCoreIn 2 ≤ pCore 2 H :=
    (pCoreIn_mono_of_normalizes hAN hNA).trans (pCoreIn_le_of_generalizedFitting_preimage_le N hf)
  have hU : (⁅pCore 2 A,(⊤ : Subgroup A)⁆).map A.subtype ≤ pCore 2 H :=
    (map_mono (commutator_le_left _ _)).trans hcore
  have hA : A.IsCComponent :=
    isCComponent_of_contained_generalizedFitting A N hAN hNA hQ hU hf
  let : A.Normal := field_four_cComponent_normal h.sqtk hc A hA ez
  have hHN : H ≤ normalizer (B : Set G) := by
    have hh := A.le_normalizer_map H.subtype
    simpa only [A,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hBH] using hh
  have hHM : H ≤ M := by
    rw [← h.normalizer_span_eq, hs]
    exact le_inf le_rfl hHN
  exact hstrict.not_ge hHM


open Chapter7.NormalizedSource.NonMathieuHermitian
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem field_four_card {E : Type*} [Field E] [Finite E]
    (hc : Nat.card E = 4) : Nat.card PSL(3,E) = 20160 := by
  rw [Matrix.PSL3.LinearThree.card_projective,hc]
  norm_num

private theorem field_four_quotient_three_rank
    {X E : Type*} [Group X] [Finite X] [Field E] [Finite E]
    (hc : Nat.card E = 4) (f : X →* PSL(3,E)) (hf : Function.Surjective f) :
    2 ≤ primeRank 3 X := by
  have hr := field_four_projective_three_rank hc
  by_contra! hb
  let P : Sylow 3 X := Classical.choice inferInstance
  have hu := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)) f hf
  omega

variable {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
variable {H M B R W : Subgroup G}

private theorem constrained_inner_injection
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ∃ f : coreCentralActorImage K ((conjugateSpanBy B M).subgroupOf H) →*
      coreCentralQuotient K, Function.Injective f := by
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let X := conjugateSpanBy B M
  let A := X.subgroupOf H
  let C := coreCentralActorImage K A
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let : Group.IsPerfect C := coreCentralActorImage_perfect K A
    (h.constrained_span_normalizes_intrinsic K hK hq)
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  obtain ⟨f,hf,_⟩ := MulAut.perfect_subgroup_exists_inner_lift C hz
  exact ⟨f,hf⟩

private theorem field_four_constrained_action_three_rank
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal) [IsQuasisimple (B ⧸ pCore 2 B)]
    (hc : Nat.card E = 4)
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) :
    2 ≤ primeRank 3 (coreCentralActorImage K ((conjugateSpanBy B M).subgroupOf H)) := by
  obtain ⟨g,hg⟩ := constrained_hermitian_action_quotient h hN e K hK hq hout
  exact field_four_quotient_three_rank hc g hg

private theorem field_four_constrained_core_card_ge
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal) [IsQuasisimple (B ⧸ pCore 2 B)]
    (hc : Nat.card E = 4)
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) : 20160 ≤ Nat.card (coreCentralQuotient K) := by
  obtain ⟨g,hg⟩ := constrained_hermitian_action_quotient h hN e K hK hq hout
  obtain ⟨f,hf⟩ := constrained_inner_injection h K hK hq
  rw [←field_four_card hc]
  exact (Nat.card_le_card_of_surjective g hg).trans (Nat.card_le_card_of_injective f hf)

private theorem field_four_constrained_small_core
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal) [IsQuasisimple (B ⧸ pCore 2 B)]
    (hc : Nat.card E = 4)
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hsize : Nat.card (coreCentralQuotient K) ≤ 20160) :
    Nonempty (coreCentralQuotient K ≃* PSL(3,E)) := by
  obtain ⟨g,hg⟩ := constrained_hermitian_action_quotient h hN e K hK hq hout
  obtain ⟨f,hf⟩ := constrained_inner_injection h K hK hq
  have h1 := Nat.card_le_card_of_surjective g hg
  have h2 := Nat.card_le_card_of_injective f hf
  have hc' := field_four_card hc
  have hfg : Nat.card (coreCentralActorImage K ((conjugateSpanBy B M).subgroupOf H)) =
      Nat.card PSL(3,E) := by omega
  have hff : Nat.card (coreCentralActorImage K ((conjugateSpanBy B M).subgroupOf H)) =
      Nat.card (coreCentralQuotient K) := by omega
  exact ⟨(MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf,hff⟩)).symm.trans (MulEquiv.ofBijective g
      ((Nat.bijective_iff_surjective_and_card g).mpr ⟨hg,hfg⟩))⟩

private theorem card_linear_three_two {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) : Nat.card SL(3,F) = 168 := by
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  norm_num [hF,Fin.prod_univ_succ] at hc
  rw [card_eq_card_quotient_mul_card_subgroup (center SL(3,F)),
    Atlas.ExceptionalSupport.card_sl_center]
  change Nat.card PSL(3,F) * Nat.gcd 3 (Nat.card F - 1) = 168
  norm_num [hF,hc]

private theorem field_four_constrained_linear_five
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal) [IsQuasisimple (B ⧸ pCore 2 B)]
    (hc : Nat.card E = 4)
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) :
    K.Normal ∧ Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) := by
  have hm := ChapterC.C27Source.star_model_from_source
    (h.constrained_source_input K hK hq hout hfK)
  have hcard := field_four_constrained_core_card_ge h hN hc e K hK hq hout
  have hsmall (hsize : Nat.card (starImage (K.map H.subtype) R (K.map H.subtype)) <
      20160) : False := by
    have hle : Nat.card (coreCentralQuotient K) ≤
        Nat.card (starImage (K.map H.subtype) R (K.map H.subtype)) := by
      rw [Nat.card_congr (h.constrained_star_central_equiv K hK hq hout hfK).toEquiv]
      exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    omega
  have hr := field_four_constrained_action_three_rank h hN hc e K hK hq hout
  have ho : Odd 3 := by decide
  have hnK : K.Normal := h.constrained_component_normal_of_central_threeRank K hK hq hout hfK
    (hr.trans (h.constrained_span_action_rank_le_central_quotient K hK hq 3))
  refine ⟨hnK,?_⟩
  cases hm with
  | linearTwo F es =>
    exact (h.no_constrained_component_star_linear_two K hK hq hout hfK F es).elim
  | linearThree F es =>
    by_cases hlarge : 1 < F.degree
    · have hF : 4 ≤ Nat.card F.Carrier := by
        rw [F.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
      have hu := linear_three_span_odd_rank h K hK hq hout hfK es hF ho
      omega
    · have hd : F.degree = 1 := by have := F.degree_pos; omega
      exfalso
      apply hsmall
      rw [Nat.card_congr es.toEquiv,card_linear_three_two (by rw [F.card_eq,hd,pow_one])]
      decide
  | symplectic F hlarge es =>
    have hF : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
    have hu := h.constrained_symplectic_span_rank_le_one K hK hq hout hfK es hF ho
    omega
  | g2 F hlarge es =>
    have hF : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
    have hu := h.constrained_g2_span_rank_le_one K hK hq hout hfK es hF ho
    omega
  | g2DerivedTwo es =>
    exfalso
    apply hsmall
    rw [Nat.card_congr es.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
    decide
  | alternating m hm es =>
    rcases hm with rfl | rfl | rfl | rfl
    all_goals try { exfalso; apply hsmall; rw [Nat.card_congr es.toEquiv,nat_card_alternatingGroup]; norm_num }
    let ec := (coreCentralQuotientCongr
      (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
        (ChapterC.Section04Constrained.source_simple_equiv
          (h.constrained_source_input K hK hq hout hfK) es
          (alternatingGroup.center_eq_bot (by simp)))
    have hcQ : Nat.card (coreCentralQuotient K) ≤ 20160 := by
      rw [Nat.card_congr ec.toEquiv,nat_card_alternatingGroup]
      norm_num
    obtain ⟨a⟩ := field_four_constrained_small_core h hN hc e K hK hq hout hcQ
    have ha : ChapterA.Section03.SourceEmbeddings.Exceptional.IsModel (coreCentralQuotient K) :=
      Or.inr (Or.inr ⟨a.trans (Atlas.fieldEquivPSL 3 (fieldFourEquiv hc))⟩)
    exact (ha.not_binaryFour ⟨ZMod 2,inferInstance,inferInstance,by simp,
      ⟨ec.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩).elim
  | linearFiveTwo es => exact ⟨es⟩
  | tripleSix ez es =>
    rw [Nat.card_congr (h.constrained_star_central_equiv K hK hq hout hfK).toEquiv,
      Nat.card_congr es.toEquiv,nat_card_alternatingGroup] at hcard
    norm_num at hcard

private theorem field_four_pushingUp_components
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hN : (B.subgroupOf M).Normal) [IsQuasisimple (B ⧸ pCore 2 B)]
    (hc : Nat.card E = 4)
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E)) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧ K.Normal ∧
      ¬ K ≤ M.subgroupOf H ∧
      ((IsComponent H K ∧ B.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K) ∨
        (generalizedFitting K = pCore 2 K ∧
          Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)))) := by
  obtain ⟨K,hK,hq,hout,hnorm,hcases⟩ := h.ordinary_or_constrained_escape
    (field_four_pushingUp_fitting_escape h hstrict hc e)
  rcases hcases with ho | hfK
  · exact ⟨K,hK,hq,h.ordinary_component_normal K ho,hout,Or.inl ⟨ho,
      h.ordinary_component_contains_original K ho,
      (h.ordinary_module_placement K ho).1.trans inf_le_right⟩⟩
  · obtain ⟨hn,hm⟩ := field_four_constrained_linear_five h hN hc e K hK hq hout hfK
    exact ⟨K,hK,hq,hn,hout,Or.inr ⟨hfK,hm⟩⟩


open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.MaximalOvergroups

private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

private theorem field_four_no_binary_four_section
    (hc : Nat.card E = 4) (U : Subgroup PSL(4,ZMod 2))
    (f : U →* PSL(3,E)) (hf : Function.Surjective f) : False := by
  have h4 : Nat.card PSL(4,ZMod 2) = 20160 := by
    rw [←Nat.card_congr Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.toEquiv,
      nat_card_alternatingGroup]
    norm_num
  have h3 := field_four_card hc
  have hu := Nat.card_le_card_of_surjective f hf
  have hi := Nat.card_le_card_of_injective U.subtype U.subtype_injective
  have he : Nat.card U = Nat.card PSL(4,ZMod 2) := by omega
  let a := MulEquiv.ofBijective U.subtype
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨U.subtype_injective,he⟩)
  let b := MulEquiv.ofBijective f
    ((Nat.bijective_iff_surjective_and_card _).mpr ⟨hf,by omega⟩)
  have hm : ChapterA.Section03.SourceEmbeddings.Exceptional.IsModel PSL(4,ZMod 2) :=
    Or.inr (Or.inr ⟨a.symm.trans (b.trans (Atlas.fieldEquivPSL 3 (fieldFourEquiv hc)))⟩)
  exact hm.not_binaryFour ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨MulEquiv.refl _⟩⟩

/-- A marked PSL₃(4) section cannot survive in a binary five-space two-local.
The representation retains its entire soluble kernel. -/
theorem field_four_no_binary_five_local {A : Type*} [Group A]
    (hc : Nat.card E = 4) (π : A →* PSL(3,E)) (hπ : Function.Surjective π)
    (Q : Subgroup (LinearGroup 5)) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (r : A →* LinearGroup 5) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (Q : Set (LinearGroup 5))) : False := by
  let : IsSimpleGroup PSL(3,E) := Atlas.psl_simple_high_rank 3 (by decide)
  have hS : ¬ Group.IsSolvable PSL(3,E) :=
    Group.IsPerfect.not_isSolvable _
  let W := fixedSpace Q
  have hW : W ≠ ⊥ := fixedSpace_ne_bot
    (by norm_num [Space,Nat.card_fun,Nat.card_fin,Nat.card_zmod]) hQ
  have hWt : W ≠ ⊤ := fixedSpace_ne_top hne
  have hpos : 0 < Module.finrank (ZMod 2) W :=
    Nat.pos_of_ne_zero (fun hz => hW (Submodule.finrank_eq_zero.mp hz))
  have hlt : Module.finrank (ZMod 2) W < 5 := by
    simpa only [Space,Module.finrank_fin_fun] using Submodule.finrank_lt hWt
  let i : Fin 4 := ⟨Module.finrank (ZMod 2) W - 1,by omega⟩
  obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace W i (by dsimp only [i]; omega)
  let P := flagStabilizer b {i}
  have hP : r.range ≤ P := by
    rw [show P = flagStabilizer b {i} from rfl,flagStabilizer_singleton,hb]
    exact hr.trans (normalizer_le_parabolic_fixedSpace Q)
  let j : A →* P := r.codRestrict P (fun x => hP ⟨x,rfl⟩)
  let : Group.IsSolvable j.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show j.ker ≤ r.ker from fun _ hx => congrArg Subtype.val hx))
    (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 P)
  let : Group.IsNilpotent (pCore 2 P) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let a := q.comp j
  let : Group.IsSolvable a.ker := isSolvable_comap_of_solvable_ker j q.ker
  let m : Group.SolvableKernelModel A a.range :=
    ⟨a.ker,inferInstance,inferInstance,QuotientGroup.quotientKerEquivRange a⟩
  obtain ⟨U,g,hg⟩ := m.simple_section hS ⊤
    (π.comp (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom)
    (hπ.comp topEquiv.surjective)
  rcases singleton_quotient_models b i with hsmall | hfour
  · obtain ⟨e⟩ := hsmall
    have hd := SimpleSection.card_dvd_of_solvable_representation hS π hπ a
    rw [field_four_card hc,Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_perm,
      Nat.card_fin] at hd
    have hc3 := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 3
    norm_num only [Nat.card_zmod,Fin.prod_univ_succ,Fin.val_zero,Fin.val_succ,
      Fin.prod_univ_zero,mul_one] at hc3
    rw [hc3] at hd
    norm_num at hd
  · obtain ⟨e⟩ := hfour
    let t := e.toMonoidHom.comp (a.range.subtype.comp U.subtype)
    have ht : Function.Injective t := e.injective.comp
      (a.range.subtype_injective.comp U.subtype_injective)
    let z := MonoidHom.ofInjective ht
    exact field_four_no_binary_four_section hc t.range
      (g.comp z.symm.toMonoidHom) (hg.comp z.symm.surjective)

private theorem field_four_constrained_intersection
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) :
    coreCentralIntersectionImage K (R.subgroupOf H) ≠ ⊥ := by
  let hs := h.constrained_source_input K hK hq hout hfK
  let K' := K.map H.subtype
  let : (K'.subgroupOf (K' ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K'.le_normalizer hs.normalizes)
  have hz : center SL(5,ZMod 2) = ⊥ := binary_center_eq_bot (by decide)
  have hlarge : 40320 < Nat.card (starImage K' R K') := by
    rw [Nat.card_congr e.toEquiv]
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    norm_num only [Nat.card_zmod,Fin.prod_univ_succ,Fin.val_zero,Fin.val_succ,
      Fin.prod_univ_zero,mul_one] at hc
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hz).toEquiv,
      Nat.card_congr (QuotientGroup.quotientBot : (SL(5,ZMod 2) ⧸ ⊥) ≃* SL(5,ZMod 2)).toEquiv] at hc
    omega
  have hn := (ChapterC.C27Source.star_intersection_placement_from_source_of_large_order hs hlarge).1.1
  rw [←ChapterC.C27Source.component_intersection_star_eq_of_normal_input
    (ChapterC.C27Source.source_join_input hs)] at hn
  have hne : coreCentralIntersectionImage K' R ≠ ⊥ := by
    intro hb
    have hm := ChapterC.Section04Constrained.source_simple_equiv_map_intersection hs e hz
    rw [hb,Subgroup.map_bot] at hm
    exact hn ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hm.symm)
  let eK := K.equivMapOfInjective H.subtype H.subtype_injective
  let ec := coreCentralQuotientCongr eK
  have he : (coreCentralIntersectionImage K (R.subgroupOf H)).map ec.toMonoidHom =
      coreCentralIntersectionImage K' R := by
    ext x
    constructor
    · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
      exact ⟨eK k,hk,(coreCentralQuotientCongr_apply eK k).symm⟩
    · rintro ⟨k,hk,rfl⟩
      refine ⟨coreCentralProjection K (eK.symm k),⟨eK.symm k,?_,rfl⟩,?_⟩
      · change ((eK.symm k : K) : H).val ∈ R
        have hh := congrArg (fun a : K' => (a : G)) (eK.apply_symm_apply k)
        change ((eK.symm k : K) : H).val = (k : G) at hh
        rwa [hh]
      · change coreCentralQuotientCongr eK (coreCentralProjection K (eK.symm k)) = _
        rw [coreCentralQuotientCongr_apply,eK.apply_symm_apply]
  intro hb
  exact hne (by rw [←he,hb,Subgroup.map_bot])

/-- The last constrained field-four row is excluded by its actual radical normalizer. -/
theorem field_four_no_constrained_component
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal) [IsQuasisimple (B ⧸ pCore 2 B)]
    (hc : Nat.card E = 4)
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) : False := by
  obtain ⟨_,⟨es⟩⟩ := field_four_constrained_linear_five h hN hc e K hK hq hout hfK
  have hn := (normal_subgroupOf_iff_le_normalizer h.component_le).mp hN
  obtain ⟨r,hker,hr⟩ := Chapter4.Section04.NormalizedRankOneOddControl.constrained_normalized_inner_representation
    h hn K hK hq hout
  let := hker
  let c := ((coreCentralQuotientCongr (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
    (ChapterC.Section04Constrained.source_simple_equiv
      (h.constrained_source_input K hK hq hout hfK) es (binary_center_eq_bot (by decide)))).trans
        (slEquivLinear 5)
  let π := e.toMonoidHom.comp ((QuotientGroup.mk' (center (B ⧸ pCore 2 B))).comp
    (QuotientGroup.mk' (pCore 2 B)))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  let U := coreCentralIntersectionImage K (R.subgroupOf H)
  let Q := U.map c.toMonoidHom
  have hQ : IsPGroup 2 Q := (coreCentralIntersectionImage_isPGroup K _ h.isRadical.isPGroup).map _
  have hne : Q ≠ ⊥ := fun hb => field_four_constrained_intersection h K hK hq hout hfK es
    ((U.map_eq_bot_iff_of_injective c.injective).mp hb)
  let f := c.toMonoidHom.comp r
  let : Group.IsSolvable f.ker := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ c.injective]
    exact hker
  apply field_four_no_binary_five_local hc π hπ Q hQ hne f
  change (c.toMonoidHom.comp r).range ≤ _
  rw [MonoidHom.range_comp]
  exact (map_mono hr).trans (U.le_normalizer_map c.toMonoidHom)

/-- Only an ordinary component can escape the original local subgroup at field four. -/
theorem field_four_pushingUp_ordinary
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hN : (B.subgroupOf M).Normal) [IsQuasisimple (B ⧸ pCore 2 B)]
    (hc : Nat.card E = 4)
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E)) :
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ M.subgroupOf H ∧ B.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K := by
  obtain ⟨K,hK,hq,hn,hout,ho | ⟨hfK,_⟩⟩ := field_four_pushingUp_components h hstrict hN hc e
  · exact ⟨K,ho.1,hn,hout,ho.2⟩
  · exact (field_four_no_constrained_component h hN hc e K hK hq hout hfK).elim

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
