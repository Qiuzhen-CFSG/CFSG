module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticTernaryCentralizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticTernaryBlock
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticTernaryMovement
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticOddSubgroupOverlap
public import Theory.GroupTheory.CoreCentralNormalizerAction.SL2BlockLift
public import Theory.GroupTheory.CoreCentralNormalizerAction.BlockAction
public import Theory.GroupTheory.DerivedInvolutionCentralizer
public import Theory.GroupTheory.CComponent.CoreCentralNormalizer
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.SpecificGroups.PSL2.CoreBlockQuinticPlacement

/-!
# Excluding the original odd ternary component

The original quintic action fixes a central involution of its supplied
component Sylow. The characteristic SL₂ block of that centralizer lifts
through the full central kernel and the full original two-core. An inverter
in its supplied Sylow puts the whole original residual in this block;
the alternative centralizes the component Sylow and contradicts movement.
The original Sylow then normalizes the selected block, so the proved
rank-one fusion terminal excludes it.

Source: Aschbacher--Smith6.1.4, odd ternary case, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups Pointwise
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric Chapter1.Section02.LocalModels

private theorem sylow_inside_supplied
    {G : Type*} [Group G] [Finite G] (K J : Subgroup G) (hJK : J ≤ K)
    (U : Sylow 2 K)
    (hUJ : (U : Subgroup K).map K.subtype ≤ normalizer (J : Set G)) :
    ∃ P : Sylow 2 J, (P : Subgroup J).map J.subtype ≤ (U : Subgroup K).map K.subtype := by
  let A := J.subgroupOf K
  have hUA : (U : Subgroup K) ≤ normalizer (A : Set K) := by
    intro u hu
    apply J.le_normalizer_comap K.subtype
    exact hUJ (mem_map_of_mem K.subtype hu)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow U A hUA
  let e := subgroupOfEquivOfLe hJK
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Q,?_⟩
  rintro x ⟨j,⟨a,ha,rfl⟩,rfl⟩
  rw [hP] at ha
  exact mem_map_of_mem K.subtype ha

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- Neither odd-prime ternary row can occur for the actual original
outside component and the original whole Hermitian residual. -/
theorem original_hermitian_component_not_odd_ternary
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (unitary : Bool) :
    ¬ IsPSLSign (coreCentralQuotient K) unitary 3 p := by
  intro hc
  let : Fact p.Prime := ⟨hp⟩
  let := hq
  let C := coreCentralQuotient K
  let X := quinticResidual T L
  let Y := (coreCentralActorImage K X).comap (MulAut.conj : C →* MulAut C)
  obtain ⟨hY,_,_,_,S,z,hS,_,hz,_,_,hYC,hfix⟩ :=
    original_hermitian_quintic_ternary_centralizer
      h hout hm hM₁ hCM₁ hK hnot hq p hp ho unitary hc
  let H := centralizer ({(z : C)} : Set C)
  let B := (commutator H).map H.subtype
  have hzC : orderOf (z : C) = 2 := by
    simpa only [Subgroup.orderOf_coe] using hz
  obtain ⟨⟨e⟩,hcent⟩ := original_hermitian_quintic_ternary_involution_block
    h hout hm hM₁ hCM₁ hK hnot hq p hp ho unitary hc z hzC
  let eb : commutator H ≃* B :=
    (commutator H).equivMapOfInjective H.subtype H.subtype_injective
  let eB : B ≃* SL(2,ZMod p) := eb.symm.trans e
  have hlarge := (original_hermitian_quintic_odd_three_card_and_prime
    h hout hm hM₁ hCM₁ hK hnot hq p hp ho unitary hc).2
  let : Fact (3 < Nat.card (ZMod p)) := ⟨by simpa using hlarge⟩
  let : IsQuasisimple B := Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
    (by simpa using hlarge) eB
  have h9 : Nat.card (ZMod p) ≠ 9 := by
    simp only [Nat.card_zmod]
    intro he
    rw [he] at hp
    norm_num at hp
  let q := QuotientGroup.mk' (pCore 2 K)
  let c := QuotientGroup.mk' (center (K ⧸ pCore 2 K))
  let R := (commutator (B.comap c)).map (B.comap c).subtype
  let J := (R.comap q).map K.subtype
  obtain ⟨hJK,_,heJ,hJB⟩ := coreCentral_sl2_block_lift K B eB
    (by simpa using ho) h9
  have hXN : X ≤ normalizer (K : Set G) :=
    original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK
  have hblock : coreCentralActorImage K (X ⊔ (T : Subgroup G)) ≤
      MulAction.stabilizer (MulAut C) B := by
    intro a ha
    exact derived_centralizer_map_eq_of_fixed a (z : C) (hfix a ha)
  have hNJ : (X ⊔ (T : Subgroup G)) ⊓ normalizer (K : Set G) ≤ normalizer (J : Set G) :=
    coreCentral_derived_block_lift_normalized K (X ⊔ (T : Subgroup G)) B hblock
  have hXJnorm : X ≤ normalizer (J : Set G) := (le_inf le_sup_left hXN).trans hNJ
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    sylow_normalizes_quinticResidual (h.rankOneInput hout).sylow_normalizes
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) M₁ :=
    ⟨T.subtype hTM₁,map_subgroupOf_eq_of_le hTM₁⟩
  obtain ⟨U,hU⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hT hK.1 hK.2.subnormal
  have hUT : (U : Subgroup K).map K.subtype ≤ T := by rw [hU]; exact inf_le_left
  have hUJ : (U : Subgroup K).map K.subtype ≤ normalizer (J : Set G) :=
    (le_inf (hUT.trans le_sup_right) ((map_subtype_le _).trans K.le_normalizer)).trans hNJ
  obtain ⟨P,hPU⟩ := sylow_inside_supplied K J hJK U hUJ
  have hXJ : X ≤ J := by
    rcases Theory.PSL2.quintic_le_or_trivial_twoCore_action J X P
      (hPU.trans (hUT.trans hTX)) hXJnorm (quinticResidual_twoPerfect T L)
      (original_hermitian_quintic_core_quotient h hout hm).2
      hp ho (by decide : 0 < 1) (by decide : 1 ≤ 2)
      (by simp) (by simpa using hlarge) (Or.inr heJ) with hle | htrivial
    · exact hle
    · have hYB : Y ≤ centralizer (B : Set C) := by
        intro y hy b hb
        have hyim : MulAut.conj y ∈ coreCentralActorImage K X := hy
        obtain ⟨x,hx,hxy⟩ := hyim
        have hh := coreCentral_block_fixed_of_trivial_twoCore_action K J hJK B hJB
          x x.property (hXJnorm hx) (htrivial ⟨x,hXJnorm hx⟩ hx) b hb
        rw [hxy] at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      have hYN : Y ≤ normalizer (S : Set C) := by
        apply le_trans _ (centralizer_le_normalizer (S : Set C))
        intro y hy s hs
        have hyH : y ∈ H := hYC ((show Y ≤ Y ⊔ (S : Subgroup C) from le_sup_left) hy)
        have hyZ : (⟨y,hyH⟩ : H) ∈ center H := by
          rw [←hcent]
          intro b hb
          apply Subtype.ext
          exact hYB hy b (mem_map_of_mem H.subtype hb)
        have hsH : s ∈ H := hYC ((show (S : Subgroup C) ≤ Y ⊔ (S : Subgroup C) from le_sup_right) hs)
        exact congrArg Subtype.val (mem_center_iff.mp hyZ (⟨s,hsH⟩ : H))
      exact (original_hermitian_ternary_inner_not_normalizes_sylow
        h hout hm hM₁ hCM₁ hK hnot hq p hp ho unitary hc
        (by
          change Y ≤ normalizer (coreCentralIntersectionImage K (T : Subgroup G) : Set C)
          rw [←hS]
          exact hYN)).elim
  have hXK : X ≤ K := hXJ.trans hJK
  obtain ⟨D,hD,_,hDX,_,_,_⟩ := original_hermitian_quintic_torus h hout hm
  have himage := original_hermitian_quintic_central_image_card
    h hout hm hM₁ hCM₁ hK hnot hq D hD hDX
  have hne : coreCentralActorImage K X ≠ ⊥ := by
    intro he
    have hle : coreCentralActorImage K D ≤ coreCentralActorImage K X :=
      map_mono (subgroupOf_mono (normalizer (K : Set G)) hDX)
    have hb : coreCentralActorImage K D = ⊥ := bot_unique (he ▸ hle)
    rw [hb,card_bot] at himage
    omega
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (le_inf hTM₁ hTX).trans
      (normalizer_inf_le_of_coreCentral_image_ne_bot M₁ K X hK.1 hK.2 hXK hne)
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (le_inf le_sup_right hTK).trans hNJ
  exact original_hermitian_no_odd_linear_comparison_subgroup h hout hm hM₁ hCM₁
    (hJK.trans hK.1) hXJ hTJ p 1 hp ho (Or.inl rfl) (by simpa using hlarge)
    ⟨ZMod p,inferInstance,inferInstance,by simp,heJ⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
