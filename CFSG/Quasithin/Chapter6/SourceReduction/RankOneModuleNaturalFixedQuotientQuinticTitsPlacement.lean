module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticTitsSubgroup
public import Theory.GroupTheory.CoreCentralNormalizerAction.QuinticInverterLift
public import Theory.GroupTheory.PResidual.InverterPlacement
public import Theory.SpecificGroups.Tits.QuinticSylowInverter

/-!
# The original quintic residual lies inside its Tits component

The actual projected component Sylow supplies an inverter modulo the whole
inner two-core. It lifts to the original component Sylow. The equal quotient
indices five recover the entire original residual two-core, and its
two-perfectness then forces containment in the original component.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original component Sylow contains an inverter of the whole
original quintic residual modulo its actual two-core. -/
theorem original_hermitian_quintic_tits_sylow_inverter
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    ∃ k : K, (k:G) ∈ T ∧
      ∀ x ∈ quinticResidual T L, (k:G)*x*(k:G)⁻¹*x ∈ (quinticResidual T L).pCoreIn 2 := by
  let := hq
  let C := coreCentralQuotient K
  let X := quinticResidual T L
  let Y := (coreCentralActorImage K X).comap (MulAut.conj : C →* MulAut C)
  obtain ⟨hy,_,_,hYfive,S,hS,hSY,_⟩ :=
    original_hermitian_quintic_tits_subgroup h hout hm hM₁ hCM₁ hK hnot hq e
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) M₁ :=
    ⟨T.subtype hTM₁,map_subgroupOf_eq_of_le hTM₁⟩
  obtain ⟨U,hU⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hT hK.1 hK.2.subnormal
  have hUK : (U : Subgroup K) = (T : Subgroup G).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hU,subgroupOf_map_subtype]
  have hUX : (U : Subgroup K).map K.subtype ≤ normalizer (X : Set G) := by
    rw [hU]
    exact inf_le_left.trans (sylow_normalizes_quinticResidual (h.rankOneInput hout).sylow_normalizes)
  have hXN : X ≤ normalizer (K : Set G) :=
    original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK
  have hz : center C = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot (K ⧸ pCore 2 K)
  have hinner : coreCentralActorImage K X ≤ MulAut.innerSubgroup C := by
    rw [←hy]
    exact (show Y.map (MulAut.conj : C →* MulAut C) ≤
      (MulAut.conj : C →* MulAut C).range from map_le_range _ _)
  obtain ⟨u,hu,hinv⟩ := Tits.quintic_sylow_inverter e S Y hSY hYfive
  have huU : u ∈ (U : Subgroup K).map (coreCentralProjection K) := by
    change u ∈ (S : Subgroup C) at hu
    rwa [hS,coreCentralIntersectionImage,←hUK] at hu
  obtain ⟨k,hk,hkinv⟩ := coreCentral_quintic_sylow_inverter_lift K X U hUX hXN hz hinner
    (original_hermitian_quintic_core_quotient h hout hm).2 hYfive ⟨u,huU,hinv⟩
  refine ⟨k,?_,hkinv⟩
  have hh := mem_map_of_mem K.subtype hk
  rw [hU] at hh
  exact hh.1

/-- The whole original two-perfect quintic residual lies in the original
Tits component before either original quotient is taken. -/
theorem original_hermitian_quintic_le_tits_component
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    quinticResidual T L ≤ K := by
  obtain ⟨k,_,hkinv⟩ := original_hermitian_quintic_tits_sylow_inverter
    h hout hm hM₁ hCM₁ hK hnot hq e
  exact le_of_normalized_inverter (quinticResidual T L) K
    (quinticResidual_twoPerfect T L)
    (original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK)
    k k.property hkinv

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
