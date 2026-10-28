module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticTernarySubgroup
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEvenExclusion
public import Theory.GroupTheory.CoreCentralNormalizerAction.SylowLift

/-!
# The original inner ternary subgroup moves the supplied Sylow

Normalizing the literal projected component Sylow would stabilize it under
the whole original action. Sylow uniqueness through the central quotient,
then through the full original two-core, would normalize the original T∩K.
The original source movement theorem excludes this.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The whole inner image of the original quintic residual cannot normalize
the literal core-central image of the original component Sylow. -/
theorem original_hermitian_ternary_inner_not_normalizes_sylow
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hc : IsPSLSign (coreCentralQuotient K) unitary 3 p) :
    let C := coreCentralQuotient K
    let Y := (coreCentralActorImage K (quinticResidual T L)).comap
      (MulAut.conj : C →* MulAut C)
    ¬ Y ≤ normalizer (coreCentralIntersectionImage K (T : Subgroup G) : Set C) := by
  let C := coreCentralQuotient K
  let X := quinticResidual T L
  let Y := (coreCentralActorImage K X).comap (MulAut.conj : C →* MulAut C)
  have hy := (original_hermitian_quintic_ternary_subgroup
    h hout hm hM₁ hCM₁ hK hnot hq p hp ho unitary hc).1
  change ¬Y ≤ normalizer (coreCentralIntersectionImage K (T : Subgroup G) : Set C)
  intro hn
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) M₁ :=
    ⟨T.subtype hTM₁,map_subgroupOf_eq_of_le hTM₁⟩
  obtain ⟨U,hU⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hT hK.1 hK.2.subnormal
  have hUK : (U : Subgroup K) = (T : Subgroup G).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hU,subgroupOf_map_subtype]
  have hstab : coreCentralActorImage K X ≤
      MulAction.stabilizer (MulAut C) ((U : Subgroup K).map (coreCentralProjection K)) := by
    intro a ha
    obtain ⟨y,hyY,rfl⟩ := hy.symm ▸ ha
    change ((U : Subgroup K).map (coreCentralProjection K)).map
      (MulAut.conj y).toMonoidHom = (U : Subgroup K).map (coreCentralProjection K)
    rw [hUK]
    exact mem_normalizer_iff_map_conj_eq.mp (hn hyY)
  have hh := coreCentral_stabilizer_normalizes_sylow K X U
    (original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK) hstab
  rw [hU] at hh
  exact original_hermitian_quintic_not_normalizes_component_sylow
    h hout hm hM₁ hCM₁ hK hnot hq hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
