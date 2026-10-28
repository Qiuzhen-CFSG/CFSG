module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEvenControl
public import Theory.GroupTheory.ConjugateOrbitSylowNormalizer

/-!
# Actual nonbinary even-row exclusion in the quintic component step

The literal quintic actor cannot normalize T∩K: the component-orbit Sylow
lemma would then normalize T∩K₀, contradicting the proved H-star argument.
Consequently its simple central carrier has no solvable Sylow control.
The actual rank-two Theorem C rows therefore reduce to the five literal
field-two endpoints. Tits remains among these alternatives.

Source: Aschbacher--Smith 6.1.4, printed p.665, using A.3.15(5)--(7).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
open Chapter1.Section02.LocalModels
open Chapter1.XiEmbedding.InvariantLarge
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original actor moves the original component Sylow, before any model
coordinates or quotient Sylow are chosen. -/
theorem original_hermitian_quintic_not_normalizes_component_sylow
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ quinticResidual T L ≤ normalizer ((((T : Subgroup G) ⊓ K) : Subgroup G) : Set G) := by
  intro hseed
  let X := quinticResidual T L
  have hTM : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  obtain ⟨D,_,_,_,_,_,hXT⟩ := original_hermitian_quintic_torus h hout hm
  have hXM : X ≤ M₁ := le_sup_left.trans (hXT.trans hCM₁)
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    sylow_normalizes_quinticResidual (h.rankOneInput hout).sylow_normalizes
  have hXK : X ≤ normalizer (K : Set G) :=
    original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK
  let P := (T : Subgroup G).subgroupOf M₁
  let F := X.subgroupOf M₁
  let B := K.subgroupOf M₁
  let e : K ≃* B := (subgroupOfEquivOfLe hK.1).symm
  let := hq
  have hqB : IsQuasisimple (B ⧸ pCore 2 B) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hPF : P ≤ normalizer (F : Set M₁) :=
    (comap_mono hTX).trans (X.le_normalizer_comap M₁.subtype)
  have hFB : F ≤ normalizer (B : Set M₁) :=
    (comap_mono hXK).trans (K.le_normalizer_comap M₁.subtype)
  have hFU : F ≤ normalizer ((P ⊓ B : Subgroup M₁) : Set M₁) :=
    (comap_mono hseed).trans (((T : Subgroup G) ⊓ K).le_normalizer_comap M₁.subtype)
  have hn := cComponent_normalizes_sylow_orbit hK.2 hqB (T.subtype hTM) hPF hFB hFU
  have hn' := (map_mono (f := M₁.subtype) hn).trans
    ((P ⊓ componentOrbit B P).le_normalizer_map M₁.subtype)
  rw [map_subgroupOf_eq_of_le hXM,Subgroup.map_inf _ _ _ M₁.subtype_injective,
    map_componentOrbit,map_subgroupOf_eq_of_le hK.1,map_subgroupOf_eq_of_le hTM] at hn'
  exact original_hermitian_quintic_not_normalizes_orbit_sylow h hout hm hM₁ hCM₁ hK hnot hn'

/-- Any actual simple carrier with solvable Sylow control is excluded from
the original outside component configuration. -/
theorem original_hermitian_component_no_solvable_sylow_control
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ SolvableSylowControl 2 (coreCentralQuotient K) := by
  intro hc
  exact original_hermitian_quintic_not_normalizes_component_sylow h hout hm hM₁ hCM₁ hK hnot hq
    (original_hermitian_quintic_normalizes_component_sylow_of_control h hout hm hM₁ hCM₁ hK hc)

/-- The nonbinary even rank-two rows are excluded; all five field-two
endpoints, explicitly including Tits, remain genuine alternatives. -/
theorem original_hermitian_rankTwo_component_small
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : RankTwoTheoremC (coreCentralQuotient K)) :
    A315Source.SmallRankTwoModel (coreCentralQuotient K) :=
  (rankTwo_sylow_control_or_small hc).resolve_left
    (original_hermitian_component_no_solvable_sylow_control h hout hm hM₁ hCM₁ hK hnot hq)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
