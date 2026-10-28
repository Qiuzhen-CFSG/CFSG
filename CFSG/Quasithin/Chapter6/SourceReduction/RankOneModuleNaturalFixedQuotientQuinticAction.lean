module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourShiftedOriginal
public import Theory.GroupTheory.ConjugateOrbitCoreAction

/-!
# The original quintic residual acts on the component quotient

If the quintic residual centralized K/O₂(K), it would centralize the
whole original T-orbit modulo O₂(M₁). That core lies in the actual Sylow.
The resulting normalization of the orbit Sylow contradicts the shifted
generation argument. Thus the original quotient action is nontrivial.

Source: Aschbacher--Smith 6.1.4, printed p.665.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The literal quintic actor has nontrivial action on the actual outside
component modulo its own two-core. -/
theorem original_hermitian_quintic_component_action_nontrivial
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M) :
    ¬ ⁅quinticResidual T L,K⁆ ≤ K.pCoreIn 2 := by
  intro hc
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
  have hcore : K.pCoreIn 2 ≤ M₁.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn K M₁ 2 hK.1 hK.2.subnormal
  have hc' : ⁅F,B⁆ ≤ pCore 2 M₁ := by
    apply (map_le_map_iff_of_injective (f := M₁.subtype) M₁.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hXM,map_subgroupOf_eq_of_le hK.1]
    exact hc.trans hcore
  have hPF : P ≤ normalizer (F : Set M₁) :=
    (comap_mono hTX).trans (X.le_normalizer_comap M₁.subtype)
  have hFB : F ≤ normalizer (B : Set M₁) :=
    (comap_mono hXK).trans (K.le_normalizer_comap M₁.subtype)
  have hFN : F ≤ normalizer (componentOrbit B P : Set M₁) := by
    apply (le_iInf fun t : P => ?_).trans (iInf_normalizer_le_normalizer_iSup _)
    exact normalizes_conjugate_of_normalizes (hPF t.property) hFB
  have hn := normalizes_orbit_intersection_of_commutator_le F B P (pCore 2 M₁)
    (pCore_isPGroup.le_sylow_of_normal (T.subtype hTM)) hPF hFN hc'
  have hn' := (map_mono (f := M₁.subtype) hn).trans
    ((P ⊓ componentOrbit B P).le_normalizer_map M₁.subtype)
  rw [map_subgroupOf_eq_of_le hXM,map_inf _ _ _ M₁.subtype_injective,
    map_componentOrbit,map_subgroupOf_eq_of_le hK.1,map_subgroupOf_eq_of_le hTM] at hn'
  exact original_hermitian_quintic_not_normalizes_orbit_sylow h hout hm hM₁ hCM₁ hK hnot hn'

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
