module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticOddNormalizer
public import Theory.GroupTheory.CoreCentralNormalizerAction.PSL2FieldBounds
public import Theory.SpecificGroups.PSL2.OddCoverCoreFree

/-!
# The actual odd linear-two component quotient

The same full component Sylow and original quintic actor exclude fields
of order three and nine on the central quotient. The ordinary odd PSL₂
cover kernel therefore has order dividing two. Since K/O₂(K) has trivial
two-core, its center vanishes: the marked model is the actual K/O₂(K).

Source: Aschbacher--Smith 6.1.4 and I.1.3--4, pp.666 and407--408.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original component quotient is centerless and has the actual odd
PSL₂ model; the field-nine cover is excluded by the original Sylow marking. -/
theorem original_hermitian_quintic_odd_linear_actual_quotient
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p d : ℕ) (hp : p.Prime) (ho : Odd p) (hd : d = 1 ∨ d = 2)
    (hc : ClassicalGroup.IsPSL (coreCentralQuotient K) 2 (p^d)) :
    center (K ⧸ pCore 2 K) = ⊥ ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p^d) ∧ 3 < p^d ∧ p^d ≠ 9 := by
  let := hq
  let X := quinticResidual T L
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) M₁ :=
    ⟨T.subtype hTM₁,map_subgroupOf_eq_of_le hTM₁⟩
  obtain ⟨U,hU⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hT hK.1 hK.2.subnormal
  have hUX : (U : Subgroup K).map K.subtype ≤ normalizer (X : Set G) := by
    rw [hU]
    exact inf_le_left.trans (sylow_normalizes_quinticResidual (h.rankOneInput hout).sylow_normalizes)
  have hinner := original_hermitian_quintic_odd_linear_inner
    h hout hm hM₁ hCM₁ hK p d hp ho (by omega) hc
  have hfive := original_hermitian_quintic_odd_linear_image_card
    h hout hm hM₁ hCM₁ hK hnot hq p d hp ho hd hc
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hc
  have hb := coreCentral_odd_quintic_field_bounds K X U hUX hinner hfive
    ⟨p,d,hp,ho,by omega,hF⟩ e
  let : Fact (3 < Nat.card F) := ⟨hb.1⟩
  have hodd : Odd (Nat.card F) := by rw [hF]; exact ho.pow
  have hz := Theory.PSL2.odd_twoCore_free_center_eq_bot
    (pCore_quotient_pCore_eq_bot 2 (G := K)) hodd hb.2 e
  let eq : (K ⧸ pCore 2 K) ≃* coreCentralQuotient K :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm
  refine ⟨hz,⟨F,inferInstance,inferInstance,hF,⟨eq.trans e⟩⟩,?_,?_⟩
  · exact hF ▸ hb.1
  · exact hF ▸ hb.2

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
