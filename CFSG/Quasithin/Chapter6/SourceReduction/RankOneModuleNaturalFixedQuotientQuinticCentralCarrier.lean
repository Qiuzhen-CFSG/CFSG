module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticFaithfulAction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedCenter
public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# The original simple carrier of the quintic component action

The comparison component is quasisimple modulo its two-core. Its actual
simple carrier is therefore (K/O₂(K))/Z(K/O₂(K)). Strong quasithinness
passes through the two-core quotient, and the proved Theorem A/C source
classifies the literal central quotient. Perfectness makes automorphisms
faithful on that quotient, so the original five-subgroup retains its
faithful normalizer action. No simple identification of K/O₂(K), restricted
A.3.15 alternative, or exclusion of the Tits carrier is assumed.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666, and A.2.3/A.3.15.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The proved source catalogue applies to the actual central quotient of
any quasisimple two-core quotient in the comparison two-local. -/
theorem original_component_core_central_catalogue
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hM₁ : IsMaximalTwoLocal M₁) (hK : K ≤ M₁)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ChapterA.Section02.IsTheoremCModel (coreCentralQuotient K) := by
  let := hq
  have hsq : IsSQTK KnownSimple.IsKnownSimple K :=
    ((h.simpleQTKE.twoLocal_sqtk hM₁.1).subgroup (K.subgroupOf M₁)).knownSimple_of_equiv
      (subgroupOfEquivOfLe hK)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (K ⧸ pCore 2 K) := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  exact ChapterA.Section03.SourceEmbeddings.quasisimple_center_quotient_theoremC_model hQ

/-- The same original order-five subgroup acts faithfully on the literal
simple central quotient. Its normalizer action is unchanged. -/
theorem original_hermitian_quintic_central_action_injective
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (D : Subgroup G) (hD : Nat.card D = 5) (hDX : D ≤ quinticResidual T L) :
    Function.Injective ((normalizerCoreCentralAction K).comp
      (inclusion (hDX.trans
        (original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK)))) := by
  let := hq
  exact MulAut.quotient_center_injective.comp
    (original_hermitian_quintic_prime_action_injective h hout hm hM₁ hCM₁ hK hnot D hD hDX)

/-- The actual normalizer image of the original five-subgroup has order five
on the simple central carrier; no replacement abstract actor is selected. -/
theorem original_hermitian_quintic_central_image_card
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (D : Subgroup G) (hD : Nat.card D = 5) (hDX : D ≤ quinticResidual T L) :
    Nat.card (coreCentralActorImage K D) = 5 := by
  have hn := hDX.trans (original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK)
  have hi := original_hermitian_quintic_central_action_injective
    h hout hm hM₁ hCM₁ hK hnot hq D hD hDX
  let f := (normalizerCoreCentralAction K).comp (inclusion hn)
  have he : f.range = coreCentralActorImage K D := by
    ext a
    constructor
    · rintro ⟨d,rfl⟩
      exact mem_map_of_mem (normalizerCoreCentralAction K) (show (inclusion hn d) ∈
        D.subgroupOf (normalizer (K : Set G)) from d.property)
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  rw [←he]
  exact (Nat.card_congr (MonoidHom.ofInjective (f := f) hi).toEquiv).symm.trans hD

/-- One original outside component carries its genuine source catalogue and
all actual five-subgroup images on its simple central quotient. The complete
Theorem C alternatives, including Tits, are retained. -/
theorem original_hermitian_exists_classified_outside_component
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn M₁ ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ generalizedFitting K = pCore 2 K ∧ ¬ K ≤ M ∧
      ChapterA.Section02.IsTheoremCModel (coreCentralQuotient K) ∧
      ∀ D : Subgroup G, Nat.card D = 5 → D ≤ quinticResidual T L →
        Nat.card (coreCentralActorImage K D) = 5 := by
  obtain ⟨K,hK,hq,hfit,hnot⟩ := original_hermitian_exists_component_outside h hout hm hM₁ hCM₁
  exact ⟨K,hK,hq,hfit,hnot,original_component_core_central_catalogue h hM₁ hK.1 hq,
    fun D hD hDX => original_hermitian_quintic_central_image_card
      h hout hm hM₁ hCM₁ hK hnot hq D hD hDX⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
