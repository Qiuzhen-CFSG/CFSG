module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticAction
public import Theory.GroupTheory.PPerfectPrimeComplement
public import Theory.GroupTheory.TwoPerfectNormalizerControl

/-!
# Faithfulness of the actual quintic quotient actor

The literal residual has order five modulo its two-core and is
two-perfect. Its nontrivial action on the original outside component
quotient is therefore faithful on every actual subgroup of order five.
The action is the normalizer's conjugation on K/O₂(K), with no replacement
actor or selected representation.

Source: Aschbacher--Smith 6.1.4, printed p.665.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The actual quintic subgroup acts faithfully on the original K/O₂(K). -/
theorem original_hermitian_quintic_prime_action_injective
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (D : Subgroup G) (hD : Nat.card D = 5) (hDX : D ≤ quinticResidual T L) :
    Function.Injective ((normalizerQuotientAction K (pCore 2 K)).comp
      (inclusion (hDX.trans
        (original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK)))) := by
  let X := quinticResidual T L
  have hn := original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK
  let f := (normalizerQuotientAction K (pCore 2 K)).comp (inclusion hn)
  have hf : f ≠ 1 := by
    intro he
    apply original_hermitian_quintic_component_action_nontrivial h hout hm hM₁ hCM₁ hK hnot
    rw [commutator_comm]
    apply commutator_le_of_normalizerQuotientAction_eq_one K X (pCore 2 K) hn
    intro x
    exact congrArg (fun a : X →* MulAut (K ⧸ pCore 2 K) => a x) he
  let E := D.subgroupOf X
  let e : D ≃* E := (subgroupOfEquivOfLe hDX).symm
  have hE : Nat.card E = 5 := (Nat.card_congr e.toEquiv).symm.trans hD
  have hi := prime_complement_restriction_injective (quinticResidual_twoPerfect T L)
    (by decide : 5 ≠ 2) (original_hermitian_quintic_core_quotient h hout hm).2 E hE f hf
  intro x y hxy
  have he : e x = e y := hi hxy
  exact e.injective he

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
