module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourFittingOriginal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticPermuting
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticOverlap
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientHermitianThompson

/-!
# Selection of the original degree-four comparison geometry

Select an actual maximal two-local overgroup of C_G(Ω₁Z(T)). The original
Hermitian assumptions then supply an outside component, a quintic torus
permuting with the given Sylow, the exact core of XT, and its Thompson
normalization. No maximal-overgroup, component, or actor witness is an input.
The final source exclusion remains a separate theorem.
Source: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The original full Hermitian branch selects its actual comparison maximal,
outside component, and quintic subgroup, retaining all literal source identities. -/
theorem original_hermitian_quintic_selection
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2)) :
    ∃ M₁ K D : Subgroup G,
      IsMaximalTwoLocal M₁ ∧ omegaCentralizer T ≤ M₁ ∧
      K ∈ Chapter1.cComponentsIn M₁ ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      generalizedFitting K = pCore 2 K ∧ ¬ K ≤ M ∧
      Nat.card D = 5 ∧ D ≤ quinticResidual T L ∧
      (D : Set G) * (T : Set G) = ((quinticResidual T L ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
      (T : Set G) * (D : Set G) = ((quinticResidual T L ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
      (quinticResidual T L ⊔ (T : Subgroup G)).pCoreIn 2 =
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      quinticResidual T L ≤ M ⊓ M₁ ∧
      M ⊓ M₁ ≤ normalizer (quinticResidual T L : Set G) ∧
      quinticResidual T L ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let hi := h.reduced_enlargement.rankOneInput hout
  have hT : (T : Subgroup G) ≠ ⊥ := by
    intro ht
    have hR : reducedSubgroup (L ⊔ (T : Subgroup G)) = ⊥ :=
      bot_unique (hi.reduced_le_sylow.trans_eq ht)
    exact hi.noncentral (by rw [hR,commutator_bot_left])
  obtain ⟨M₁,hM₁,hCM₁⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (omegaCentralizer T) (by
      intro hz
      apply omegaCentralizer_mem_H hT
      change (pCore 2 (omegaCentralizer T)).map (omegaCentralizer T).subtype = ⊥
      rw [hz,Subgroup.map_bot])
  obtain ⟨K,hK,hq,hfit,hnot⟩ := original_hermitian_exists_component_outside h hout hm hM₁ hCM₁
  obtain ⟨D,hD,hDX,hDT,hTD⟩ := original_hermitian_quintic_permuting_torus h hout hm
  obtain ⟨hXM,hMN⟩ := original_hermitian_quintic_overlap h hout hm hM₁ hCM₁
  exact ⟨M₁,K,D,hM₁,hCM₁,hK,hq,hfit,hnot,hD,hDX,hDT,hTD,
    original_hermitian_quintic_sylow_core h hout hm,hXM,hMN,
    original_hermitian_quintic_normalizes_thompson h hout hm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
