module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticOddExclusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticBinaryRankOne
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticJankoOne
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticBinaryEndpoints
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticBinaryLinear
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticLargerMathieu
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticMathieuTwelve
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticMathieuElevenHeld
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticJankoTwo
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticHigmanSims
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticRudvalis

/-!
# The remaining literal carriers of the original outside component

Apply the proved full Theorem C catalogue to the same original component,
then use the genuine quintic exclusions for its alternating, odd linear-two,
binary and finite rows. The surviving alternatives retain the actual central
quotient and their exact group models. The odd ternary, J₄ and Tits source
arguments remain separate mathematical duties.

Source: Aschbacher--Smith 6.1.4 and A.3.15, printed pp.665--666 and 50--51.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- Every remaining carrier is an actual odd ternary, J₄ or Tits model of
the original outside component's simple central quotient. -/
theorem original_hermitian_component_remaining_models
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool,
      IsPSLSign (coreCentralQuotient K) unitary 3 p) ∨
      Nonempty (coreCentralQuotient K ≃* Janko4.Model) ∨
      Nonempty (coreCentralQuotient K ≃* Tits.ParrottGroup) := by
  let := hq
  let : IsSimpleGroup (coreCentralQuotient K) := IsQuasisimple.simple
  let : Group.IsPerfect (coreCentralQuotient K) := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)))
  have hc := ChapterA.Section03.SourceComponents.sourceTheoremC_to_local
    (Group.IsPerfect.not_isMulCommutative (coreCentralQuotient K))
    (original_component_core_central_catalogue h hM₁ hK.1 hq)
  cases hc with
  | alternating r hr he =>
    exact (original_hermitian_component_not_alternating
      h hout hm hM₁ hCM₁ hK hnot hq r hr.2 he).elim
  | linear_odd p d hp ho hd _ he =>
    exact (original_hermitian_component_not_odd_linear
      h hout hm hM₁ hCM₁ hK hnot hq p d hp ho hd he).elim
  | three_odd p hp ho unitary he => exact Or.inl ⟨p,hp,ho,unitary,he⟩
  | rank_one he =>
    exact (original_hermitian_component_not_bender h hout hm hM₁ hCM₁ hK hnot hq he).elim
  | rank_two he =>
    exact Or.inr (Or.inr
      (original_hermitian_rankTwo_component_tits h hout hm hM₁ hCM₁ hK hnot hq he))
  | binary_linear r hr he =>
    exact (original_hermitian_component_not_binary_linear
      h hout hm hM₁ hCM₁ hK hnot hq r hr he).elim
  | sporadic name hne he =>
    cases name with
    | m11 => exact (original_hermitian_component_not_mathieuEleven h hout hm hM₁ hCM₁ hK hnot hq he).elim
    | m12 => exact (original_hermitian_component_not_mathieuTwelve h hout hm hM₁ hCM₁ hK hnot hq he).elim
    | m22 => exact (original_hermitian_component_not_larger_mathieu h hout hm hM₁ hCM₁ hK hnot hq (Or.inl he)).elim
    | m23 => exact (original_hermitian_component_not_larger_mathieu h hout hm hM₁ hCM₁ hK hnot hq (Or.inr (Or.inl he))).elim
    | m24 => exact (original_hermitian_component_not_larger_mathieu h hout hm hM₁ hCM₁ hK hnot hq (Or.inr (Or.inr he))).elim
    | j2 => exact (original_hermitian_component_not_jankoTwo h hout hm hM₁ hCM₁ hK hnot hq he).elim
    | j3 => exact (hne rfl).elim
    | j4 => exact Or.inr (Or.inl he)
    | hs => exact (original_hermitian_component_not_higmanSims h hout hm hM₁ hCM₁ hK hnot hq he).elim
    | he => exact (original_hermitian_component_not_held h hout hm hM₁ hCM₁ hK hnot hq he).elim
    | ru => exact (original_hermitian_component_not_rudvalis h hout hm hM₁ hCM₁ hK hnot hq he).elim
  | janko_one he =>
    exact (original_hermitian_component_not_jankoOne h hout hm hM₁ hCM₁ hK hnot hq he).elim

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
