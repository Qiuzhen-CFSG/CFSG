module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEvenExclusion
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.RankOne

/-!
# Excluding binary rank-one carriers of the original outside component

In each actual binary rank-one model, a proper overgroup of the supplied
Sylow subgroup lies in its normalizer. A solvable subgroup is proper in a
nontrivial perfect group. Thus these models have solvable Sylow control,
contradicting the original quintic component's proved nonnormalization.
No condition placing the quintic actor inside the simple carrier is used.

Source: Aschbacher--Smith 6.1.4, printed p.665, and A.3.15(5).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Chapter1.XiEmbedding.InvariantLarge
open RankOneGeneric Chapter1.Section02.LocalModels

/-- Concrete binary rank-one geometry controls the supplied Sylow subgroup
in every solvable overgroup, including those arising from outer actors. -/
theorem binary_rankOne_solvable_sylow_control
    {C : Type*} [Group C] [Finite C] [IsSimpleGroup C] [Group.IsPerfect C]
    {d : ℕ} (hd : 1 < d) (hc : EvenActions.RankOne.IsBinaryRankOne C d) :
    SolvableSylowControl 2 C := by
  intro S A hA hSA
  have hS : ChapterF.Source.RankOneSylowFacts S := by
    rcases hc with hc | hc | ⟨m,_,⟨e⟩⟩
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hc
      exact ChapterF.Source.rankOneSylowFacts_of_equiv S e
        (ChapterF.Source.rankOneSylowFacts_psl2 F d (by omega) hF _)
    · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hc
      exact ChapterF.Source.rankOneSylowFacts_of_equiv S e
        (ChapterF.Source.rankOneSylowFacts_psu3 J d (by omega) hF hconj _)
    · exact ChapterF.Source.rankOneSylowFacts_of_equiv S e
        (ChapterF.Source.suzuki_rankOneSylowFacts m _)
  apply hS.unique_maximal A hSA
  apply lt_top_iff_ne_top.mpr
  intro he
  let : Group.IsSolvable A := hA
  have hsurj : Function.Surjective A.subtype := by
    intro c
    exact ⟨⟨c,he ▸ trivial⟩,rfl⟩
  exact Group.IsPerfect.not_isSolvable C
    (Group.isSolvable_of_surjective hsurj)

attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- None of the three binary rank-one families can be the literal central
carrier of the original outside component. -/
theorem original_hermitian_component_not_binary_rankOne
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (d : ℕ) (hd : 1 < d) :
    ¬ EvenActions.RankOne.IsBinaryRankOne (coreCentralQuotient K) d := by
  intro hc
  let := hq
  let : IsSimpleGroup (coreCentralQuotient K) := IsQuasisimple.simple
  let : IsQuasisimple (coreCentralQuotient K) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center (K ⧸ pCore 2 K))) (QuotientGroup.mk'_surjective _)
  exact original_hermitian_component_no_solvable_sylow_control
    h hout hm hM₁ hCM₁ hK hnot hq (binary_rankOne_solvable_sylow_control hd hc)

/-- The entire Bender row of the actual Theorem C catalogue is excluded. -/
theorem original_hermitian_component_not_bender
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ ClassificationModels.IsBenderModel (coreCentralQuotient K) := by
  intro hc
  cases hc with
  | linear d hd he =>
    exact original_hermitian_component_not_binary_rankOne
      h hout hm hM₁ hCM₁ hK hnot hq d (by omega) (Or.inl he)
  | unitary d hd he =>
    exact original_hermitian_component_not_binary_rankOne
      h hout hm hM₁ hCM₁ hK hnot hq d (by omega) (Or.inr (Or.inl he))
  | suzuki m hpos he =>
    exact original_hermitian_component_not_binary_rankOne
      h hout hm hM₁ hCM₁ hK hnot hq (2*m+1) (by omega) (Or.inr (Or.inr ⟨m,rfl,he⟩))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
