module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Definitions
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Generation.Recognition
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Generation.Comparison

/-!
# Generation by the two distinguished unitary centralizers

If their join were proper, distinguished generation and local recognition
would give a perfect group with a Bender central quotient at the original
field parameter. The concrete quotient-order comparison then makes each
unitary factor equal to the join. Their prescribed intersection would force
L = Lᵤ, contradicting the strict unitary alternative.

The comparison uses the quotient of each factor by its full center, and
therefore includes the special-unitary central cover.
Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemma 13.3.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory
universe v
variable {G : Type v} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

omit [Finite G] in
private theorem cover_subgroupOf {H F : Subgroup G} (hle : H ≤ F)
    (hH : IsUnitaryCentralizerCoverAt n H) :
    IsUnitaryCentralizerCoverAt n (H.subgroupOf F) := by
  obtain ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, hmodel⟩ := hH
  refine ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, ?_⟩
  rcases hmodel with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨(subgroupOfEquivOfLe hle).trans e⟩
  · exact Or.inr ⟨(subgroupOfEquivOfLe hle).trans e⟩

/-- The generation assertion of GLS4, Chapter 2, Lemma 13.3, with the
second-centralizer witness explicit and no additional mathematical premise. -/
public theorem two_distinguished_centralizers_generate
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hn : 2 ≤ n) (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n) :
    centralizerClosure Z u ⊔ distinguishedCentralizer Z d.torus = ⊤ := by
  by_contra hproper
  let F := centralizerClosure Z u ⊔ distinguishedCentralizer Z d.torus
  obtain ⟨hcenter, hperfect, hmodel⟩ :=
    TwoGeneratorRecognition.twoCentralizerJoin_quotient_atExponent
      h r ha hz hzM ht htM hL heven hn hcard hunitary huD hu d hproper
  have hmodel' : IsSimpleBenderGroupAtExponent n (F ⧸ center F) := by
    let eqv : (F ⧸ center F) ≃* (F ⧸ pPrimeCore 2 F) :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).symm
    cases hmodel with
    | isPSL2 he => exact .isPSL2 ⟨eqv.trans he.some⟩
    | isSuzuki he =>
      obtain ⟨m, hm, he⟩ := he
      exact .isSuzuki ⟨m, hm, ⟨eqv.trans he.some⟩⟩
    | isPSU3 he =>
      obtain ⟨E, hfield, hfinite, J, hJ, hc, hf, he⟩ := he
      exact .isPSU3 ⟨E, hfield, hfinite, J, hJ, hc, hf, ⟨eqv.trans he.some⟩⟩
  have heq : ∀ H : Subgroup G, H ≤ F → IsUnitaryCentralizerCoverAt n H → H = F := by
    intro H hHF hH
    have he := TwoGeneratorComparison.unitary_subgroup_eq_top_of_bender_quotient
      (H.subgroupOf F) hn hperfect hmodel' (cover_subgroupOf hHF hH)
    have hm := congrArg (Subgroup.map F.subtype) he
    simpa only [map_subgroupOf_eq_of_le hHF, ← MonoidHom.range_eq_map, range_subtype] using hm
  have hfirst : centralizerClosure Z u = F := heq _ le_sup_left (hunitary u huD hu).2
  have hsecond : distinguishedCentralizer Z d.torus = F := heq _ le_sup_right d.second_cover
  have hcollapse : residualGenerated M z t = centralizerClosure Z u := by
    rw [← d.intersection, hfirst, hsecond, inf_idem]
  exact (hunitary u huD hu).1.ne hcollapse

end BenderSuzuki.ZD.UnitaryExclusion
