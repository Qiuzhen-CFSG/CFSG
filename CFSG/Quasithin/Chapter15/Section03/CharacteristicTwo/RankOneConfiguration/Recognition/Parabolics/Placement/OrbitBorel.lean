module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Models
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearThree
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearTwo

/-!
# The nonnormal component orbit contradiction in 15.3.27

The reduction verifies the ambient SQTK and faithful FF inputs, transfers
the C-component into I, constructs its two-element orbit and proves that
S exhausts it. The orbit span is the prime-to-three residual, so it contains
the actual S-invariant solvable subgroup Y₊ with Sylow three-order three.

The complete nonnormal and FF model lists give matching PSL₂(2^n) or
PSL₃(2) models for the intrinsic component quotient and its star image.
The latter case contradicts the Sylow three-order of the actual Y₊ image
in the two-factor quotient. In the former case the canonical Borel
L₀ ∩ N_G(S ∩ L₀) contains Y₊ and is solvable and Y₊S-invariant. Its field
degree is even and its three-rank exceeds one, contradicting the rank
bound for every such invariant solvable subgroup of I.

This proves relative normality from the displayed earlier source inputs.
The final adapter obtains the rank-one facts from the genuine preliminary
15.3.11(5) alternative. The universal earlier orbit and complete FF
classification implications remain explicit under this module's contract;
there is no specialized orbit, model or Borel conclusion among the inputs.
Containment Y₊ ≤ L and the remaining clauses belong to the placement owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.27, printed pp.1130–1131 (PDF pp.1147–1148).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual invariant subgroup of Sylow three-order three excludes
PSL₃(2) from the model comparison. Both surviving quotient conventions
have the same binary field degree. -/
theorem linear_two_models_of_nonnormal {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K)
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hG : IsSimpleQTKE K G) (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hVT : d.V ≤ (d.T : Subgroup G))
    (h : RankOneFacts d I) (hr : primeRank 3 d.Yplus = 1) :
    ∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 2 (2 ^ n) ∧
      ClassicalGroup.IsPSL (d.starImage I c.L) 2 (2 ^ n) := by
  rcases componentModelAlternatives_of_ambient earlier classification hG d hI hf c hn hS hVT
    with hmodel | ⟨hthree, _⟩
  · exact hmodel
  · exact (LinearThree.excluded earlier hG d hI hf c hn hS h hr hthree).elim

/-- Construct the canonical Borel, retaining its actual component models
and even field degree. No solvable-invariant control is needed to construct
the witness; that control subsequently contradicts its excess three-rank. -/
theorem source_borel_witness_of_ambient {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K)
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hG : IsSimpleQTKE K G) (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hVT : d.V ≤ (d.T : Subgroup G))
    (h : RankOneFacts d I) (hr : primeRank 3 d.Yplus = 1) :
    let B := LinearTwo.canonicalBorel (localSpan c.L d.S) d.S
    ∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 2 (2 ^ n) ∧
      ClassicalGroup.IsPSL (d.starImage I c.L) 2 (2 ^ n) ∧
      B ≤ I ∧ d.Yplus ≤ B ∧ Group.IsSolvable B ∧
      d.Yplus ⊔ d.S ≤ normalizer (B : Set G) ∧ Even n ∧ 1 < primeRank 3 B := by
  obtain ⟨n, hn₂, hm, hstar⟩ :=
    linear_two_models_of_nonnormal earlier classification hG d hI hf c hn hS hVT h hr
  exact ⟨n, hn₂, hm, hstar,
    LinearTwo.source_borel_witness_of_isPSL earlier hG d hI c hn hS h hr hn₂ hm⟩

/-- The constructed orbit Borel violates the invariant solvable rank bound.
All model and quotient-coordinate premises have been discharged. -/
theorem nonnormal_contradiction_of_ambient {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K)
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hG : IsSimpleQTKE K G) (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hVT : d.V ≤ (d.T : Subgroup G))
    (h : RankOneFacts d I) (hr : primeRank 3 d.Yplus = 1)
    (hcontrol : SolvableInvariantControl d I) : False := by
  obtain ⟨_, _, _, _, hBI, _, hs, hnorm, _, hrB⟩ :=
    source_borel_witness_of_ambient earlier classification hG d hI hf c hn hS hVT h hr
  exact (not_lt_of_ge
    (invariant_solvable_three_rank_le_one d h hr hcontrol hBI hs hnorm)) hrB

/-- Relative component normality, the first clause of 15.3.27, from the
universal earlier source implications and the genuine local conclusions.
Neither minimality of I nor containment Y₊ ≤ L is assumed. -/
theorem component_normal_of_ambient {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K)
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hG : IsSimpleQTKE K G) (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hVT : d.V ≤ (d.T : Subgroup G))
    (h : RankOneFacts d I) (hr : primeRank 3 d.Yplus = 1)
    (hcontrol : SolvableInvariantControl d I) : (c.L.subgroupOf I).Normal := by
  by_contra hn
  exact nonnormal_contradiction_of_ambient earlier classification hG d hI hf c hn hS hVT
    h hr hcontrol

/-- Source-facing normality with the rank-one facts constructed by eliminating
the first alternative of 15.3.11(5). The disjunction retains precisely the
earlier numerical consequences used by the established 15.3.26(1) proof. -/
theorem component_normal_of_15_3_11_5 {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K)
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hG : IsSimpleQTKE K G) (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hVT : d.V ≤ (d.T : Subgroup G))
    (hr : primeRank 3 d.Yplus = 1) (hcontrol : SolvableInvariantControl d I)
    (h11_5 :
      (IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus) ∧
        Monoid.exponent (d.Yplus ⧸ pCore 2 d.Yplus) ∣ 3 ∧
        3 < Nat.card (d.Yplus ⧸ pCore 2 d.Yplus)) ∨ RankOneFacts d I) :
    (c.L.subgroupOf I).Normal := by
  exact component_normal_of_ambient earlier classification hG d hI hf c hS hVT
    (lemma_15_3_26_1_of_15_3_11_5 d I hr h11_5) hr hcontrol

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel
