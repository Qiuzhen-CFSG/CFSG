module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalChief
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Original Chapter 12 applications of the Cartan chief-factor comparison

The original chosen reduced module supplies the universal rank-one Input.
The literal right block propagates to the maximal component and identifies
both block layers with the four-space. The original cubic has at least
three noncentral factors on T∩L; a right block bounds that count by three.
Together with the nonblock torus argument this forces degree two whenever
the original component fails to centralize omega. Thus degree greater than
two gives omega-centralization without either block exclusion as a premise.

The degree-two block exclusions, postcentralization whole-module recognition,
component sieve and final source assembly remain necessary.
Source: Aschbacher–Smith 5.1.13 and 12.2.2, printed pp.638,795,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C K : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The original right block has the same intrinsic layer as the maximal component. -/
theorem rankOne_local_cartan_right_block_layers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X C) (a : LocalA7Configuration T L H X K)
    (hb : ChapterC.IsChiBlockIn (pResidual 2 H)) :
    (ChapterC.blockU (pResidual 2 H)).map (H.subtype.comp (pResidual 2 H).subtype) =
        localOmegaModule T K ∧
      (ChapterC.blockU K).map K.subtype = localOmegaModule T K ∧
      ⁅(K ⊔ (T : Subgroup G)).pCoreIn 2,K⁆ = localOmegaModule T K :=
  a.right_block_layers
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d hb

/-- The original cubic and moved layer give the left chief-factor lower bound. -/
theorem rankOne_local_cartan_cubic_chief_lower
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X C) (a : LocalA7Configuration T L H X K) :
    n ≤ conjugationCubicLength C (RankOneModule.commutatorLayer T L) ∧
      n + Nat.log 4 (2 ^ n) ≤ conjugationCubicLength C ((T : Subgroup G) ⊓ L) ∧
      3 ≤ conjugationCubicLength C ((T : Subgroup G) ⊓ L) :=
  a.left_cubic_chief_lower
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d

/-- The right block bounds the count on the same original left Sylow intersection. -/
theorem rankOne_local_cartan_right_block_chief_upper
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X C) (a : LocalA7Configuration T L H X K)
    (hb : ChapterC.IsChiBlockIn (pResidual 2 H)) :
    conjugationCubicLength C ((T : Subgroup G) ⊓ L) ≤ 3 :=
  a.right_block_chief_upper
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d hb

/-- Every actual local A₇ configuration has the original degree two. -/
theorem rankOne_local_cartan_configuration_degree_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X C) (a : LocalA7Configuration T L H X K) : n = 2 :=
  a.degree_two
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d

/-- The genuine FF producer removes the configuration premise from degree two. -/
theorem rankOne_local_cartan_noncentral_degree_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hXC : ¬ X ≤ omegaCentralizer T) : n = 2 :=
  localCartan_noncentral_degree_two
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hXC

/-- The original higher-degree component centralizes omega without a block guard. -/
theorem rankOne_local_cartan_centralizes_of_degree_gt_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hlarge : 2 < n) : X ≤ omegaCentralizer T :=
  localCartan_centralizes_of_degree_gt_two
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hlarge

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
