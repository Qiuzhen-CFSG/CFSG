module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeAmbientSourceNormalizer
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
public import Theory.Quasithin.PositiveLocalRank

/-!
# The containing binary point component is simple

The A.3.6 catalogue for the actual quasisimple containing component has
either a simple carrier or a central three-cover. In the latter case its
central cubic subgroup commutes with the original smaller component B.
The actual quotient B/O₂(B) is centreless PSL₃(2), so the two cubic ranks
add inside their join in N(B). This contradicts the original normalizer's
cubic rank at most one. No quasisimplicity of B is assumed.

Source: Aschbacher--Smith A.3.6 and the original point-centralizer setting
of 15.3.23, printed pp.43--45,1128--1129.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
variable {X : Type*} [Group X] [Finite X]

private theorem binary_three_not_containing_cubic_center
    {B K : Subgroup X} (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hr : primeRank 3 (normalizer (B : Set X)) ≤ 1)
    (eZ : center K ≃* Multiplicative (ZMod 3)) : False := by
  let A := (center K).map K.subtype
  have hc : A ≤ centralizer (B : Set X) := by
    rintro x ⟨a,ha,rfl⟩ b hb
    exact congrArg Subtype.val (mem_center_iff.mp ha (⟨b,hBK hb⟩ : K))
  have hn : A ≤ normalizer (B : Set X) := hc.trans (Subgroup.centralizer_le_normalizer _)
  let eSL := eB.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  have hz : Nat.Coprime 3 (Nat.card (center (B ⧸ pCore 2 B))) := by
    rw [Nat.card_congr (centerCongr eSL).toEquiv,Matrix.PSL3Two.center_eq_bot,card_bot]
    decide
  have hcomm : ⁅(pResidual 2 A).map A.subtype,B⁆ ≤ B.pCoreIn 2 := by
    have hb : ⁅A,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hc
    exact (commutator_mono (map_subtype_le _) le_rfl).trans (hb ▸ bot_le)
  have hsum := ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    (by decide : Odd 3) A B hn hcomm hz
  have hA : 1 ≤ primeRank 3 A := by
    apply Theory.Quasithin.one_le_primeRank_of_dvd_card
    change 3 ∣ Nat.card ((center K).map K.subtype)
    rw [card_map_of_injective K.subtype_injective,Nat.card_congr eZ.toEquiv]
    simp
  have hB : 1 ≤ primeRank 3 B := by
    have hq : 1 ≤ primeRank 3 (B ⧸ pCore 2 B) := by
      apply Theory.Quasithin.one_le_primeRank_of_dvd_card
      rw [Nat.card_congr eSL.toEquiv,Matrix.PSL3Two.card_SL]
      decide
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup] at hq
    exact hq
  have hu := (primeRank_mono 3 (sup_le hn B.le_normalizer)).trans hr
  omega

/-- The actual containing component has a simple Theorem C carrier;
the central three-cover alternative is excluded by the original smaller
component's full normalizer bound. -/
theorem binary_three_containing_simple_models
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (hO : pCore 2 X = ⊥)
    {B K : Subgroup X} (hK : K.IsCComponent) (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) [IsQuasisimple K]
    (hr : primeRank 3 (normalizer (B : Set X)) ≤ 1) :
    IsSimpleGroup K ∧ Chapter1.Section02.LocalModels.TheoremCModel K := by
  rcases ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
    hX hO hK with hs | ⟨⟨eZ⟩,_⟩
  · exact hs
  · exact (binary_three_not_containing_cubic_center hBK eB hr eZ).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
