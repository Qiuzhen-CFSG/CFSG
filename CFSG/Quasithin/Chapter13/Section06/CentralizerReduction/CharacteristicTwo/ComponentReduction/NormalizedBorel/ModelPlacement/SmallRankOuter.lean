module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.SmallRankOuter.Catalogue
public import Theory.SpecificGroups.Suzuki.CyclicOuter
public import Theory.SpecificGroups.Triality.ElementaryNine

/-!
# The outer-group calculation in case (ii) of 13.6.6

The complete binary catalogue reduces to PSL₂, Suzuki, and the two signed
degree-three families with their proved parameter restrictions. Their actual
outer groups are abelian by the proved automorphism coverage. Simplicity
of the unitary model is transported from the supplied simple group.

The application uses precisely K* = K/Z(K) inside N(K)/C(K). The published
central-cover rank transport and perfect descent then give Lᵥ* ≤ K*, with
the actual marked Sylow, action kernel, and both normalizer hypotheses.

The elementary nine constructed in the genuine triality central quotient
discharges the last catalogue input. The unconditional calculation and its
case-(ii) application retain the earlier conditional interfaces below.
Source: Aschbacher–Smith, proof of 13.6.6(ii), printed p.927.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory InitialSieve A5Module
open Theory.SpecificGroups.Classical
open scoped MatrixGroups IsMulCommutative

/-- Every surviving small-three-rank model has abelian outer group, conditional
only on the genuine triality rank witness needed by the full-catalogue sieve. -/
theorem outer_isMulCommutative_of_binaryModelAt_of_triality_nine
    (htriality : ∀ (f : ℕ) (hf : 1 < f),
      ∃ E : Subgroup (Triality.Standard.BinaryCarrier f (by omega)),
        IsElementaryAbelian 3 E ∧ Nat.card E = 9)
    {D : Type*} [Group D] [Finite D] [IsSimpleGroup D] {m : ℕ}
    (hm : 1 < m) (hmodel : BinaryModelAt D m) (hr : primeRank 3 D ≤ 1) :
    IsMulCommutative (MulAut.Outer D) := by
  rcases SmallRankOuter.small_three_rank_models_of_triality_nine htriality hm hmodel hr with
    hlin | ⟨hlin, _⟩ | ⟨hunit, _⟩ | ⟨n, hn, _, ⟨e⟩⟩
  · obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hlin
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hc
    let := Theory.PSL2.OuterSolvable.charTwo_outer_isCyclic (F := F)
    let := (MulAut.outerCongr e).isCyclic.mpr inferInstance
    infer_instance
  · obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hlin
    have hrF : primeRank 3 PSL(3,F) ≤ 1 := by rwa [← primeRank_equiv 3 e]
    let := BinarySmallThreeRankOuter.linear_outer_isMulCommutative (by omega) hc hrF
    apply IsMulCommutative.of_comm
    intro a b
    apply (MulAut.outerCongr e).injective
    simp only [map_mul, mul_comm]
  · obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := hunit
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_injective e.symm e.symm.injective
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      e.isSimpleGroup_congr.mp inferInstance
    have hrF : primeRank 3 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) ≤ 1 := by
      rwa [← primeRank_equiv 3 e]
    let := BinarySmallThreeRankOuter.unitary_outer_isCyclic J hm hc hconj hrF
    let := (MulAut.outerCongr e).isCyclic.mpr inferInstance
    infer_instance
  · let := BenderSuzuki.MatrixGroups.suzuki_outer_isCyclic n hn
    let := (MulAut.outerCongr e).isCyclic.mpr inferInstance
    infer_instance

/-- Every finite simple model in the full binary catalogue with defining
exponent greater than one and three-rank at most one has abelian outer group.
The genuine triality elementary nine discharges the last rank exclusion. -/
theorem outer_isMulCommutative_of_binaryModelAt
    {D : Type*} [Group D] [Finite D] [IsSimpleGroup D] {m : ℕ}
    (hm : 1 < m) (hmodel : BinaryModelAt D m) (hr : primeRank 3 D ≤ 1) :
    IsMulCommutative (MulAut.Outer D) :=
  outer_isMulCommutative_of_binaryModelAt_of_triality_nine
    (fun f hf => Triality.Standard.exists_elementaryAbelian_three_card_nine f (by omega))
    hm hmodel hr

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- The literal case-(ii) application: all outer and central-cover premises
are discharged except the independently owned triality elementary nine. -/
theorem residualStar_le_of_binaryModelAt_small_three_rank_of_triality_nine
    (htriality : ∀ (f : ℕ) (hf : 1 < f),
      ∃ E : Subgroup (Triality.Standard.BinaryCarrier f (by omega)),
        IsElementaryAbelian 3 E ∧ Nat.card E = 9)
    (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    {m : ℕ} (hm : 1 < m) (hmodel : BinaryModelAt (NormalizerAction.componentImage K) m)
    (hr : primeRank 3 K ≤ 1)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K) :
    residualStar s K ≤ NormalizerAction.componentImage K := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (NormalizerAction.componentImage K) :=
    (NormalizerAction.componentCentralQuotientEquiv K).isSimpleGroup_congr.mp
      IsQuasisimple.simple
  exact residualStar_le_of_small_three_rank s T K hK hr
    (outer_isMulCommutative_of_binaryModelAt_of_triality_nine htriality hm hmodel)
    hk hTL S hS hDN hTN

/-- The case-(ii) containment on the actual component image, with all model
outer-group and central-cover premises discharged. The rank hypothesis is
on K, while the conclusion lies in N(K)/C(K); no identification K = K* is used. -/
theorem residualStar_le_of_binaryModelAt_small_three_rank
    (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    {m : ℕ} (hm : 1 < m) (hmodel : BinaryModelAt (NormalizerAction.componentImage K) m)
    (hr : primeRank 3 K ≤ 1)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K) :
    residualStar s K ≤ NormalizerAction.componentImage K := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (NormalizerAction.componentImage K) :=
    (NormalizerAction.componentCentralQuotientEquiv K).isSimpleGroup_congr.mp
      IsQuasisimple.simple
  exact residualStar_le_of_small_three_rank s T K hK hr
    (outer_isMulCommutative_of_binaryModelAt hm hmodel) hk hTL S hS hDN hTN

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
