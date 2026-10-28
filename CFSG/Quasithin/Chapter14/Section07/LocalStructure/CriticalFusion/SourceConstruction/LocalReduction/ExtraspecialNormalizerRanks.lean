module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerKernel
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.SpecificGroups.HeisenbergPrime.ElementaryPlane

/-!
# Three-ranks in the original extraspecial normalizer

The elementary plane of K/O₂(K) lifts across its two-core, giving
m₃(K) ≥ 2. The original maximal two-local bound gives m₃(N_G(K)) = 2.
The literal action kernel C centralizes this quotient with cubic center,
so the residual-centralizer rank theorem bounds m₃(C) by one. Thus its
Sylow three-subgroups are cyclic.

Source: Aschbacher–Smith 14.7.21(1), printed p.1049. These are the
rank inputs for the subsequent normal-three-complement argument.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original extraspecial residual supplies two independent cubic directions. -/
theorem extraspecial_residual_threeRank_lower
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    2 ≤ primeRank 3 (K F) := by
  obtain ⟨e⟩ := he
  rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 (K F)) pCore_isPGroup,
    primeRank_congr 3 e]
  obtain ⟨E,hE,hc⟩ := HeisenbergPrime.exists_elementary_plane (by decide : 3 ≠ 2)
  let := hE
  exact IsElementaryAbelian.primeRank_ge_of_card E hc

/-- The maximal two-local has three-rank two, and its literal quotient-action
centralizer has three-rank at most one. No quotient-rank monotonicity is assumed. -/
theorem extraspecial_normalizer_threeRanks
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    primeRank 3 (normalizer (K F : Set G)) = 2 ∧
      primeRank 3 (normalizerResidualCentralizer F) ≤ 1 := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  have hn := (extraspecial_residual_normalizer_unique d h hab structural previous faithful he).1
  have hr : primeRank 3 N ≤ 2 := (d.qtke.twoLocal_sqtk hn.1).stronglyQuasithin 3 (by decide) (by decide)
  have hK := extraspecial_residual_threeRank_lower he
  have hlo := (primeRank_le_of_injective 3 (inclusion (K F).le_normalizer)
    (inclusion_injective (K F).le_normalizer))
  change primeRank 3 (K F) ≤ primeRank 3 N at hlo
  have hrN : primeRank 3 N = 2 := by omega
  refine ⟨hrN,?_⟩
  have hCN : C ≤ N := map_subtype_le _
  have hc : ⁅K F,C⁆ ≤ (K F).pCoreIn 2 := by
    apply commutator_le_core_of_pCoreNormalizerAction_eq_one 2 (K F) C hCN
    rintro ⟨c,⟨n,hn,rfl⟩⟩
    exact hn
  have hcomm : ⁅(pResidual 2 C).map C.subtype,K F⁆ ≤ (K F).pCoreIn 2 := by
    rw [commutator_comm] at hc
    exact (commutator_mono (map_subtype_le _) le_rfl).trans hc
  obtain ⟨e⟩ := he
  have hz : Nat.card (center ((K F) ⧸ pCore 2 (K F))) ≤ 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv,HeisenbergPrime.card_center]
  have hCK : C ⊔ K F ≤ N := sup_le hCN (K F).le_normalizer
  exact Theory.GroupTheory.ResidualCentralizerRank.three_rank_le_one_of_normalized_factor_cubic_center
    C (K F) hCN hcomm hz hK
    ((primeRank_le_of_injective 3 (inclusion hCK) (inclusion_injective hCK)).trans hr)

/-- Every three-Sylow of the actual residual centralizer is cyclic. -/
theorem extraspecial_normalizer_centralizer_sylow_cyclic
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (S : Sylow 3 (normalizerResidualCentralizer F)) : IsCyclic S :=
  S.isCyclic_of_odd_of_primeRank_le_one (by decide)
    (extraspecial_normalizer_threeRanks d h hab structural previous faithful he).2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
