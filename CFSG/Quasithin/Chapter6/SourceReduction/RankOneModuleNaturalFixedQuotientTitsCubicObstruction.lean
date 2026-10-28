module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsFixedGeometry
public import Theory.GroupTheory.CComponent.CentralizerMovement
public import Theory.SpecificGroups.Tits.ThreeRankLowerBound

/-!
# Cubic residuals cannot move the original inner omega-center in the Tits case

The original Sylow omega-center lies in the inner Sylow omega-center W.
Thus C_G(W) lies in the same M₁. The outside component centralizes W and
persists in N_G(W). Its centerless Tits quotient has cubic rank two and
outer automorphism group a two-group. The actual two-local rank bound
therefore forces every cubic residual normalizing W to centralize W.

Source application: Aschbacher--Smith 6.1.4, printed pp.665--666, using
the full-rank component argument of A.3.18.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation PerfectCentralCovering
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The actual full Sylow omega-center lies in the actual inner omega-center. -/
theorem original_hermitian_sylow_omega_le_inner_omega
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2)) :
    omegaOneCenterAmbient (T : Subgroup G) ≤ omegaOneCenterAmbient
      (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let S := ((T : Subgroup G) ⊓ L) ⊔ Q
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hST : S ≤ (T : Subgroup G) := sup_le inf_le_left hQT
  have hBT : B ≤ (T : Subgroup G) :=
    (h.reduced_enlargement.rankOneInput hout).reduced_le_sylow
  have hC : (T : Subgroup G) ⊓ centralizer (B : Set G) = Q :=
    full_reduced_hermitian_sylow_centralizer h hm
  intro z hz
  obtain ⟨hzT,hz2,hzc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzQ : z ∈ Q := hC.le ⟨hzT,fun b hb => hzc b (hBT hb)⟩
  exact (mem_omegaOneCenterAmbient_iff S z).mpr
    ⟨mem_sup_right hzQ,hz2,fun s hs => hzc s (hST hs)⟩

/-- The Tits alternative forbids cubic residual movement of the original
inner omega-center, without any new local rank or cover assumption. -/
theorem original_hermitian_tits_inner_omega_cubic_residual_centralizes
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup)
    (A : Subgroup G)
    (hA : A ≤ normalizer (omegaOneCenterAmbient
      (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) : Set G))
    (hres : (primeToResidual 3 A).map A.subtype = A) :
    ⁅omegaOneCenterAmbient
      (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2),A⁆ = ⊥ := by
  let W := omegaOneCenterAmbient
    (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
  by_contra hmove
  have hW : W ≠ ⊥ := by
    intro hh
    exact hmove (by change ⁅W,A⁆ = ⊥; rw [hh,commutator_bot_left])
  let := hqK
  let eK : (K ⧸ pCore 2 K) ≃* Tits.ParrottGroup :=
    centralQuotientEquivOfUniversalKernelEqBot
      Tits.CentralCoverLifting.CompatibleGenerators.universalProjection_ker_eq_bot e
  have hz : center (K ⧸ pCore 2 K) = ⊥ :=
    center_eq_bot_of_centralQuotientEquiv
      Tits.CentralCoverLifting.CompatibleGenerators.universalProjection_ker_eq_bot e
  have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_congr 3 (eK.trans Tits.parrottFiniteImageEquiv)]
    exact Tits.ThreeRank.rank_two_le
  have ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) :=
    Tits.OuterOddSubgroups.parrott_outer_isPGroup.of_equiv (MulAut.outerCongr eK).symm
  have hN : primeRank 3 (normalizer (W : Set G)) ≤ 2 :=
    (h.simpleQTKE.twoLocal_sqtk
      ⟨W,hW,(omegaOneCenterAmbient_elementaryAbelian _).isPGroup,rfl⟩).stronglyQuasithin
        3 Nat.prime_three (by decide)
  have hCW : centralizer (W : Set G) ≤ M₁ :=
    (centralizer_le (original_hermitian_sylow_omega_le_inner_omega h hout hm)).trans hCM₁
  have hKW : K ≤ centralizer (W : Set G) := by
    apply le_centralizer_iff.mp
    exact commutator_eq_bot_iff_le_centralizer.mp
      (original_hermitian_tits_component_centralizes_inner_omega
        h hout hm hM₁ hCM₁ hK hnot hqK e)
  exact hK.2.not_centralizes_of_cubic_movement hCW hz hr ho hN hA hres hmove hKW

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
