module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsQuinticResidualCentralization
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The original Tits two-core moves the full Hermitian module

The original quintic residual centralizes the full module modulo the whole
two-core of KT, but its actual order-five torus does not centralize the module
itself. If that core centralized the module, the residual displacement would
lie in the core's omega-center, which the actual component centralizes.
Two-perfect commutator idempotence excludes this. In particular the Tits core
cannot be contained in the original two-core of LT.

This is a necessary original-source inference in the remaining Tits branch
of Aschbacher--Smith 6.1.4, printed pp.665--666. It makes no generic assertion
about Thompson subgroups of Tits extensions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The whole two-core of the original KT join acts nontrivially on the
same full reduced Hermitian module. -/
theorem original_hermitian_tits_core_not_centralizes_module
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    ¬ (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      centralizer (reducedSubgroup (L ⊔ (T : Subgroup G)) : Set G) := by
  intro hRB
  let X := quinticResidual T L
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let R := (K ⊔ (T : Subgroup G)).pCoreIn 2
  have hXL : X ≤ L := (map_subtype_le _).trans inf_le_left
  have hXB : X ≤ normalizer (B : Set G) := hXL.trans hm.normalizes
  have hXK : X ≤ K := original_hermitian_quintic_le_tits_component
    h hout hm hM₁ hCM₁ hK hnot hqK e
  have hBR : B ⊓ R ≤ omegaOneCenterAmbient R := by
    intro b hb
    have hbB : b ∈ omegaOneCenterAmbient ((L ⊔ (T : Subgroup G)).pCoreIn 2) :=
      h.reduced_enlargement_eq_omega_core ▸ hb.1
    have hb2 := ((mem_omegaOneCenterAmbient_iff _ b).mp hbB).2.1
    exact (mem_omegaOneCenterAmbient_iff R b).mpr
      ⟨hb.2,hb2,(le_centralizer_iff.mp hRB) hb.1⟩
  have hdispR : ⁅B,X⁆ ≤ R := by
    rw [commutator_comm]
    exact original_hermitian_tits_quintic_residual_centralizes_mod_core
      h hout hm hM₁ hCM₁ hK hnot hqK e
  have hdisp : ⁅B,X⁆ ≤ omegaOneCenterAmbient R :=
    (le_inf (le_normalizer_iff_commutator_le_left.mp hXB) hdispR).trans hBR
  have hquad : ⁅⁅B,X⁆,X⁆ = ⊥ := by
    apply bot_unique
    exact (commutator_mono hdisp hXK).trans_eq
      (original_hermitian_tits_component_centralizes_omega
        h hout hm hM₁ hCM₁ hK hnot hqK e)
  have hBtwo : IsPGroup 2 B :=
    T.isPGroup'.to_le (h.reduced_enlargement.rankOneInput hout).reduced_le_sylow
  have hcomm : ⁅B,X⁆ = ⊥ :=
    (commutator_isPPerfect_idempotent X B (quinticResidual_twoPerfect T L)
      hBtwo hXB).symm.trans hquad
  have hXC : X ≤ centralizer (B : Set G) := by
    rw [commutator_comm] at hcomm
    exact commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hXcore : X ≤ L.pCoreIn 2 := by
    rw [←hm.centralizer_eq_core (OrthogonalFourMinus.RankOne.hermitian_injective 2)]
    exact le_inf hXL hXC
  obtain ⟨D,hD,_,hDX,_,_,_⟩ := original_hermitian_quintic_torus h hout hm
  have hdiv : 5 ∣ Nat.card (L.pCoreIn 2) := hD ▸ card_dvd_of_le (hDX.trans hXcore)
  obtain ⟨a,ha⟩ := (isPGroup_pCoreIn 2 L).exists_card_eq
  rw [ha] at hdiv
  exact (by decide : ¬ 5 ∣ 2) (Nat.prime_five.dvd_of_dvd_pow hdiv)

/-- The entire original Tits core escapes the original LT core. This uses
the newly proved residual centralization, with both kernels unchanged. -/
theorem original_hermitian_tits_core_not_le_original_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    ¬ (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  intro hRQ
  apply original_hermitian_tits_core_not_centralizes_module
    h hout hm hM₁ hCM₁ hK hnot hqK e
  apply hRQ.trans
  apply le_centralizer_iff.mp
  intro b hb
  rw [h.reduced_enlargement_eq_omega_core] at hb
  exact ((mem_omegaOneCenterAmbient_iff _ b).mp hb).2.2

/-- The same Tits core lies in the actual inner Sylow S=O₂(XT). Together
with core escape, this locates a nontrivial image in S/O₂(LT). -/
theorem original_hermitian_tits_core_le_inner_sylow
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := K ⊔ (T : Subgroup G)
  have hRT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)] using
      pCoreIn_le_sylow J (T.subtype le_sup_right)
  have hXK := original_hermitian_quintic_le_tits_component
    h hout hm hM₁ hCM₁ hK hnot hqK e
  have hHJ : quinticResidual T L ⊔ (T : Subgroup G) ≤ J :=
    sup_le (hXK.trans le_sup_left) le_sup_right
  rw [←original_hermitian_quintic_sylow_core h hout hm]
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) (hRT.trans le_sup_right)
    (hHJ.trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
