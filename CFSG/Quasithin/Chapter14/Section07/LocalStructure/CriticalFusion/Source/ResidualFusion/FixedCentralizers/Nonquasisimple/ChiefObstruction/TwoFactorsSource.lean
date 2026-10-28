module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.PlaneNoncentralitySource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Characteristic
public import Theory.GroupTheory.NoncentralChiefRefinement.TwoIntervals

/-!
# Two chief factors on the original K

The original identities U=[U,K] and [U,O₂(H)]=V₁ first show that U cannot
centralize O₂(K): otherwise the three-subgroups lemma kills V₁. Applying
the same argument within K shows that K acts nontrivially on O₂(K)/U.
Thus both intervals 1<U and U<O₂(K) are noncentral binary intervals of the
two-perfect actor K. Their chief refinements supply the required two factors.
This proves the count from actual commutators, with no dual-module premise.

Source: Aschbacher–Smith 14.5.21(1–2) and 14.7.68, printed pp.1071–1072.
The point-commutator producer from original13.3.2 is imported for final assembly.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)
include d

theorem U_not_centralizes_K_core
    (hUQ : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ¬ F.U ≤ centralizer ((K F).pCoreIn 2 : Set G) := by
  intro hcentral
  have hQK : ⁅F.H.pCoreIn 2, K F⁆ ≤ (K F).pCoreIn 2 := by
    rw [K_core_eq_inter]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp
      ((K_le_H F).trans (F.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))))
      (le_normalizer_iff_commutator_le_right.mp
        ((pCoreIn_le 2 F.H).trans (H_normalizes_K F)))
  have h₁ : ⁅⁅K F,F.H.pCoreIn 2⁆,F.U⁆ = ⊥ := by
    rw [commutator_comm (K F) (F.H.pCoreIn 2),commutator_eq_bot_iff_le_centralizer]
    exact hQK.trans (le_centralizer_iff.mp hcentral)
  have h₂ : ⁅⁅F.H.pCoreIn 2,F.U⁆,K F⁆ = ⊥ := by
    rw [commutator_comm (F.H.pCoreIn 2) F.U,hUQ,commutator_eq_bot_iff_le_centralizer]
    exact le_centralizer_iff.mp ((K_le_H F).trans d.H_centralizes_point)
  have hz := commutator_commutator_eq_bot_of_rotate h₁ h₂
  rw [← d.U_eq_commutator_K,hUQ] at hz
  exact d.z_ne_one (mem_bot.mp (hz ▸ (d.point ▸ mem_zpowers d.z)))

theorem K_core_commutator_not_le_U
    (hUQ : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ¬ ⁅(K F).pCoreIn 2,K F⁆ ≤ F.U := by
  intro hle
  let := d.abelian
  have h₁ : ⁅⁅K F,(K F).pCoreIn 2⁆,F.U⁆ = ⊥ := by
    rw [commutator_comm (K F) ((K F).pCoreIn 2),commutator_eq_bot_iff_le_centralizer]
    exact hle.trans (le_centralizer F.U)
  have h₂ : ⁅⁅(K F).pCoreIn 2,F.U⁆,K F⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    have hh : ⁅(K F).pCoreIn 2,F.U⁆ ≤ F.Vi 1 := by
      rw [← hUQ,commutator_comm F.U (F.H.pCoreIn 2)]
      exact commutator_mono (pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)) le_rfl
    exact hh.trans (le_centralizer_iff.mp ((K_le_H F).trans d.H_centralizes_point))
  have hz := commutator_commutator_eq_bot_of_rotate h₁ h₂
  rw [← d.U_eq_commutator_K] at hz
  exact d.U_not_centralizes_K_core hUQ (commutator_eq_bot_iff_le_centralizer.mp hz)

theorem exists_K_two_chief_of_point_commutator
    (hUQ : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ s : ChiefSeries (K F), s.head = ⊥ ∧ s.last = ⊤ ∧ 2 ≤ s.noncentralTwoCount := by
  let A : NormalNode (K F) := ⟨F.U.subgroupOf (K F),
    normal_subgroupOf_of_le_normalizer ((K_le_H F).trans d.conjugationSection.normalized)⟩
  let B : NormalNode (K F) := ⟨pCore 2 (K F),(inferInstance : (pCore 2 (K F)).Normal)⟩
  have hAcore : A.val ≤ B.val := by
    intro x hx
    obtain ⟨a,ha,he⟩ := d.U_le_K_core hx
    exact (Subtype.ext he : a = x) ▸ ha
  have hAp : IsPGroup 2 A.val := pCore_isPGroup.to_le hAcore
  have hAm : A.val.map (K F).subtype = F.U := map_subgroupOf_eq_of_le d.U_le_K
  have hA : IsNoncentralTwo ⊥ A := by
    refine ⟨hAp.to_quotient _,?_⟩
    rw [isCentral_iff_commutator_le]
    intro hc
    have hm := map_mono (f := (K F).subtype) hc
    rw [map_commutator,← MonoidHom.range_eq_map,range_subtype,hAm] at hm
    change ⁅K F,F.U⁆ ≤ (⊥ : Subgroup (K F)).map (K F).subtype at hm
    rw [Subgroup.map_bot,commutator_comm,← d.U_eq_commutator_K] at hm
    exact d.z_ne_one (mem_bot.mp (hm (d.U₀_le_U d.z_mem_U₀)))
  have hB : IsNoncentralTwo A B := by
    let : A.val.Normal := A.property
    refine ⟨pCore_isPGroup.to_quotient _,?_⟩
    rw [isCentral_iff_commutator_le]
    intro hc
    have hm := map_mono (f := (K F).subtype) hc
    rw [map_commutator,← MonoidHom.range_eq_map,range_subtype,hAm] at hm
    exact d.K_core_commutator_not_le_U hUQ ((commutator_comm _ _).le.trans hm)
  exact exists_two_chief_of_two_noncentral (K_twoPerfect F) A B hAcore hA hB
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
