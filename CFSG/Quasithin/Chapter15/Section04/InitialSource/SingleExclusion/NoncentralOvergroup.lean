module

public import CFSG.Quasithin.Chapter15.Section04.InitialSource.SingleExclusion.SingleOvergroup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup.NoncentralSource

/-!
# The original single-factor overgroup theorem without universal classification

Each actual Chapter 15 input has C_G(Ω₁Z(T)) = T. Its subgroup YT properly
contains T, so YT moves this omega-center. Two distinct maximal overgroups
would therefore give a core-free characteristic-two Goldschmidt triple in
the noncentral-omega branch. The proved local recognition identifies both
vertices with C₂ × S₄, contradicting the original 15.4.13 exclusion.

All noncentrality, quotient and transport premises are constructed from the
same two Inputs and original Sylow subgroup. Source: Aschbacher–Smith
15.4.12–15, printed pp.1160–1162.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open LocalSetup.TwoFactors.SingleOvergroup
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem input_omega_center_not_central {κ : GroupClass} (T : Sylow 2 G)
    {M Y : Subgroup G} (d : FamilySource.ModuleStructure.Input κ T M Y 1) :
    ¬ omegaOneCenterAmbient (T : Subgroup G) ≤
      centralizer ((Y ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
  intro hc
  have hn : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    d.sylow_le.trans ((normal_subgroupOf_iff_le_normalizer d.member_le).mp d.normal)
  have hi : (pCore 2 Y).index = 3 := by
    rw [Subgroup.index_eq_card]
    simpa only [pow_one] using d.quotient_card
  have hcomm : Y = ⁅Y, ChapterB.thompsonJ (T : Subgroup G) 0⁆ := by
    simpa only [ChapterB.thompsonJ_zero] using d.member.2
  have hindex := (single_factor_quotient T Y hn hi hcomm).1
  have hle : Y ⊔ (T : Subgroup G) ≤ (T : Subgroup G) :=
    (le_centralizer_iff.mp hc).trans_eq d.center_centralizer
  rw [le_antisymm hle le_sup_right, relIndex_self] at hindex
  omega

/-- The actual single-factor source Inputs have at most one maximal overgroup;
their centralizer equality supplies the noncentral-omega recognition internally. -/
theorem single_factor_overgroups_eq_noncentral {κ : GroupClass} (T : Sylow 2 G)
    {M₁ M₂ Y₁ Y₂ : Subgroup G}
    (d₁ : FamilySource.ModuleStructure.Input κ T M₁ Y₁ 1)
    (d₂ : FamilySource.ModuleStructure.Input κ T M₂ Y₂ 1)
    (hu₁ : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y₁ ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (hu₂ : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y₂ ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4) : M₁ = M₂ := by
  by_contra hne
  have hn₁ : M₁ ≤ normalizer (Y₁ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer d₁.member_le).mp d₁.normal
  have hn₂ : M₂ ≤ normalizer (Y₂ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer d₂.member_le).mp d₂.normal
  have hi₁ : (pCore 2 Y₁).index = 3 := by
    rw [Subgroup.index_eq_card]
    simpa only [pow_one] using d₁.quotient_card
  have hi₂ : (pCore 2 Y₂).index = 3 := by
    rw [Subgroup.index_eq_card]
    simpa only [pow_one] using d₂.quotient_card
  have hc₁ : Y₁ = ⁅Y₁, ChapterB.thompsonJ (T : Subgroup G) 0⁆ := by
    simpa only [ChapterB.thompsonJ_zero] using d₁.member.2
  have hc₂ : Y₂ = ⁅Y₂, ChapterB.thompsonJ (T : Subgroup G) 0⁆ := by
    simpa only [ChapterB.thompsonJ_zero] using d₂.member.2
  let A := Y₁ ⊔ (T : Subgroup G)
  let B := Y₂ ⊔ (T : Subgroup G)
  let I := A ⊔ B
  have hTI : (T : Subgroup G) ≤ I := le_sup_right.trans le_sup_left
  obtain ⟨hint, htriple, hcore, hA, hB⟩ := single_factor_goldschmidt T
    (d₁.ambient.evenCharacteristic T) d₁.maximal d₂.maximal d₁.sylow_le d₂.sylow_le
    d₁.member_le d₂.member_le hn₁ hn₂ hi₁ hi₂ hc₁ hc₂ hu₁ hu₂ hne
  have hint' : A.subgroupOf I ⊓ B.subgroupOf I = (T : Subgroup G).subgroupOf I := by
    change (A ⊓ B).subgroupOf I = _
    rw [hint]
  have hz : Nat.card (omegaOneCenterAmbient (A.subgroupOf I ⊓ B.subgroupOf I)) = 4 := by
    rw [hint', omega_center_card_subgroupOf hTI]
    exact hZ
  have move (P : Subgroup G) (hPI : P ≤ I)
      (hn : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer (P : Set G)) :
      ⁅P.subgroupOf I, omegaOneCenterAmbient (A.subgroupOf I ⊓ B.subgroupOf I)⁆ ≠ ⊥ := by
    intro hh
    apply omega_center_not_central_subgroupOf hTI hPI hn
    rw [hint'] at hh
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
  obtain ⟨⟨eA⟩, _⟩ := goldschmidt_identification_of_noncentral_omega htriple hcore hA hB
    (move A le_sup_left (input_omega_center_not_central T d₁))
    (move B le_sup_right (input_omega_center_not_central T d₂)) hz
  exact lemma_15_4_13 d₁.ambient T d₁.member
    ⟨(subgroupOfEquivOfLe (show A ≤ I from le_sup_left)).symm.trans eA⟩

end CFSG.Quasithin.Chapter15.Section04.InitialSource
