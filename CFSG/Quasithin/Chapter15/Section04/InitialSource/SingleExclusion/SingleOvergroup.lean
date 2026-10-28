module

public import CFSG.Quasithin.Chapter15.Section04.InitialSource.SingleExclusion
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup

/-!
# The single-factor application of 15.4.13

Two actual single-factor inputs provide the normality, quotient order and
Thompson saturation needed for the Goldschmidt argument. The full F.6.5
classification, source uniqueness and the preceding central order-four
result identify a forbidden `S₂ × S₄` subgroup if their maximal overgroups
differ. Lemma 15.4.13 therefore makes those overgroups equal.

Aschbacher–Smith, *The Classification of Quasithin Groups*, 15.4.15,
printed pp.1161–1162.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual single-factor Inputs have at most one maximal two-local
overgroup. The full F.6.5 theorem and preceding order-four assertion are
retained as their exact independent source inputs. -/
theorem single_factor_overgroups_eq {κ : GroupClass} (T : Sylow 2 G)
    {M₁ M₂ Y₁ Y₂ : Subgroup G}
    (d₁ : FamilySource.ModuleStructure.Input κ T M₁ Y₁ 1)
    (d₂ : FamilySource.ModuleStructure.Input κ T M₂ Y₂ 1)
    (hu₁ : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y₁⊔(T:Subgroup G)≤M → M=M₁)
    (hu₂ : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y₂⊔(T:Subgroup G)≤M → M=M₂)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T:Subgroup G))=4)
    (classification : LocalSetup.TwoFactors.SingleOvergroup.GoldschmidtClassification.{u}) : M₁=M₂ := by
  by_contra hne
  have hn₁ : M₁≤normalizer (Y₁:Set G) :=
    (normal_subgroupOf_iff_le_normalizer d₁.member_le).mp d₁.normal
  have hn₂ : M₂≤normalizer (Y₂:Set G) :=
    (normal_subgroupOf_iff_le_normalizer d₂.member_le).mp d₂.normal
  have hi₁ : (pCore 2 Y₁).index=3 := by rw [Subgroup.index_eq_card]; simpa only [pow_one] using d₁.quotient_card
  have hi₂ : (pCore 2 Y₂).index=3 := by rw [Subgroup.index_eq_card]; simpa only [pow_one] using d₂.quotient_card
  have hc₁ : Y₁=⁅Y₁,ChapterB.thompsonJ (T:Subgroup G) 0⁆ := by
    simpa only [ChapterB.thompsonJ_zero] using d₁.member.2
  have hc₂ : Y₂=⁅Y₂,ChapterB.thompsonJ (T:Subgroup G) 0⁆ := by
    simpa only [ChapterB.thompsonJ_zero] using d₂.member.2
  have hid:=LocalSetup.TwoFactors.SingleOvergroup.single_factor_identifications (Y₁:=Y₁) (Y₂:=Y₂) (M₁:=M₁) (M₂:=M₂) classification T
    (d₁.ambient.evenCharacteristic T) d₁.maximal d₂.maximal d₁.sylow_le d₂.sylow_le
    d₁.member_le d₂.member_le hn₁ hn₂ hi₁ hi₂ hc₁ hc₂ hu₁ hu₂ hZ hne
  exact lemma_15_4_13 d₁.ambient T d₁.member hid.1

end CFSG.Quasithin.Chapter15.Section04.InitialSource
