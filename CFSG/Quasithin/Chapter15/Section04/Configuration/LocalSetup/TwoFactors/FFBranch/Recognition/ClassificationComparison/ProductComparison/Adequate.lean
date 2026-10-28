module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.SmallOrders
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate

/-!
# Product comparison from the adequate outer route

The order comparison for the F.6.18(2) row only uses the actual A₆ subgroup
inside the outer actor.  This extension keeps the literal ambient group and
the existing quotient hypotheses, while allowing the outer branch to carry
`ChapterB.OuterSixThreeShape` instead of the unavailable fixed-space fields.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace ProductComparison
open FFAlternatives

universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D} {K : GroupClass.{u}}
attribute [local instance] offenderSubgroup_normal

/-- The three product branches with the adequate group-only outer case. -/
def AdequateBranch {A : Type*} [Group A]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) A W) : Prop :=
  Nonempty (SourceTwoFactorCase σ) ∨
    Nonempty (ChapterB.OuterSixThreeShape A) ∨
    Nonempty (HyperplaneCase σ)

/-- The A₆ factor alone excludes the extraspecial order 108 row. -/
theorem adequate_outerSixThree_not_card_108
    (c : ChapterB.OuterSixThreeShape (offenderSubgroup ρ)) : Nat.card D ≠ 108 := by
  intro hd
  have hh := (Nat.card_le_card_of_injective c.first.subtype c.first.subtype_injective).trans
    (Nat.card_le_card_of_injective (offenderSubgroup ρ).subtype
      (offenderSubgroup ρ).subtype_injective)
  rw [Nat.card_congr c.firstEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hd]
    at hh
  norm_num [Nat.factorial] at hh

/-- Every adequate product branch excludes the extraspecial order 108 row. -/
theorem adequate_branch_not_card_108 (h : ClassifiedAction K ρ G₁ G₂)
    (hb : AdequateBranch (ρ.comp (offenderSubgroup ρ).subtype)) : Nat.card D ≠ 108 := by
  unfold AdequateBranch at hb
  rcases hb with hb | hb | hb <;> obtain ⟨hb⟩ := hb
  · exact sourceTwoFactor_not_card_108 h hb
  · exact adequate_outerSixThree_not_card_108 hb
  · exact hyperplane_not_card_108 hb

/-- The F.6.18(2) comparison remains valid for the adequate branch input. -/
theorem case2_equiv_of_adequate (h : ClassifiedAction K ρ G₁ G₂)
    (hb : AdequateBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (hr : GoldschmidtAlternatives.Case2 D) :
    Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  rcases hr with he | he
  · exact he
  · apply (adequate_branch_not_card_108 h hb ?_).elim
    rw [he.card, HeisenbergPrime.card]
    norm_num [GoldschmidtAlternatives.E4, GoldschmidtAlternatives.C, Nat.card_prod]

end ProductComparison
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
