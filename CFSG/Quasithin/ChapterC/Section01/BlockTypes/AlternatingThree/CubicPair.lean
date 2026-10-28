module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.CubicProduct
public import Theory.GroupTheory.PCoreCommutingProduct
public import Theory.SpecificGroups.Alternating.FourPairResidual

/-!
# Two commuting cubic blocks

Two commuting A₃ blocks are disjoint because they are centerless. Their
multiplication map identifies the join with A₄ × A₄ and carries the embedded
two-core to the join of their original four-groups. The second theorem
constructs both blocks directly from their cubic actions on those four-groups.

Source: Aschbacher–Smith 13.5.6, printed p.917.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem alternatingThree_pair (X Y : Subgroup G)
    (hX : IsAlternatingBlock X 3) (hY : IsAlternatingBlock Y 3)
    (hc : X ≤ centralizer (Y : Set G)) :
    Disjoint X Y ∧ Nonempty ((X ⊔ Y : Subgroup G) ≃* AlternatingFourPair.Model) ∧
      (X ⊔ Y).pCoreIn 2 = X.pCoreIn 2 ⊔ Y.pCoreIn 2 := by
  have hd : Disjoint X Y := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hz : (⟨x,hx.1⟩ : X) ∈ center X :=
      mem_center_iff.mpr (fun y => Subtype.ext ((hc y.property x hx.2).symm))
    rw [hX.center_eq_bot,mem_bot] at hz
    exact congrArg Subtype.val hz
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting X Y hd hc
  obtain ⟨eX⟩ := hX.equiv_alternatingFour
  obtain ⟨eY⟩ := hY.equiv_alternatingFour
  exact ⟨hd,⟨e.symm.trans (eX.prodCongr eY)⟩,
    pCoreIn_sup_of_disjoint_of_commuting 2 X Y hd hc⟩

theorem cubic_pair_product (U₁ U₂ P₁ P₂ : Subgroup G)
    [IsElementaryAbelian 2 U₁] [IsElementaryAbelian 2 U₂]
    (hU₁ : Nat.card U₁=4) (hU₂ : Nat.card U₂=4)
    (hP₁ : Nat.card P₁=3) (hP₂ : Nat.card P₂=3)
    (hn₁ : P₁≤normalizer (U₁:Set G)) (hn₂ : P₂≤normalizer (U₂:Set G))
    (hm₁ : ⁅U₁,P₁⁆=U₁) (hm₂ : ⁅U₂,P₂⁆=U₂)
    (hc : U₁⊔P₁ ≤ centralizer ((U₂⊔P₂ : Subgroup G) : Set G)) :
    IsAlternatingBlock (U₁⊔P₁ : Subgroup G) 3 ∧
    IsAlternatingBlock (U₂⊔P₂ : Subgroup G) 3 ∧
    Nonempty (((U₁⊔U₂)⊔(P₁⊔P₂) : Subgroup G) ≃* AlternatingFourPair.Model) ∧
    ((U₁⊔U₂)⊔(P₁⊔P₂)).pCoreIn 2 = U₁⊔U₂ := by
  obtain ⟨ha₁,hq₁⟩ := alternatingThree_of_cubic_product U₁ P₁ hU₁ hP₁ hn₁ hm₁
  obtain ⟨ha₂,hq₂⟩ := alternatingThree_of_cubic_product U₂ P₂ hU₂ hP₂ hn₂ hm₂
  obtain ⟨_,he,hq⟩ := alternatingThree_pair _ _ ha₁ ha₂ hc
  have hs : (U₁⊔P₁)⊔(U₂⊔P₂) = (U₁⊔U₂)⊔(P₁⊔P₂) := by ac_rfl
  change (U₁⊔P₁).pCoreIn 2=U₁ at hq₁
  change (U₂⊔P₂).pCoreIn 2=U₂ at hq₂
  rw [hs] at he hq
  exact ⟨ha₁,ha₂,he,hq.trans (congrArg₂ (· ⊔ ·) hq₁ hq₂)⟩
end CFSG.Quasithin.ChapterC
