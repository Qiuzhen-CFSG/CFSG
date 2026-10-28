module
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure

/-!
# Sylow-normalized two-perfect subgroups at index three

A p-perfect subgroup normalized by a p-subgroup of index three is either
trivial or the entire p-residual. In the nontrivial case it cannot lie in
the p-subgroup. The two subgroups therefore generate the group, making
the p-perfect subgroup normal with p-group quotient.

This is the residual-image argument for a point parabolic in the natural
A6 module in Aschbacher--Smith 13.3.9, printed p.887.
-/
public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G]

private theorem trivial_of_pPerfect_in_pGroup {p:ℕ} (N S:Subgroup G)
    (hN:IsPPerfect p N) (hS:IsPGroup p S) (hle:N≤S) : N=⊥ := by
  have hp:=hS.to_le hle
  have he:(⊥:Subgroup N)=⊤ := hN _ inferInstance
    (hp.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective _))
  apply eq_bot_iff.mpr
  intro n hn
  exact congrArg Subtype.val (mem_bot.mp
    (show (⟨n,hn⟩:N)∈(⊥:Subgroup N) from he.symm ▸ mem_top _))

theorem eq_bot_or_residual_of_index_three {p:ℕ} (S N:Subgroup G)
    (hS:IsPGroup p S) (hi:S.index=3)
    (hN:IsPPerfect p N) (hn:S≤normalizer (N:Set G)) :
    N=⊥ ∨ N=pResidual p G := by
  by_cases hle:N≤S
  · exact Or.inl (trivial_of_pPerfect_in_pGroup N S hN hS hle)
  right
  have hgen:N⊔S=⊤ := by
    rcases (isCoatom_of_index_three S hi).le_iff.mp
      (show S≤N⊔S from le_sup_right) with hh|hh
    · exact hh
    · exact (hle (le_sup_left.trans hh.le)).elim
  let : N.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸ sup_le N.le_normalizer hn))
  exact (pResidual_eq_of_isPPerfect_sup N S hN hS hgen).symm
end Subgroup
