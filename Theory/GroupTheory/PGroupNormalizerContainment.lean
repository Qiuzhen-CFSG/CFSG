module
public import Theory.PGroupCore
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# Containment from a normalizer intersection in a p-group

If R normalizes P and P∩N(R)≤R, the p-group RP has R self-normalizing.
The nilpotent normalizer condition forces RP=R and hence P≤R.
This preserves the original ambient subgroups and their actual normalizer.

Source application: Aschbacher–Smith, Lemma 2.4.11, printed p.531.
-/
public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem le_of_normalized_pGroup_inf_normalizer_le {p : ℕ} [Fact p.Prime]
    (R P : Subgroup G) (hR : IsPGroup p R) (hP : IsPGroup p P)
    (hRP : R ≤ normalizer (P : Set G))
    (hN : P ⊓ normalizer (R : Set G) ≤ R) : P ≤ R := by
  let J := R ⊔ P
  have hJ : IsPGroup p J := hR.to_sup_of_normal_right' hP hRP
  let : Group.IsNilpotent J := hJ.isNilpotent
  have hself : normalizer (R.subgroupOf J : Set J)=R.subgroupOf J := by
    apply le_antisymm ?_ le_normalizer
    intro x hx
    have hxN : (x:G) ∈ normalizer (R : Set G) := by
      rw [←subgroupOf_normalizer_eq (show R≤J from le_sup_left)] at hx
      exact hx
    have hp : (x:G) ∈ (R:Set G)*(P:Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right R P hRP]
      exact x.property
    obtain ⟨r,hr,y,hy,he⟩ := hp
    change r*y=(x:G) at he
    have hyN : y ∈ normalizer (R : Set G) := by
      have heN : r*y ∈ normalizer (R : Set G) := he.symm ▸ hxN
      exact ((normalizer (R:Set G)).mul_mem_cancel_left (R.le_normalizer hr)).mp heN
    change (x:G) ∈ R
    exact he ▸ R.mul_mem hr (hN ⟨hy,hyN⟩)
  have htop : R.subgroupOf J=⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G:=J))) _ hself
  exact le_sup_right.trans (subgroupOf_eq_top.mp htop)
end Subgroup
