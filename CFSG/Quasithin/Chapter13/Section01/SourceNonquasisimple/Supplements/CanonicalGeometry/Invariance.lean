module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Basic
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Invariance of the actual radical supplements

Inside BT, the normal subgroup L intersect BT is the product of B with
the intersection of O∞(L). Its quotient image is therefore normal.
Reflection of C-component normality through that solvable kernel proves
that T normalizes B. Normality of L is needed only relative to LT.

Source: Aschbacher--Smith 13.1.9, first proof paragraph, printed p.869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter1.RadicalNormalizers
variable {G : Type*} [Group G] [Finite G]

/-- Every actual radical supplement of a T-invariant local component
is itself T-invariant. -/
theorem supplement_invariant {T L B : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G))
    (hB : B ∈ radicalSupplements T L) : T ≤ normalizer (B : Set G) := by
  let W := B ⊔ T
  let D := (solvableRadical L).map L.subtype
  have hBL : B ≤ L := hB.2 ▸ le_sup_right
  have hDL : D ≤ L := map_subtype_le _
  have hWL : W ≤ normalizer (L : Set G) := sup_le (hBL.trans L.le_normalizer) hTL
  have hWD : W ≤ normalizer (D : Set G) :=
    hWL.trans (normalizer_le_normalizer_characteristic_image L (solvableRadical L))
  let D' := D.subgroupOf W
  let B' := B.subgroupOf W
  let I := L.subgroupOf W
  let : D'.Normal := normal_subgroupOf_of_le_normalizer hWD
  let : I.Normal := normal_subgroupOf_of_le_normalizer hWL
  let : Group.IsSolvable D := Group.isSolvable_of_surjective
    (f := L.subtype.subgroupMap (solvableRadical L))
    (L.subtype.subgroupMap_surjective (solvableRadical L))
  let : Group.IsSolvable D' := Group.isSolvable_of_isSolvable_injective
    (f := W.subtype.subgroupComap D)
    (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun d : D => (d : G)) h)))
  have hIB : D' ⊔ B' = I := by
    apply le_antisymm (sup_le (comap_mono hDL) (comap_mono hBL))
    intro x hx
    have hx' : (x : G) ∈ D ⊔ B := hB.2.symm ▸ hx
    obtain ⟨d,hd,b,hb,he⟩ :=
      (coe_mul_of_right_le_normalizer_left D B (le_sup_left.trans hWD)).subset hx'
    have hdW : d ∈ W := by
      have := W.mul_mem x.property (W.inv_mem (show b ∈ W from mem_sup_left hb))
      simpa only [← he,mul_inv_cancel_right] using this
    have heW : (⟨d,hdW⟩ : W) * ⟨b,mem_sup_left hb⟩ = x := Subtype.ext he
    rw [← heW]
    exact (D' ⊔ B').mul_mem (mem_sup_left hd) (mem_sup_right hb)
  let q := QuotientGroup.mk' D'
  have hi : I.map q = B'.map q := by
    rw [← hIB,Subgroup.map_sup]
    simp only [q,QuotientGroup.map_mk'_self,bot_sup_eq]
  have hn : (B'.map q).Normal := hi ▸
    (inferInstance : I.Normal).map q (QuotientGroup.mk'_surjective D')
  have hbN : B'.Normal := cComponent_normal_of_quotient_normal hB.1.1 D' hn
  have hnW : W ≤ normalizer (B : Set G) := by
    exact (normal_subgroupOf_iff_le_normalizer le_sup_left).mp hbN
  exact le_sup_right.trans hnW
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
