module

public import Theory.GroupTheory.SolvableNormalSup
public import Mathlib.GroupTheory.Index

/-!+# Solvability and index of a normalized subgroup product

If C normalizes A, their join is the product AC. Solvability of both
factors gives solvability of the join by the normal-subgroup extension
argument. If C is finite, the subgroup diamond gives [AC:C] = [A:A ∩ C].
Only C must be finite for the cancellation in that index calculation.

These elementary product arguments are used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, F.1.3(4) and the observation
S ∈ Syl₂(B) used in F.1.10(2), printed pp.260–262.
-/

public section

open Subgroup
variable {G : Type*} [Group G]

/-- A product of solvable subgroups is solvable when the second normalizes
the first; no ambient normality or finiteness is required. -/
theorem Group.isSolvable_sup_of_normalizes (A C : Subgroup G)
    [Group.IsSolvable A] [Group.IsSolvable C]
    (hn : C ≤ normalizer (A : Set G)) : Group.IsSolvable (A ⊔ C : Subgroup G) := by
  let N := A.subgroupOf (A ⊔ C)
  let D := C.subgroupOf (A ⊔ C)
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show A ≤ A ⊔ C from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show A ≤ A ⊔ C from le_sup_left)).injective
  let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show C ≤ A ⊔ C from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show C ≤ A ⊔ C from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top N D
  rw [← subgroupOf_sup (show A ≤ A ⊔ C from le_sup_left)
    (show C ≤ A ⊔ C from le_sup_right)]
  exact subgroupOf_self _

/-- The index of a finite normalizing factor in a subgroup product is the
index of the intersection in the normalized factor. -/
theorem Subgroup.relIndex_sup_of_normalizes (A C : Subgroup G) [Finite C]
    (hn : C ≤ normalizer (A : Set G)) : C.relIndex (A ⊔ C) = C.relIndex A := by
  let J := A ⊔ C
  let : (A.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have hindex := relIndex_sup_left (C.subgroupOf J) (A.subgroupOf J)
  rw [← subgroupOf_sup (show A ≤ J from le_sup_left) (show C ≤ J from le_sup_right),
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf (show C ≤ J from le_sup_right)] at hindex
  have h₁ := relIndex_mul_relIndex (C ⊓ A) C J inf_le_left le_sup_right
  have h₂ := relIndex_mul_relIndex (C ⊓ A) A J inf_le_right le_sup_left
  rw [inf_relIndex_left] at h₁
  rw [inf_relIndex_right, hindex] at h₂
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero
    (index_ne_zero_of_finite : A.relIndex C ≠ 0))
  exact h₁.trans (h₂.symm.trans (Nat.mul_comm _ _))
