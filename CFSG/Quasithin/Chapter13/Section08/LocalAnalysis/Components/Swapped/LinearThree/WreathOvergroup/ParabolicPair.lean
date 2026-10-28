module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# A marked pair of binary parabolics and its lift

This intermediate geometric interface records two commuting, disjoint S₄
subgroups of the actual H/O₂(H). Their product contains L₁*, and T* permutes
the two factors transitively. It records neither a wreath quotient nor an
automizer calculation. Its source producer must choose these subgroups from
the two moving PSL₃(2) components, including the compatibility with T.

The inverse image of ⟨P₁,P₂,T*⟩ is a solvable overgroup of L₁T in H. The
proof uses relative normalization and the solvable two-core kernel. No
normality in the ambient simple group is imposed.

Source: the construction in Aschbacher–Smith 13.8.16(1), printed p.952.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup
variable {G : Type*} [Group G]

/-- Intermediate geometry to be constructed from the marked PSL₃(2) factors.
The two equivalences refer to the literal embedded parabolic carriers. -/
structure ParabolicPair (H L₁ T : Subgroup G) where
  base_le : L₁ ⊔ T ≤ H
  two : IsPGroup 2 T
  left : Subgroup (Source.Hstar H)
  right : Subgroup (Source.Hstar H)
  leftEquiv : left ≃* Equiv.Perm (Fin 4)
  rightEquiv : right ≃* Equiv.Perm (Fin 4)
  disjoint : Disjoint left right
  commute : ∀ x ∈ left, ∀ y ∈ right, Commute x y
  seed_le : Source.starImage H L₁ ≤ left ⊔ right
  permutes : ∀ t ∈ Source.starImage H T,
    (left.map (MulAut.conj t).toMonoidHom = left ∧
      right.map (MulAut.conj t).toMonoidHom = right) ∨
    (left.map (MulAut.conj t).toMonoidHom = right ∧
      right.map (MulAut.conj t).toMonoidHom = left)
  moves : ∃ t ∈ Source.starImage H T,
    left.map (MulAut.conj t).toMonoidHom = right

namespace ParabolicPair
variable {H L₁ T : Subgroup G} (d : ParabolicPair H L₁ T)

/-- The generated subgroup in the actual two-core quotient. -/
def starOvergroup : Subgroup (Source.Hstar H) :=
  (d.left ⊔ d.right) ⊔ Source.starImage H T

/-- The chosen overgroup in the original ambient group. -/
def overgroup : Subgroup G :=
  (d.starOvergroup.comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype

theorem overgroup_le : d.overgroup ≤ H := map_subtype_le _

theorem base_le_overgroup : L₁ ⊔ T ≤ d.overgroup := by
  apply sup_le
  · intro x hx
    refine ⟨⟨x, (le_sup_left.trans d.base_le) hx⟩, ?_, rfl⟩
    apply (show d.left ⊔ d.right ≤ d.starOvergroup from le_sup_left)
    exact d.seed_le (mem_map_of_mem (QuotientGroup.mk' (pCore 2 H)) hx)
  · intro x hx
    refine ⟨⟨x, (le_sup_right.trans d.base_le) hx⟩, ?_, rfl⟩
    apply (show Source.starImage H T ≤ d.starOvergroup from le_sup_right)
    exact mem_map_of_mem (QuotientGroup.mk' (pCore 2 H)) hx

/-- The marked T-action normalizes the product, also when it swaps factors. -/
theorem normalizes_product : Source.starImage H T ≤
    normalizer ((d.left ⊔ d.right : Subgroup (Source.Hstar H)) : Set _) := by
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup]
  change d.left.map (MulAut.conj t).toMonoidHom ⊔
    d.right.map (MulAut.conj t).toMonoidHom = d.left ⊔ d.right
  rcases d.permutes t ht with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, sup_comm]

private theorem solvable_join_of_normalizes {X : Type*} [Group X]
    (A B : Subgroup X) [Group.IsSolvable A] [Group.IsSolvable B]
    (hn : B ≤ normalizer (A : Set X)) : Group.IsSolvable (A ⊔ B : Subgroup X) := by
  let A' := A.subgroupOf (A ⊔ B)
  let B' := B.subgroupOf (A ⊔ B)
  let _ : A'.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  let _ : Group.IsSolvable A' := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show A ≤ A ⊔ B from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show A ≤ A ⊔ B from le_sup_left)).injective
  let _ : Group.IsSolvable B' := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show B ≤ A ⊔ B from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ A ⊔ B from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top A' B'
  apply map_injective (A ⊔ B).subtype_injective
  simp [A', B', Subgroup.map_sup, le_sup_left, le_sup_right, ← MonoidHom.range_eq_map]

/-- The generated image is solvable, by normalization of its S₄ × S₄ base. -/
theorem starOvergroup_solvable [Finite G] : Group.IsSolvable d.starOvergroup := by
  let _ : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let _ : Group.IsSolvable d.left := Group.isSolvable_of_isSolvable_injective
    (f := d.leftEquiv.toMonoidHom) d.leftEquiv.injective
  let _ : Group.IsSolvable d.right := Group.isSolvable_of_isSolvable_injective
    (f := d.rightEquiv.toMonoidHom) d.rightEquiv.injective
  have hn : d.right ≤ normalizer (d.left : Set _) := by
    apply le_normalizer_iff.mpr
    intro y hy x hx
    have he : y * x * y⁻¹ = x := by rw [← (d.commute x hx y hy).eq]; simp
    rwa [he]
  let _ : Group.IsSolvable (d.left ⊔ d.right : Subgroup (Source.Hstar H)) :=
    solvable_join_of_normalizes _ _ hn
  have hT : IsPGroup 2 (Source.starImage H T) := by
    exact (d.two.comap_of_injective H.subtype H.subtype_injective).map _
  let _ := hT.isNilpotent
  exact solvable_join_of_normalizes _ _ d.normalizes_product

/-- Solvability survives the literal lift through O₂(H). -/
theorem overgroup_solvable [Finite G] : Group.IsSolvable d.overgroup := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let _ : Group.IsSolvable d.starOvergroup := d.starOvergroup_solvable
  have hk : IsPGroup 2 q.ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 H)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let _ := hk.isNilpotent
  let _ : Group.IsSolvable (d.starOvergroup.comap q) :=
    isSolvable_comap_of_solvable_ker q _
  exact Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective _)

end ParabolicPair
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup
end
