module

public import Theory.GroupTheory.SolvableNormalSup
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.Order.Minimal
public import Mathlib.Data.SetLike.Fintype

/-!
# The solvable radical of a finite group

The solvable radical is the join of the normal solvable subgroups. It is
characteristic, and in a finite group it is solvable. For the latter assertion,
choose a maximal normal solvable subgroup: joining it with any other normal
solvable subgroup is still solvable, so maximality makes it the radical.

This is the usual O_∞(G), not the terminal derived subgroup G^∞.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, notation
preceding Proposition A.3.3, pp. 41–42, and the elementary extension theorem
for solvable groups.
-/

@[expose] public section
open Subgroup

/-- The join of two solvable subgroups is solvable if the first is normal. -/
theorem Group.isSolvable_sup_of_normal_left {G : Type*} [Group G] (H K : Subgroup G) [H.Normal]
    [Group.IsSolvable H] [Group.IsSolvable K] : Group.IsSolvable (H ⊔ K : Subgroup G) := by
  let A := H.subgroupOf (H ⊔ K)
  let B := K.subgroupOf (H ⊔ K)
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe (show H ≤ H ⊔ K from le_sup_left)).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe (show H ≤ H ⊔ K from le_sup_left)).injective
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe (show K ≤ H ⊔ K from le_sup_right)).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe (show K ≤ H ⊔ K from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top A B
  apply (Subgroup.map_injective (H ⊔ K).subtype_injective)
  simp [A, B, Subgroup.map_sup, le_sup_left, le_sup_right, ← MonoidHom.range_eq_map]


namespace Subgroup
variable {G : Type*} [Group G]
/-- The solvable radical, the join of all normal solvable subgroups. -/
def solvableRadical (G : Type*) [Group G] : Subgroup G :=
  sSup {K : Subgroup G | K.Normal ∧ Group.IsSolvable K}
instance solvableRadical_characteristic : (solvableRadical G).Characteristic := by
  apply characteristic_iff_map_le.mpr
  intro e
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro H ⟨hn, hs⟩
  apply map_le_iff_le_comap.mp
  let := hs
  exact le_sSup ⟨Normal.map hn _ e.surjective,
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)⟩

instance solvableRadical_normal : (solvableRadical G).Normal := inferInstance

/-- Every normal solvable subgroup lies in the solvable radical. -/
theorem le_solvableRadical (K : Subgroup G) (hn : K.Normal)
    (hs : Group.IsSolvable K) : K ≤ solvableRadical G := le_sSup ⟨hn, hs⟩

instance solvableRadical_isSolvable [Finite G] : Group.IsSolvable (solvableRadical G) := by
  obtain ⟨R, ⟨hn, hs⟩, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun K : Subgroup G => K.Normal ∧ Group.IsSolvable K)
    ⟨⊥, inferInstance, inferInstance⟩
  let := hn
  let := hs
  have he : solvableRadical G = R := by
    apply le_antisymm _ (le_solvableRadical R hn hs)
    apply sSup_le
    intro K hK
    let := hK.1
    let := hK.2
    exact le_sup_right.trans (hmax ⟨inferInstance, Group.isSolvable_sup_of_normal_left R K⟩ le_sup_left)
  rwa [he]

end Subgroup
