module
public import Theory.GroupTheory.CComponent.RadicalKernel

/-!
A nonsolvable subgroup of a C-component fills its image whenever that image
is normal. The preimage of the smaller image is a normal subgroup of the
component; a proper such subgroup is solvable.
Source application: Aschbacher–Smith9.4.1, printed p.735.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

theorem cComponent_map_eq_of_normal_image
    {E : Type*} [Group E] (K B : Subgroup H) (hK : K.IsCComponent)
    (hBK : B ≤ K) (hB : ¬ Group.IsSolvable B) (f : H →* E)
    [(B.map f).Normal] : K.map f = B.map f := by
  let N := ((B.map f).comap f).subgroupOf K
  let : N.Normal := inferInstance
  have hBN : ∀ b : B, inclusion hBK b ∈ N := fun b => mem_map_of_mem f b.property
  have htop : N = ⊤ := by
    by_contra hn
    let : Group.IsSolvable N := hK.isSolvable_of_subnormal_lt_top
      (inferInstance : N.Normal).isSubnormal hn
    let j : B →* N := (inclusion hBK).codRestrict N hBN
    exact hB (Group.isSolvable_of_isSolvable_injective (f := j)
      (fun a b hab => inclusion_injective hBK (congrArg Subtype.val hab)))
  apply le_antisymm ?_ (map_mono hBK)
  rintro _ ⟨k,hk,rfl⟩
  exact (show (⟨k,hk⟩ : K) ∈ N from htop.symm ▸ mem_top _)

end Theory.GroupTheory
