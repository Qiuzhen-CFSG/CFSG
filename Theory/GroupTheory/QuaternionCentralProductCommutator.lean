module
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

/-!
# Central differences on quaternion central-product factors

For commuting subgroups B,C with B quaternion and intersection of order two,
conjugation by any element of B joined with C changes an element of B only
by an element of the shared intersection. No finiteness of the ambient group
is required.

Write the conjugating element as a product a*c with a in B and c in C.
The C component centralizes B. In the quaternion factor, the remaining
conjugation difference is the identity or its unique involution, as checked
by kernel reduction in Q8. The order-two intersection supplies exactly this
involution in the actual ambient group.

This transfers inner conjugation differences to the finite factor action
used to select invariant diagonals in Stellmacher (9.1), Journal of
Algebra190 (1997), p.48. It also proves normalization of these diagonals
by their central product.
-/

open scoped Pointwise
namespace Subgroup

/-- Inner action of the central product on a quaternion factor is trivial
modulo its shared order-two intersection. -/
public theorem factor_central_difference_of_mem_sup
    {G : Type*} [Group G] (B C : Subgroup G)
    (model : B ≃* QuaternionGroup 2)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (v : G) (hv : v ∈ B ⊔ C) (b : G) (hb : b ∈ B) :
    b⁻¹*(v*b*v⁻¹) ∈ B ⊓ C := by
  have hBCn : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro a ha c hc
    exact (hcomm a ha c hc).symm
  have hv' : v ∈ (B : Set G)*(C : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right B C hBCn]
    exact hv
  obtain ⟨a, ha, c, hc, rfl⟩ := hv'
  have heq : b⁻¹*((a*c)*b*(a*c)⁻¹) = b⁻¹*(a*b*a⁻¹) := by
    have hh : c*b*c⁻¹=b := by rw [← hcomm b hb c hc, mul_inv_cancel_right]
    calc
      b⁻¹*((a*c)*b*(a*c)⁻¹) = b⁻¹*(a*(c*b*c⁻¹)*a⁻¹) := by group
      _ = b⁻¹*(a*b*a⁻¹) := by rw [hh]
  rw [heq]
  obtain ⟨z,hzne,_⟩ := (Nat.card_eq_two_iff' (1 : (B ⊓ C : Subgroup G))).mp hinter
  have hzG : (z:G) ≠ 1 := fun hh => hzne (Subtype.ext hh)
  have hz2 : (z:G)^2=1 := by
    have hh := pow_card_eq_one' (x := z)
    rw [hinter] at hh
    exact congrArg Subtype.val hh
  let zz : B := ⟨z,z.property.1⟩
  let aa : B := ⟨a,ha⟩
  let bb : B := ⟨b,hb⟩
  have hzmodel : model zz ≠ 1 := by
    intro hh
    exact hzG (congrArg Subtype.val (model.injective (hh.trans model.map_one.symm)))
  have hzsq : (model zz)^2=1 := by
    rw [← map_pow]
    have hh : zz^2=1 := Subtype.ext hz2
    rw [hh,map_one]
  have hfinite : ∀ z : QuaternionGroup 2, z ≠ 1 → z^2=1 →
      ∀ a b : QuaternionGroup 2, b⁻¹*(a*b*a⁻¹)=1 ∨ b⁻¹*(a*b*a⁻¹)=z := by decide
  have hh := hfinite (model zz) hzmodel hzsq (model aa) (model bb)
  have hm : model (bb⁻¹*(aa*bb*aa⁻¹)) = (model bb)⁻¹*((model aa)*(model bb)*(model aa)⁻¹) := by simp
  rcases hh with hh | hh
  · have hh' : bb⁻¹*(aa*bb*aa⁻¹)=1 := model.injective (hm.trans (hh.trans model.map_one.symm))
    have hhG : b⁻¹*(a*b*a⁻¹)=1 := congrArg Subtype.val hh'
    rw [hhG]
    exact one_mem _
  · have hh' : bb⁻¹*(aa*bb*aa⁻¹)=zz := model.injective (hm.trans hh)
    have hhG : b⁻¹*(a*b*a⁻¹)=(z:G) := congrArg Subtype.val hh'
    rw [hhG]
    exact z.property
end Subgroup
