module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# The norm image of a characteristic abelian subgroup of index two

For an abelian normal subgroup `A` and an element `t`, the norm on `A` sends
`a` to `a * (t * a * t⁻¹)`. At index two all outside elements induce the
same conjugation on `A`. Consequently, when `A` is characteristic, the norm
image is characteristic in the ambient group, independently of the chosen
representative of the outside coset.

This is the characteristic-subgroup device for analyzing the outside action
in Janko–Thompson, Math. Z. 113 (1970), results 1.3–1.4, printed p.386.
-/

namespace Subgroup

/-- Commuting with an index-two subgroup and one outside element implies centrality. -/
public theorem mem_center_of_commute_index_two
    {G : Type*} [Group G] (A : Subgroup G) (hi : A.index = 2)
    (t : G) (ht : t ∉ A) (z : G)
    (hA : ∀ a ∈ A, Commute z a) (htz : Commute z t) : z ∈ center G := by
  apply mem_center_iff.mpr
  intro g
  by_cases hg : g ∈ A
  · exact (hA g hg).eq.symm
  · have hgt : g * t⁻¹ ∈ A := (A.mul_mem_iff_of_index_two hi).mpr (by
      simp only [A.inv_mem_iff, hg, ht])
    have h := (hA _ hgt).mul_right htz
    simpa only [inv_mul_cancel_right] using h.eq.symm

/-- The square of an outside element of an abelian index-two subgroup is central. -/
public theorem sq_mem_center_of_not_mem_abelian_index_two
    {G : Type*} [Group G] (A : Subgroup G) [IsMulCommutative A]
    (hi : A.index = 2) (t : G) (ht : t ∉ A) : t ^ 2 ∈ center G := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  apply mem_center_of_commute_index_two A hi t ht
  · intro a ha
    exact congrArg Subtype.val (mul_comm (⟨t ^ 2, A.sq_mem_of_index_two hi t⟩ : A) ⟨a, ha⟩)
  · exact (Commute.refl t).pow_left 2

/-- The norm associated with conjugation on an abelian normal subgroup. -/
@[expose] public def abelianConjNorm {G : Type*} [Group G]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (t : G) : A →* G :=
  letI : CommGroup A := IsMulCommutative.instCommGroup
  A.subtype.comp ((MonoidHom.id A) * (MulAut.conjNormal t).toMonoidHom)

@[simp] public theorem abelianConjNorm_apply {G : Type*} [Group G]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (t : G) (a : A) :
    abelianConjNorm A t a = (a : G) * (t * a * t⁻¹) := rfl

/-- Multiplication by a base element changes the outside square by its norm. -/
public theorem mul_sq_eq_abelianConjNorm_mul_sq {G : Type*} [Group G]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (t : G) (a : A) :
    ((a : G) * t) ^ 2 = abelianConjNorm A t a * t ^ 2 := by
  rw [abelianConjNorm_apply]
  simp only [pow_two]
  group

/-- Conjugation on an abelian index-two subgroup is constant on the outside coset. -/
public theorem conj_eq_of_not_mem_abelian_index_two {G : Type*} [Group G]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (hi : A.index = 2)
    (t x : G) (ht : t ∉ A) (hx : x ∉ A) (a : G) (ha : a ∈ A) :
    x * a * x⁻¹ = t * a * t⁻¹ := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have htx : t⁻¹ * x ∈ A := (A.mul_mem_iff_of_index_two hi).mpr (by
    simp only [A.inv_mem_iff, ht, hx])
  have hcomm : Commute (t⁻¹ * x) a :=
    congrArg Subtype.val (mul_comm (⟨t⁻¹ * x, htx⟩ : A) ⟨a, ha⟩)
  calc
    x * a * x⁻¹ = t * ((t⁻¹ * x) * a * (t⁻¹ * x)⁻¹) * t⁻¹ := by group
    _ = t * a * t⁻¹ := by rw [hcomm.mul_inv_cancel]

/-- The norm image from the outside coset of a characteristic abelian
subgroup of index two is characteristic. -/
public theorem abelianConjNorm_range_characteristic {G : Type*} [Group G]
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A]
    (hi : A.index = 2) (t : G) (ht : t ∉ A) :
    (abelianConjNorm A t).range.Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro f x hx
  obtain ⟨a, rfl⟩ := hx
  have ha : f (a : G) ∈ A := characteristic_iff_le_comap.mp inferInstance f a.property
  have hft : f t ∉ A := by
    intro h
    have h' : f.symm (f t) ∈ A := characteristic_iff_le_comap.mp inferInstance f.symm h
    exact ht (by simpa using h')
  refine ⟨⟨f a, ha⟩, ?_⟩
  change (f (a : G)) * (t * f a * t⁻¹) = f ((a : G) * (t * a * t⁻¹))
  rw [map_mul, map_mul, map_mul, map_inv,
    conj_eq_of_not_mem_abelian_index_two A hi t (f t) ht hft _ ha]

end Subgroup
