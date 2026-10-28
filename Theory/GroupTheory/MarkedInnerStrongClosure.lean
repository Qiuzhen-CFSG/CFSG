module

public import Theory.GroupTheory.SetStrongClosure
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Strong closure and a marked inner involution

Write the original involution as `z = f(t)c`, where `f` embeds a centerless
component and `c` centralizes its image. Centrality of z on the actual Sylow
places the order-two implementer t in the component Sylow. Each component
conjugate a of t returning to that Sylow forces f(a)c into U. Abelianness of
U then forces every two such a to commute. U need not lie in the component,
and neither t nor c is assumed to lie in U.

This is the fusion obstruction for Aschbacher--Smith 1.1.5(3)(e), used in
the Bender inspection on printed pp.519--520.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.MarkedInnerStrongClosure
variable {G K : Type*} [Group G] [Group K]

/-- Fusion of the original marked involution forces its component
implementer's conjugates in the component Sylow to commute. -/
theorem conjugates_commute (S U : Subgroup G) [IsMulCommutative U]
    (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (f : K →* G) (hf : Function.Injective f) (hcK : center K = ⊥)
    (P : Sylow 2 K) (hPS : (P : Subgroup K).map f ≤ S)
    (z : G) (hzU : z ∈ U) (hz2 : z ^ 2 = 1)
    (hzc : ∀ s ∈ S, Commute z s)
    (t : K) (haction : ∀ x : K, f (t * x * t⁻¹) = z * f x * z⁻¹)
    (a b : K) (haP : a ∈ P) (hbP : b ∈ P)
    (ha : IsConj t a) (hb : IsConj t b) : Commute a b := by
  have ht2 : t ^ 2 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot hcK
    apply MulEquiv.ext
    intro x
    apply hf
    simp only [MulAut.conj_apply, one_mul, inv_one, mul_one]
    calc
      _ = f (t * (t * x * t⁻¹) * t⁻¹) := by simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = z * (z * f x * z⁻¹) * z⁻¹ := by rw [haction, haction]
      _ = z ^ 2 * f x * (z ^ 2)⁻¹ := by simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = f x := by rw [hz2]; simp
  have htP : t ∈ P := (MulAut.involution_mem_sylow_of_centralizes P t ht2
    (fun x hx => hf (by
      change f (t * x * t⁻¹) = f x
      rw [haction, (hzc (f x) (hPS (mem_map_of_mem f hx))).eq]
      simp only [mul_assoc, mul_inv_cancel, mul_one]))).1
  let c : G := (f t)⁻¹ * z
  have hcS : c ∈ S := S.mul_mem (S.inv_mem (hPS (mem_map_of_mem f htP))) (hU.1 hzU)
  have hcf (x : K) : Commute c (f x) := by
    apply mul_inv_eq_iff_eq_mul.mp
    change ((f t)⁻¹ * z) * f x * ((f t)⁻¹ * z)⁻¹ = f x
    calc
      _ = (f t)⁻¹ * (z * f x * z⁻¹) * f t := by group
      _ = (f t)⁻¹ * f (t * x * t⁻¹) * f t := by rw [haction]
      _ = f x := by simp only [map_mul, map_inv]; group
  have hz : z = f t * c := by dsimp [c]; group
  have hforced (a : K) (haP : a ∈ P) (ha : IsConj t a) : f a * c ∈ U := by
    obtain ⟨g, hg⟩ := isConj_iff.mp ha
    have he : f g * z * (f g)⁻¹ = f a * c := by
      rw [hz]
      calc
        _ = f g * f t * (c * (f g)⁻¹) := by group
        _ = f g * f t * ((f g)⁻¹ * c) := by rw [(hcf g).inv_right.eq]
        _ = f (g * t * g⁻¹) * c := by simp only [map_mul, map_inv]; group
        _ = f a * c := by rw [hg]
    have hs : f a * c ∈ S := S.mul_mem (hPS (mem_map_of_mem f haP)) hcS
    have hu := hU.2 z hzU (f g)⁻¹ (mem_top _) (by simpa only [inv_inv, he] using hs)
    change f a * c ∈ (U : Set G)
    simpa only [inv_inv, he] using hu
  have hh := congrArg Subtype.val
    (mul_comm (⟨f a * c, hforced a haP ha⟩ : U) ⟨f b * c, hforced b hbP hb⟩)
  change (f a * c) * (f b * c) = (f b * c) * (f a * c) at hh
  have he : f a * f b * (c * c) = f b * f a * (c * c) := by
    calc
      _ = (f a * c) * (f b * c) := ((hcf b).mul_mul_mul_comm (f a) c).symm
      _ = (f b * c) * (f a * c) := hh
      _ = f b * f a * (c * c) := (hcf a).mul_mul_mul_comm (f b) c
  exact hf (by simpa only [map_mul] using mul_right_cancel he)

/-- A single involution class with noncommuting involutions in the component
Sylow excludes a nontrivial marked inner action. -/
theorem false_of_involution_fusion (S U : Subgroup G) [IsMulCommutative U]
    (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (f : K →* G) (hf : Function.Injective f) (hcK : center K = ⊥)
    (P : Sylow 2 K) (hPS : (P : Subgroup K).map f ≤ S)
    (z : G) (hzU : z ∈ U) (hz2 : z ^ 2 = 1)
    (hzc : ∀ s ∈ S, Commute z s)
    (t : K) (ht : t ≠ 1)
    (haction : ∀ x : K, f (t * x * t⁻¹) = z * f x * z⁻¹)
    (hclass : ∀ a b : K, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (hpair : ∃ a b : P, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬Commute a b) : False := by
  have ht2 : t ^ 2 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot hcK
    apply MulEquiv.ext
    intro x
    apply hf
    simp only [MulAut.conj_apply, one_mul, inv_one, mul_one]
    calc
      _ = f (t * (t * x * t⁻¹) * t⁻¹) := by simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = z * (z * f x * z⁻¹) * z⁻¹ := by rw [haction, haction]
      _ = z ^ 2 * f x * (z ^ 2)⁻¹ := by simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = f x := by rw [hz2]; simp
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht
  obtain ⟨a, b, ha, hb, hab⟩ := hpair
  have ha' : orderOf (a : K) = 2 := by simpa only [Subgroup.orderOf_coe] using ha
  have hb' : orderOf (b : K) = 2 := by simpa only [Subgroup.orderOf_coe] using hb
  exact hab (Subtype.ext (conjugates_commute S U hU f hf hcK P hPS z hzU hz2 hzc
    t haction a b a.property b.property (hclass t a hto ha') (hclass t b hto hb')).eq)

end Theory.GroupTheory.MarkedInnerStrongClosure
