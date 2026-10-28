module
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.PrimeOrderClosure
public import Mathlib.GroupTheory.Solvable

/-!
# Cubic generation through a two-group kernel

An order-three element has an order-three lift through a surjective map
with two-group kernel: choose a two-regular lift and compare its cube with
the kernel. Thus the cubic-generated subgroups map onto one another, and
solvability passes to the image. Injective transport supplies the companion
subgroup statement. These are the quotient steps used in the original
symplectic branch of Aschbacher–Smith 15.3.20.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H] [Finite G]

private theorem cubic_lift (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (y : H) (hy : orderOf y = 3) :
    ∃ x : G, f x = y ∧ orderOf x = 3 := by
  obtain ⟨x,hodd,he⟩ := f.exists_pRegular_lift hf 2 Nat.prime_two y (by rw [hy]; decide)
  have hc : x^3 ∈ f.ker := by
    change f (x^3) = 1
    rw [map_pow,he,←hy]
    exact pow_orderOf_eq_one y
  let z : f.ker := ⟨x^3,hc⟩
  have hd : orderOf z ∣ orderOf x := by
    rw [←Subgroup.orderOf_coe z]
    exact orderOf_pow_dvd 3
  have hcop := hk.orderOf_coprime (Nat.prime_two.coprime_iff_not_dvd.mpr hodd) z
  have hz : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hd
  have hx3 : x^3 = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp hz)
  have hxne : x ≠ 1 := by
    intro hh
    have hyone : y = 1 := he.symm.trans (hh ▸ f.map_one)
    simp [hyone] at hy
  exact ⟨x,he,orderOf_eq_prime hx3 hxne⟩

/-- Cubic generation passes through a surjection with two-group kernel. -/
theorem cubic_closure_map_of_two_kernel (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) :
    (closure {x : G | orderOf x = 3}).map f = closure {y : H | orderOf y = 3} := by
  apply le_antisymm
  · rw [MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro y ⟨x,hx,rfl⟩
    have hd : orderOf (f x) ∣ 3 := hx ▸ orderOf_map_dvd f x
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · rw [orderOf_eq_one_iff.mp h1]
      exact one_mem _
    · exact subset_closure h3
  · apply (closure_le _).mpr
    intro y hy
    obtain ⟨x,hxy,hx⟩ := cubic_lift f hf hk y hy
    exact ⟨x,subset_closure hx,hxy⟩

/-- A two-kernel quotient preserves solvability of the cubic-generated subgroup. -/
theorem solvable_cubic_closure_of_two_kernel (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hs : Group.IsSolvable (closure {x : G | orderOf x = 3})) :
    Group.IsSolvable (closure {y : H | orderOf y = 3}) := by
  let := hs
  rw [←cubic_closure_map_of_two_kernel f hf hk]
  exact Group.isSolvable_of_surjective (f.subgroupMap_surjective _)

omit [Finite G] in
/-- Cubic-closure solvability descends along an injective homomorphism. -/
theorem solvable_cubic_closure_of_injective (f : G →* H) (hf : Function.Injective f)
    (hs : Group.IsSolvable (closure {y : H | orderOf y = 3})) :
    Group.IsSolvable (closure {x : G | orderOf x = 3}) := by
  have hle : closure {x : G | orderOf x = 3} ≤
      (closure {y : H | orderOf y = 3}).comap f := by
    apply (closure_le _).mpr
    intro x hx
    exact subset_closure ((orderOf_injective f hf x).trans hx)
  let j : closure {x : G | orderOf x = 3} →* closure {y : H | orderOf y = 3} :=
    (f.comp (closure {x : G | orderOf x = 3}).subtype).codRestrict _
    (fun x => hle x.property)
  let := hs
  exact Group.isSolvable_of_isSolvable_injective (f := j)
    (fun x y hh => Subtype.ext (hf (congrArg Subtype.val hh)))
end Theory.GroupTheory
