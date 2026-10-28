module

public import Theory.GroupTheory.CyclicNormRetraction
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Perm.Fin

/-!
# A normal complement from the cubic norm

Let a finite group map onto S₃ with abelian two-group kernel. If every kernel
element fixed by a lift of a three-cycle is central, the kernel has an ambient
normal complement to its central part.

Conjugation on the kernel factors through the literal S₃ map. The cubic norm
commutes with this action, since conjugation either fixes or inverts the
three-cycle. Its image is central, so the norm is invariant under the entire
ambient group and its kernel is normal. On central elements it is cubing;
cubing is invertible in a two-group, giving the complement. No exponent-two
hypothesis on the kernel is used.

This is the splitting step in the first M₁₂ parabolic's derived-kernel
calculation, used for Aschbacher–Smith I.1.3(1), printed p.407.
-/

open Subgroup
open scoped IsMulCommutative
namespace Subgroup
noncomputable section

private theorem cubicNorm_equivariant {N : Type*} [CommGroup N]
    (a b : MulAut N) (ha : a ^ 3 = 1)
    (hab : a * b = b * a ∨ a * b = b * a ^ 2) (x : N) :
    MulAut.cyclicNorm a 3 (b x) = b (MulAut.cyclicNorm a 3 x) := by
  have hn (y : N) : MulAut.cyclicNorm a 3 y = y * a y * (a ^ 2) y := by
    simp [MulAut.cyclicNorm_apply, Finset.prod_range_succ]
  rw [hn, hn, map_mul, map_mul]
  rcases hab with hab | hab
  · have h1 : a (b x) = b (a x) := congrArg (fun c : MulAut N => c x) hab
    have h2 : (a ^ 2) (b x) = b ((a ^ 2) x) := by
      have he : a ^ 2 * b = b * a ^ 2 := by
        rw [pow_two, mul_assoc, hab, ← mul_assoc, hab, mul_assoc]
      exact congrArg (fun c : MulAut N => c x) he
    rw [h1,h2]
  · have h1 : a (b x) = b ((a ^ 2) x) := congrArg (fun c : MulAut N => c x) hab
    have hfour : a ^ 2 * a ^ 2 = a := by
      rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_add, ha, one_mul, pow_one]
    have h2 : (a ^ 2) (b x) = b (a x) := by
      have he : a ^ 2 * b = b * a := by
        calc
          a ^ 2 * b = a * (a * b) := by rw [pow_two, mul_assoc]
          _ = a * (b * a ^ 2) := by rw [hab]
          _ = b * (a ^ 2 * a ^ 2) := by rw [← mul_assoc, hab, mul_assoc]
          _ = b * a := by rw [hfour]
      exact congrArg (fun c : MulAut N => c x) he
    rw [h1,h2]
    ac_rfl

/-- Cubic averaging constructs an ambient normal complement to the central
part of an abelian two-group kernel over S₃. -/
public theorem exists_normal_complement_of_cubic_fixed_central
    {E : Type*} [Group E] [Finite E]
    (f : E →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hab : IsMulCommutative f.ker) (hp : IsPGroup 2 f.ker)
    (t : E) (ht : f t = List.formPerm [0,2,1])
    (hfixed : ∀ x ∈ f.ker, Commute t x → x ∈ center E) :
    ∃ U : Subgroup E, U.Normal ∧ U ≤ f.ker ∧
      Disjoint U (center E) ∧ f.ker ≤ U ⊔ center E := by
  let : IsMulCommutative f.ker := hab
  let N := f.ker
  let β : E →* MulAut N := MulAut.conjNormal
  have hβker : f.ker ≤ β.ker := by
    intro g hg
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change g * (x : E) * g⁻¹ = x
    have hc := congrArg (fun y : N => (y : E)) (mul_comm (⟨g,hg⟩ : N) x)
    change g * (x : E) = (x : E) * g at hc
    rw [hc, mul_inv_cancel_right]
  let α : Equiv.Perm (Fin 3) →* MulAut N := f.liftOfSurjective hf ⟨β,hβker⟩
  have hα (g : E) : α (f g) = β g := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  let c : Equiv.Perm (Fin 3) := List.formPerm [0,2,1]
  let a : MulAut N := α c
  have ha : a ^ 3 = 1 := by
    change (α c)^3 = 1
    rw [← map_pow, show c^3 = 1 by decide +kernel, map_one]
  have hat : a = β t := by
    change α (List.formPerm [0,2,1]) = β t
    rw [← ht, hα]
  let n : N →* N := MulAut.cyclicNorm a 3
  have hcentral (x : N) : (n x : E) ∈ center E := by
    apply hfixed _ (n x).property
    have hfix : β t (n x) = n x := by
      rw [← hat]
      exact MulAut.cyclicNorm_fixed a ha x
    have hh := congrArg (fun y : N => (y : E)) hfix
    change t * (n x : E) * t⁻¹ = (n x : E) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hnorm_equiv (g : E) (x : N) : n (β g x) = β g (n x) := by
    apply cubicNorm_equivariant a (β g) ha
    have hperm : ∀ σ : Equiv.Perm (Fin 3), c * σ = σ * c ∨ c * σ = σ * c^2 := by
      decide +kernel
    rcases hperm (f g) with h | h
    · left
      simpa only [map_mul, hα] using congrArg α h
    · right
      simpa only [map_mul, map_pow, hα] using congrArg α h
  have hnorm_invariant (g : E) (x : N) : n (β g x) = n x := by
    rw [hnorm_equiv]
    apply Subtype.ext
    change g * (n x : E) * g⁻¹ = (n x : E)
    rw [mem_center_iff.mp (hcentral x) g, mul_inv_cancel_right]
  have hnorm_central (x : N) (hx : (x : E) ∈ center E) : n x = x^3 := by
    apply MulAut.cyclicNorm_of_fixed
    rw [hat]
    apply Subtype.ext
    change t * (x : E) * t⁻¹ = x
    rw [mem_center_iff.mp hx t, mul_inv_cancel_right]
  let U : Subgroup E := n.ker.map N.subtype
  have hU : U ≤ N := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  have hUnormal : U.Normal := by
    constructor
    rintro _ ⟨x,hx,rfl⟩ g
    refine ⟨β g x, ?_, rfl⟩
    change n (β g x) = 1
    rw [hnorm_invariant]
    exact hx
  refine ⟨U,hUnormal,hU,?_,?_⟩
  · apply disjoint_iff.mpr
    apply le_bot_iff.mp
    rintro _ ⟨⟨x,hx,rfl⟩,hc⟩
    have hpow : x^3 = 1 := (hnorm_central x hc).symm.trans hx
    have ho : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes
      (hp.orderOf_coprime (by decide : Nat.Coprime 2 3) x)
      dvd_rfl (orderOf_dvd_of_pow_eq_one hpow)
    exact congrArg (fun y : N => (y : E)) (orderOf_eq_one_iff.mp ho)
  · intro x hx
    let xN : N := ⟨x,hx⟩
    obtain ⟨k,hk⟩ := exists_pow_eq_self_of_coprime
      (hp.orderOf_coprime (by decide : Nat.Coprime 2 3) (n xN)).symm
    let z : N := (n xN)^k
    have hz : (z : E) ∈ center E := (center E).pow_mem (hcentral xN) k
    have hnz : n z = n xN := by
      rw [hnorm_central z hz]
      change ((n xN)^k)^3 = n xN
      calc
        ((n xN)^k)^3 = ((n xN)^3)^k := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = n xN := hk
    have hu : (xN * z⁻¹ : N) ∈ n.ker := by
      change n (xN * z⁻¹) = 1
      rw [map_mul, map_inv, hnz, mul_inv_cancel]
    have hh := (U ⊔ center E).mul_mem
      ((show U ≤ U ⊔ center E from le_sup_left)
        (show (xN * z⁻¹ : N).val ∈ U from ⟨_,hu,rfl⟩))
      ((show center E ≤ U ⊔ center E from le_sup_right) hz)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right] using hh

end
end Subgroup
