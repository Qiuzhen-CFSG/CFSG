module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index

/-!
# Cube-one automorphisms fixing an index-two two-subgroup

An automorphism whose cube is the identity and which fixes an index-two
two-subgroup pointwise is the identity. No finiteness of the ambient group,
characteristic-subgroup condition, or splitting assumption is required.

Pointwise fixation makes membership in the subgroup invariant. Since its
index is two, the displacement x⁻¹*e(x) lies in the subgroup. The automorphism
fixes this displacement, so iterating three times shows its cube is one. A
two-group has no nonidentity element with cube one; every displacement is
therefore trivial.

This elementary coprime restriction argument supports the actual residual
order-three action in Stellmacher (9.1), Journal of Algebra 190 (1997), p.48,
where the quaternion central product has index two in the terminal two-core.
It is stated independently of that application and its classification inputs.
-/

namespace Subgroup

public theorem eq_one_of_cube_eq_one_of_fixed_index_two
    {G : Type*} [Group G] (C : Subgroup G) (hi : C.index = 2)
    (hC : IsPGroup 2 C) (e : MulAut G) (hthree : e ^ 3 = 1)
    (hfixed : ∀ x ∈ C, e x = x) : e = 1 := by
  have hmem (x : G) : e x ∈ C ↔ x ∈ C := by
    constructor
    · intro hx
      have heq := hfixed (e x) hx
      have heq' : e x = x := e.injective heq
      exact heq' ▸ hx
    · intro hx
      exact (hfixed x hx).symm ▸ hx
  apply MulEquiv.ext
  intro x
  let d := x⁻¹ * e x
  have hd : d ∈ C := by
    rw [C.mul_mem_iff_of_index_two hi]
    simp only [C.inv_mem_iff, hmem]
  have hdfixed : e d = d := hfixed d hd
  have hstep : e x = x * d := by simp [d]
  have hcube : d ^ 3 = 1 := by
    have hiter : e (e (e x)) = x * d ^ 3 := by
      calc
        e (e (e x)) = e (e (x * d)) := by rw [← hstep]
        _ = x * d ^ 3 := by simp only [map_mul, hdfixed, hstep]; simp [pow_succ, mul_assoc]
    have hiter' : x = x * d ^ 3 := by
      have hh : e (e (e x)) = x := by
        have ht := congrArg (fun a : MulAut G => a x) hthree
        simpa [pow_succ] using ht
      rw [hh] at hiter
      exact hiter
    exact mul_left_cancel (hiter'.symm.trans (mul_one x).symm)
  have hone : d = 1 := by
    have hc := hC.orderOf_coprime (n := 3) (by decide) (⟨d, hd⟩ : C)
    have hdvd : orderOf (⟨d, hd⟩ : C) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext hcube)
    have horder := Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hdvd
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp horder)
  simpa [hone] using hstep

end Subgroup
