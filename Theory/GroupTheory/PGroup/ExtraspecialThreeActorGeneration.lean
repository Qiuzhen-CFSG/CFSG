module
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints

/-!
# Normal generation by a small actor on an extraspecial three-group

A nontrivial involution on an extraspecial group of order 27 which fixes
its center inverts the Frattini quotient. Its commutators therefore
surject onto that quotient and generate the entire group. Consequently,
every normal subgroup of an overgroup containing that involution also
contains the extraspecial group. This applies to section centralizers in
Aschbacher–Smith 14.7.20(2), printed p.1049.
-/

public noncomputable section
open Subgroup
namespace IsExtraspecial
variable {D : Type*} [Group D] [Finite D]

/-- A normal subgroup containing a nontrivial center-fixing involution
contains the whole normal extraspecial subgroup of order 27. -/
theorem le_normal_of_center_fixing_involution
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (t : D) (ht : t ^ 2 = 1)
    (hne : (MulAut.conjNormal t : MulAut P) ≠ 1)
    (hcenter : ∀ z ∈ center P, (MulAut.conjNormal t : MulAut P) z = z)
    (N : Subgroup D) [N.Normal] (htN : t ∈ N) : P ≤ N := by
  let a : MulAut P := MulAut.conjNormal t
  have ha : Function.Involutive a := by
    intro x
    have he : a ^ 2 = 1 := by
      change (MulAut.conjNormal t : MulAut P) ^ 2 = 1
      rw [←map_pow,ht,map_one]
    exact congrArg (fun f : MulAut P => f x) (by simpa only [pow_two] using he)
  obtain ⟨hexp,hinv⟩ := exponent_and_frattini_inversion_of_card27 hP a ha hne hcenter
  let J := N.subgroupOf P
  have hgen : J ⊔ frattini P = ⊤ := by
    apply top_unique
    intro x _
    let y := a x * x⁻¹
    have hy : y ∈ J := by
      change t*(x:D)*t⁻¹*(x:D)⁻¹ ∈ N
      rw [show t*(x:D)*t⁻¹*(x:D)⁻¹ = t*((x:D)*t⁻¹*(x:D)⁻¹) by group]
      exact N.mul_mem htN ((inferInstance : N.Normal).conj_mem t⁻¹ (N.inv_mem htN) x)
    have hxy : x / y ∈ frattini P := by
      apply QuotientGroup.eq_iff_div_mem.mp
      change QuotientGroup.mk' (frattini P) x = QuotientGroup.mk' (frattini P) y
      change _ = QuotientGroup.mk' (frattini P) (a x * x⁻¹)
      rw [map_mul,hinv,map_inv,←map_inv,←map_mul]
      have hx3 : x^3=1 := by simpa only [hexp] using Monoid.pow_exponent_eq_one x
      congr 1
      calc
        x = x^3*(x⁻¹*x⁻¹) := by group
        _ = x⁻¹*x⁻¹ := by rw [hx3,one_mul]
    have hm := (J ⊔ frattini P).mul_mem
      ((show frattini P ≤ J ⊔ frattini P from le_sup_right) hxy)
      ((show J ≤ J ⊔ frattini P from le_sup_left) hy)
    simpa only [div_mul_cancel] using hm
  have hJ : J = ⊤ := frattini_nongenerating hgen
  intro x hx
  exact show (⟨x,hx⟩ : P) ∈ J from hJ ▸ mem_top _

end IsExtraspecial
