module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.Group

/-!
# Lifting involution fusion through a Klein four kernel

For a nontrivial involution on a four-group, every fixed element is an
automorphism difference. Thus two involutions with the same image under a
homomorphism with four-group kernel are kernel-conjugate whenever their
conjugation action on the kernel is nontrivial. Lifting a conjugator from the
quotient then lifts a single involution class in an outer coset.

The kernel need not be central in the whole group: that would rule out the
required nontrivial action. This is the elementary lifting step for the field
coset of the perfect four-cover in Aschbacher--Smith 15.3.38, printed p.1137
(1 March 2004 manuscript). The projective coset calculation remains explicit.
-/

public section

namespace IsKleinFour

/-- A nontrivial involution of a four-group has trivial first cohomology. -/
theorem exists_difference_of_involutive_ne_one
    {A : Type*} [Group A] [IsKleinFour A]
    (a : MulAut A) (ha : Function.Involutive a) (hne : a ≠ 1)
    (c : A) (hc : a c = c) : ∃ b : A, b * (a b)⁻¹ = c := by
  by_cases hc1 : c = 1
  · exact ⟨1, by simp [hc1]⟩
  obtain ⟨b, hb⟩ : ∃ b : A, a b ≠ b := by
    by_contra h
    push Not at h
    apply hne
    exact MulEquiv.ext h
  have hb1 : b ≠ 1 := by intro h; subst b; exact hb (map_one a)
  have hab1 : a b ≠ 1 := by simpa using hb1
  have hcb : c ≠ b := by intro h; subst c; exact hb hc
  have hcab : c ≠ a b := by
    intro h
    have hh := congrArg a h
    rw [hc, ha] at hh
    exact hcb hh
  refine ⟨b, ?_⟩
  rw [inv_eq_self]
  exact (eq_mul_of_ne_all hb1 hab1 hb.symm hc1 hcb hcab).symm

end IsKleinFour

namespace Subgroup
variable {G Q : Type*} [Group G] [Group Q]

/-- Involutions above the same quotient element are conjugate by the four-kernel. -/
theorem involution_fiber_conjugate_of_kleinFour_kernel
    (q : G →* Q) [IsKleinFour q.ker] (f : G)
    (hf : f ^ 2 = 1)
    (hnontrivial : ∃ c : q.ker, f * (c : G) * f⁻¹ ≠ (c : G))
    (x : G) (hx : x ^ 2 = 1) (hqx : q x = q f) :
    ∃ c : q.ker, (c : G) * f * (c : G)⁻¹ = x := by
  let a : MulAut q.ker := MulAut.conjNormal f
  have ha : Function.Involutive a := by
    intro c
    apply Subtype.ext
    change f * (f * (c : G) * f⁻¹) * f⁻¹ = (c : G)
    have hf' : f * f = 1 := by simpa only [pow_two] using hf
    calc
      f * (f * (c : G) * f⁻¹) * f⁻¹ = (f * f) * (c : G) * (f * f)⁻¹ := by group
      _ = (c : G) := by rw [hf']; simp
  have hne : a ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := hnontrivial
    exact hc (congrArg Subtype.val (show a c = c from DFunLike.congr_fun h c))
  let c : q.ker := ⟨x * f⁻¹, by simp [MonoidHom.mem_ker, hqx]⟩
  have hcf : (c : G) * f = f * (c : G) := by
    have hci : (c : G)⁻¹ = (c : G) := congrArg Subtype.val (IsKleinFour.inv_eq_self c)
    have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hf)
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
    calc
      (c : G) * f = x := by simp [c]
      _ = x⁻¹ := hxi.symm
      _ = f * (c : G) := by rw [show x = (c : G) * f by simp [c], mul_inv_rev, hci, hfi]
  have hfix : a c = c := by
    apply Subtype.ext
    change f * (c : G) * f⁻¹ = (c : G)
    rw [← hcf, mul_inv_cancel_right]
  obtain ⟨b, hb⟩ := IsKleinFour.exists_difference_of_involutive_ne_one a ha hne c hfix
  refine ⟨b, ?_⟩
  have hb' : (b : G) * (f * (b : G) * f⁻¹)⁻¹ = x * f⁻¹ := congrArg Subtype.val hb
  have hh := congrArg (fun y : G => y * f) hb'
  convert hh using 1 <;> group

/-- A single quotient coset class lifts to a single class, with its conjugator in `N`. -/
theorem involution_coset_conjugate_of_kleinFour_kernel
    (q : G →* Q) [IsKleinFour q.ker] (N : Subgroup G) (hN : q.ker ≤ N)
    (f : G) (hf : f ^ 2 = 1)
    (hnontrivial : ∃ c : q.ker, f * (c : G) * f⁻¹ ≠ (c : G))
    (hquotient : ∀ y : Q, y ^ 2 = 1 → y * (q f)⁻¹ ∈ N.map q →
      ∃ b ∈ N.map q, b * q f * b⁻¹ = y)
    (x : G) (hx : x ^ 2 = 1) (hxN : x * f⁻¹ ∈ N) :
    ∃ n : N, (n : G) * f * (n : G)⁻¹ = x := by
  have hqx : (q x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hqxN : q x * (q f)⁻¹ ∈ N.map q := by
    simpa only [map_mul, map_inv] using mem_map_of_mem q hxN
  obtain ⟨b, hb, he⟩ := hquotient (q x) hqx hqxN
  obtain ⟨n, hn, rfl⟩ := hb
  have hyq : q (n⁻¹ * x * n) = q f := by
    rw [map_mul, map_mul, map_inv, ← he]
    group
  have hy2 : (n⁻¹ * x * n) ^ 2 = 1 := by
    calc
      (n⁻¹ * x * n) ^ 2 = n⁻¹ * x ^ 2 * n := by simp only [pow_two]; group
      _ = 1 := by rw [hx]; simp
  obtain ⟨c, hc⟩ := involution_fiber_conjugate_of_kleinFour_kernel q f hf
    hnontrivial (n⁻¹ * x * n) hy2 hyq
  refine ⟨⟨n * (c : G), N.mul_mem hn (hN c.property)⟩, ?_⟩
  change (n * (c : G)) * f * (n * (c : G))⁻¹ = x
  calc
    _ = n * ((c : G) * f * (c : G)⁻¹) * n⁻¹ := by group
    _ = x := by rw [hc]; group
end Subgroup
