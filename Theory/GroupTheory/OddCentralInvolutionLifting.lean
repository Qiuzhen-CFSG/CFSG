module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Conj

/-!
# Lifting involutory relations through odd central kernels

A quotient involution lifts by raising an arbitrary preimage to the odd
kernel order. Two involutory lifts differ by a central element whose square
is one, so they coincide. A power of a product of two involutions is inverted
by the first factor; if it is central and lies in an odd kernel, it is one.
Thus all Coxeter relations lift. More generally a relator already known to
have square one vanishes as soon as its image vanishes.

This is the central-kernel specialization of L. H. Soicher,
*Presentations of Some Finite Groups*, PhD thesis (Cambridge, 1985),
Section I.6, Propositions I.2 and I.3 (p = 2), printed pp.13--14;
https://doi.org/10.17863/CAM.110463. It makes no presentation-completeness
assertion about a concrete finite group.
-/

namespace OddCentralLifting

variable {G B : Type*} [Group G] [Group B] (q : G →* B)
variable (hodd : Odd (Nat.card q.ker))

include hodd

/-- A square-one relator trivial downstairs vanishes in an odd kernel. -/
public theorem kernel_involution_eq_one {x : G} (hx : q x = 1) (hx2 : x ^ 2 = 1) : x = 1 := by
  let z : q.ker := ⟨x, hx⟩
  have hz2 : z ^ 2 = 1 := Subtype.ext hx2
  have hzc : z ^ Nat.card q.ker = 1 := pow_card_eq_one'
  obtain ⟨k, hk⟩ := hodd
  have heq : Nat.card q.ker = 2 * k + 1 := by simpa only [two_mul] using hk
  rw [heq, pow_add, pow_mul, hz2] at hzc
  have hz : z = 1 := by simpa using hzc
  exact congrArg Subtype.val hz

/-- Every element with square one lifts to an element with square one. -/
public theorem exists_involution_lift (hq : Function.Surjective q)
    (b : B) (hb : b ^ 2 = 1) : ∃ a : G, q a = b ∧ a ^ 2 = 1 := by
  obtain ⟨x, hx⟩ := hq b
  let z : q.ker := ⟨x ^ 2, by rw [MonoidHom.mem_ker, map_pow, hx, hb]⟩
  have hz : (x ^ 2) ^ Nat.card q.ker = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := z))
  refine ⟨x ^ Nat.card q.ker, ?_, ?_⟩
  · rw [map_pow, hx]
    obtain ⟨k, hk⟩ := hodd
    have heq : Nat.card q.ker = 2 * k + 1 := by simpa only [two_mul] using hk
    rw [heq, pow_add, pow_mul, hb]
    simp
  · simpa only [← pow_mul, Nat.mul_comm] using hz

/-- Centrality makes the square-one lift unique. -/
public theorem involution_lift_unique (hcentral : q.ker ≤ Subgroup.center G)
    {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : q a = q b) : a = b := by
  have hk : q (a * b⁻¹) = 1 := by simp [hab]
  have hc : Commute (a * b⁻¹) b :=
    (Subgroup.mem_center_iff.mp (hcentral hk) b).symm
  have hksq : (a * b⁻¹) ^ 2 = 1 := by
    have h := hc.mul_pow 2
    have habb : a * b⁻¹ * b = a := by simp [mul_assoc]
    rw [habb, ha, hb, mul_one] at h
    exact h.symm
  exact mul_inv_eq_one.mp (kernel_involution_eq_one q hodd hk hksq)

/-- Every relation on the product of two involutions lifts through an odd
central kernel. This is the Coxeter-relator step. -/
public theorem involution_product_relation (hcentral : q.ker ≤ Subgroup.center G)
    {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (n : ℕ) (hn : (q a * q b) ^ n = 1) : (a * b) ^ n = 1 := by
  have hk : q ((a * b) ^ n) = 1 := by simpa only [map_pow, map_mul] using hn
  have hc := Subgroup.mem_center_iff.mp (hcentral hk) a
  have ha' : a * a = 1 := by simpa only [pow_two] using ha
  have hb' : b * b = 1 := by simpa only [pow_two] using hb
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha'
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb'
  have hinv : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    simp only [mul_inv_rev, hainv, hbinv]
    rw [← mul_assoc a a b, ha', one_mul]
  have hp : a * (a * b) ^ n * a⁻¹ = ((a * b) ^ n)⁻¹ := by
    rw [← conj_pow, hinv, inv_pow]
  have hfix : a * (a * b) ^ n * a⁻¹ = (a * b) ^ n := by
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have he : (a * b) ^ n = ((a * b) ^ n)⁻¹ := hfix.symm.trans hp
  have hs : ((a * b) ^ n) ^ 2 = 1 := by
    rw [pow_two]
    calc
      _ = ((a * b) ^ n)⁻¹ * (a * b) ^ n := congrArg (fun z => z * (a * b) ^ n) he
      _ = 1 := inv_mul_cancel _
  exact kernel_involution_eq_one q hodd hk hs
end OddCentralLifting
