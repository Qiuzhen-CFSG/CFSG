module

public import Theory.SpecificGroups.SL2.ProjectiveBorelFrobenius
public import Theory.GroupTheory.Commutator.SubnormalAbsorption
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Subnormal subgroups of binary projective Borel powers

Every subnormal subgroup of the actual projective SL₂ Borel either lies in
its upper-unipotent kernel or contains the whole kernel. Indeed, an element
outside that abelian kernel has the same conjugation action on it as a
nonidentity diagonal element. The action is fixed-point-free, so its
commutator map covers the finite kernel; subnormal commutator absorption
then gives containment.

If a subnormal subgroup of a finite power of the Borel had order twelve,
Cauchy's theorem would supply an element of order three. A nonidentity
coordinate still has order three and lies outside the binary kernel.
Coordinate projection is surjective on the whole power, so its image is
subnormal in the whole Borel and contains the kernel. Thus the field order
divides twelve, which is impossible for `2 ^ n` with `n ≥ 3`.

This is the matrix-group order obstruction used in the Borel A₃-block
exclusion in Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259). No short-group hypothesis is used.
-/

public section

open scoped MatrixGroups IsMulCommutative commutatorElement
open Subgroup
namespace Matrix.ProjectiveSpecialLinearGroup.EvenBorelSubnormalOrder
open OddBorel
variable (F : Type*) [Field F]

private theorem fixedPointFree_of_not_mem (x : borel F)
    (hx : x ∉ (kernel F).subgroupOf (borel F)) :
    MonoidHom.FixedPointFree
      ((MulAut.conjNormal x : MulAut ((kernel F).subgroupOf (borel F))).toMonoidHom) := by
  intro u hu
  obtain ⟨⟨k, c⟩, hkc⟩ := (kernel_isComplement F).2 x
  have he : (k.val.val : PSL(2,F)) * c.val.val = x.val :=
    congrArg Subtype.val hkc
  have hc : (⟨c.val.val, c.property⟩ : complement F) ≠ 1 := by
    intro hc
    apply hx
    change x.val ∈ kernel F
    have hc1 : c.val.val = 1 := congrArg Subtype.val hc
    rw [← he, hc1, mul_one]
    exact k.property
  have hu' : x.val * u.val.val * x.val⁻¹ = u.val.val :=
    congrArg (fun z : (kernel F).subgroupOf (borel F) => z.val.val) hu
  have hku : k.val.val * u.val.val = u.val.val * k.val.val :=
    congrArg Subtype.val (mul_comm (⟨k.val.val, k.property⟩ : kernel F)
      (⟨u.val.val, u.property⟩ : kernel F))
  have hcu : c.val.val * u.val.val * c.val.val⁻¹ = u.val.val := by
    calc
      c.val.val * u.val.val * c.val.val⁻¹ =
          k.val.val⁻¹ * (x.val * u.val.val * x.val⁻¹) * k.val.val := by
        rw [← he]
        group
      _ = k.val.val⁻¹ * u.val.val * k.val.val := by rw [hu']
      _ = u.val.val := by rw [mul_assoc, ← hku]; group
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : kernel F => (z : PSL(2,F)))
    (fixedPointFree F _ hc ⟨u.val.val, u.property⟩ hcu)

variable [Finite F]

/-- A subnormal subgroup of the projective Borel not contained in its
unipotent kernel contains that entire kernel. -/
theorem kernel_le_of_isSubnormal_of_not_le (X : Subgroup (borel F))
    (hX : X.IsSubnormal) (hnot : ¬ X ≤ (kernel F).subgroupOf (borel F)) :
    (kernel F).subgroupOf (borel F) ≤ X := by
  obtain ⟨x, hx, hxU⟩ := SetLike.not_le_iff_exists.mp hnot
  apply le_of_isSubnormal_of_le_commutator _ _ hX
  intro u hu
  obtain ⟨v, hv⟩ := (fixedPointFree_of_not_mem F x hxU).commutatorMap_surjective ⟨u, hu⟩
  have he : (v : borel F) / (x * v * x⁻¹) = u := congrArg Subtype.val hv
  have he' : ⁅(v : borel F), x⁆ = u := by
    rw [← he, commutatorElement_def, div_eq_mul_inv]
    group
  rw [← he']
  exact commutator_mem_commutator v.property hx

/-- No subnormal subgroup of a finite power of the actual projective Borel
has order twelve when the field has order `2 ^ n` with `n ≥ 3`. -/
theorem card_ne_twelve_of_isSubnormal (n : ℕ) (hn : 3 ≤ n)
    (hF : Nat.card F = 2 ^ n) (k : ℕ)
    (X : Subgroup (Fin k → borel F)) (hX : X.IsSubnormal) : Nat.card X ≠ 12 := by
  intro hcard
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hcard]; decide)
  have hxne : x ≠ 1 := by
    intro h
    simp [h] at hxorder
  obtain ⟨i, hi⟩ : ∃ i : Fin k, x.val i ≠ 1 := by
    by_contra h
    push Not at h
    exact hxne (Subtype.ext (funext h))
  let ev : (Fin k → borel F) →* borel F := Pi.evalMonoidHom _ i
  have hev : Function.Surjective ev := fun y => ⟨fun _ => y, rfl⟩
  have hiorder : orderOf (ev x.val) = 3 := by
    have hd : orderOf (ev x.val) ∣ 3 := by
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, hxorder] using
        orderOf_map_dvd (ev.comp X.subtype) x
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h1 | h3
    · exact False.elim (hi (orderOf_eq_one_iff.mp h1))
    · exact h3
  have hiU : ev x.val ∉ (kernel F).subgroupOf (borel F) := by
    intro h
    have hd := ((kernel F).subgroupOf (borel F)).orderOf_dvd_natCard h
    rw [hiorder, card_kernel_in_borel, hF] at hd
    exact (by decide : ¬ (3 : ℕ) ∣ 2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hd)
  have hU : (kernel F).subgroupOf (borel F) ≤ X.map ev :=
    kernel_le_of_isSubnormal_of_not_le F (X.map ev) (hX.map hev)
      (fun h => hiU (h (mem_map_of_mem ev x.property)))
  have hd : 2 ^ n ∣ 12 := by
    simpa only [card_kernel_in_borel, hF, hcard] using
      (card_dvd_of_le hU).trans (X.card_map_dvd ev)
  have h8 : 8 ∣ 12 := (Nat.pow_dvd_pow 2 hn).trans hd
  norm_num at h8

end Matrix.ProjectiveSpecialLinearGroup.EvenBorelSubnormalOrder
