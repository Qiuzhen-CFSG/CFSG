module

public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.GroupAction.AutomorphismFixedTransport
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Involutions in index-two subgroups of the PSL₃(4) fixed group

An extension with odd-order kernel and quaternion quotient Q₈ has every
element of square one in each subgroup of index two. Indeed the odd kernel
lies in that subgroup, and every element of square one in Q₈ is a square.
Lift a square root in Q₈ and compare its square with the original element.
This argument requires no splitting of the extension.

For the actual PSL₃(4) carrier, `FixedGroupTable` retains the precise earlier
table input: the full fixed subgroup of an outer involution is perfect or
has an E₉ kernel and Q₈ quotient. The extension is specified by a surjective
homomorphism from that fixed subgroup and an actual equivalence of its kernel
with E₉. This module proves involution containment from this structural input;
it does not assert the automorphism table or construct the extension maps.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.4 on
printed p.1171 and its use in the proof of 16.4.9(2), printed p.1190.
The notation Q₈/E₉ on p.1190 has E₉ as kernel and Q₈ as quotient. The
two-residual E₉ in 16.1.4(5) alone does not identify the full fixed group.
-/

@[expose] public section

namespace Subgroup
variable {H : Type*} [Group H]

/-- An odd-kernel extension of Q₈ has no involution outside an index-two
subgroup. The statement also includes the identity, and requires no splitting. -/
theorem sq_eq_one_mem_of_odd_kernel_quaternion_quotient
    (π : H →* QuaternionGroup 2) (hπ : Function.Surjective π)
    (hodd : Odd (Nat.card π.ker)) (D : Subgroup H) (hD : D.index = 2)
    (x : H) (hx : x ^ 2 = 1) : x ∈ D := by
  have hker : π.ker ≤ D := by
    intro k hk
    let z : π.ker := ⟨k, hk⟩
    obtain ⟨m, hm⟩ := exists_pow_eq_pow_two_mul
      (pow_card_eq_one' (x := z)) hodd 1
    have he : k = (k ^ 2) ^ m := by
      simpa only [pow_one, pow_mul, Subgroup.coe_pow] using congrArg Subtype.val hm
    rw [he]
    exact D.pow_mem (D.sq_mem_of_index_two hD k) m
  have hsq : ∀ q : QuaternionGroup 2, q ^ 2 = 1 → ∃ y, y ^ 2 = q := by decide
  obtain ⟨q, hq⟩ := hsq (π x) (by rw [← map_pow, hx, map_one])
  obtain ⟨y, hy⟩ := hπ q
  have hk : x * (y ^ 2)⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hy, hq, mul_inv_cancel]
  have hm := D.mul_mem (hker hk) (D.sq_mem_of_index_two hD y)
  simpa only [inv_mul_cancel_right] using hm

end Subgroup

namespace Matrix.PSL3Four.IndexTwoFixedInvolutions

/-- Actual maps for an extension with normal kernel E₉ and quotient Q₈.
Normality is intrinsic to the kernel; a complement is not part of the data. -/
structure ElementaryNineQuaternionExtension (H : Type*) [Group H] where
  projection : H →* QuaternionGroup 2
  surjective : Function.Surjective projection
  kernelEquiv : projection.ker ≃* Multiplicative (Fin 2 → ZMod 3)

/-- The specified E₉ kernel has odd order. -/
theorem ElementaryNineQuaternionExtension.kernel_odd {H : Type*} [Group H]
    (s : ElementaryNineQuaternionExtension H) : Odd (Nat.card s.projection.ker) := by
  rw [Nat.card_congr s.kernelEquiv.toEquiv]
  change Odd (Nat.card (Fin 2 → ZMod 3))
  norm_num [Nat.card_eq_fintype_card]

/-- The full-fixed-group consequence of the earlier table used on p.1190,
for this particular automorphism of the actual PSL₃(4) carrier. This is an
explicit input, not a proved classification of outer automorphisms. -/
def FixedGroupTable (a : MulAut PSL) : Prop :=
  orderOf a = 2 → (¬ ∃ x : PSL, a = MulAut.conj x) →
    Group.IsPerfect a.fixedSubgroup ∨
      Nonempty (ElementaryNineQuaternionExtension a.fixedSubgroup)

/-- From the exact full-fixed-group table, each index-two subgroup contains
every element of square one in a nonperfect outer-involution fixed group. -/
theorem fixed_sq_eq_one_mem_of_table (a : MulAut PSL) (hTable : FixedGroupTable a)
    (ha : orderOf a = 2) (houter : ¬ ∃ x : PSL, a = MulAut.conj x)
    (hperfect : ¬ Group.IsPerfect a.fixedSubgroup)
    (D : Subgroup a.fixedSubgroup) (hD : D.index = 2)
    (x : a.fixedSubgroup) (hx : x ^ 2 = 1) : x ∈ D := by
  obtain ⟨s⟩ := (hTable ha houter).resolve_left hperfect
  exact D.sq_eq_one_mem_of_odd_kernel_quaternion_quotient
    s.projection s.surjective s.kernel_odd hD x hx

/-- The involution formulation of the PSL₃(4) model fact. -/
theorem fixed_involution_mem_of_table (a : MulAut PSL) (hTable : FixedGroupTable a)
    (ha : orderOf a = 2) (houter : ¬ ∃ x : PSL, a = MulAut.conj x)
    (hperfect : ¬ Group.IsPerfect a.fixedSubgroup)
    (D : Subgroup a.fixedSubgroup) (hD : D.index = 2)
    (x : a.fixedSubgroup) (hx : orderOf x = 2) : x ∈ D :=
  fixed_sq_eq_one_mem_of_table a hTable ha houter hperfect D hD x
    (by simpa only [hx] using pow_orderOf_eq_one x)

end Matrix.PSL3Four.IndexTwoFixedInvolutions
