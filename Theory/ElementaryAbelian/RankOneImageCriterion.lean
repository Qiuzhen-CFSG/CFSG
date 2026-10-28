module

public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# Rank-one quotient images of elementary two-groups

An elementary two-group has image of generator rank at most one exactly when
the kernel contains at least half its elements. The kernel is written as the
literal intersection with the homomorphism kernel. Thus the quotient form
applies to intrinsic local two-cores and solvable radicals without replacing
them by ambient cores or by unconnected isomorphic groups.

This is the cardinal calculation used for outer actors in Aschbacher--Smith,
E.1.5 and E.1.14(7), printed pp.210 and 214.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace IsElementaryAbelian
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- A rank-one image is equivalent to a kernel containing half of the actor. -/
theorem rank_map_le_one_iff_card_le_twice_kernel (A : Subgroup G)
    [IsElementaryAbelian 2 A] (f : G →* H) :
    Group.rank (A.map f) ≤ 1 ↔
      Nat.card A ≤ 2 * Nat.card (A ⊓ f.ker : Subgroup G) := by
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hprod := card_inf_ker_mul_card_map A f
  have hk : 0 < Nat.card (A ⊓ f.ker : Subgroup G) := Nat.card_pos
  constructor
  · intro hr
    let : CommGroup (A.map f) := IsMulCommutative.instCommGroup
    have hd := card_dvd_exponent_pow_rank' (A.map f)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (A.map f)))
    have hc : Nat.card (A.map f) ≤ 2 :=
      (Nat.le_of_dvd (by positivity) hd).trans
        (by simpa using (pow_le_pow_right' (by decide : 1 ≤ 2) hr))
    nlinarith
  · intro hc
    apply IsElementaryAbelian.rank_le_of_card_le (p := 2)
    have hmap : Nat.card (A.map f) ≤ 2 := by nlinarith
    simpa using hmap

/-- The quotient version retains the actual normal subgroup being killed. -/
theorem rank_quotient_image_le_one_iff_card_le_twice_intersection
    (A N : Subgroup G) [IsElementaryAbelian 2 A] [N.Normal] :
    Group.rank (A.map (QuotientGroup.mk' N)) ≤ 1 ↔
      Nat.card A ≤ 2 * Nat.card (A ⊓ N : Subgroup G) := by
  simpa only [QuotientGroup.ker_mk'] using
    rank_map_le_one_iff_card_le_twice_kernel A (QuotientGroup.mk' N)

end IsElementaryAbelian
