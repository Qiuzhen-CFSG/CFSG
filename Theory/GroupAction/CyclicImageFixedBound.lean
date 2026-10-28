module
public import Theory.GroupAction.FourthPowerFixedCard
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Fixed points for a cyclic quotient of exponent four

If the action kernel contains the kernel of a homomorphism, a generator of
the cyclic quotient image lifts to an automorphism with exactly the same
fixed points. When the quotient image has order dividing four, its lift has
fourth power one and the binary fixed-point bound gives |V| ≤ |C_V(S)|⁴.

The original quintic amalgam uses this to show that its two-core moves the
plane: otherwise its elementary closure of order at least 32 would have
order at most 16. Source: Aschbacher--Smith 14.2.20--21, pp.988--989;
the elementary fixed-point estimate is proved in `FourthPowerFixedCard`.
-/

public section
namespace Theory.GroupAction
open Subgroup
open scoped IsMulCommutative

section
variable {H K V : Type*} [Group H] [Group K] [Group V] [Finite V]
  [IsElementaryAbelian 2 V]

/-- A cyclic quotient of order dividing four bounds a binary module by its fixed group. -/
theorem cyclic_image_fixed_bound (q : H →* K) (f : H →* MulAut V)
    (S : Subgroup H) [IsCyclic (S.map q)]
    (hcard : Nat.card (S.map q) ∣ 4) (hk : q.ker ≤ f.ker) :
    Nat.card V ≤ Nat.card (FixedPoints.subgroup (S.map f) V) ^ 4 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := S.map q)
  obtain ⟨t, ht, he⟩ := a.property
  have hq4 : q t ^ 4 = 1 := by
    rw [he]
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_natCard a).trans hcard))
  have hf4 : f t ^ 4 = 1 := by
    rw [← map_pow]
    apply hk
    simpa only [MonoidHom.mem_ker, map_pow] using hq4
  have hgen (s : H) (hs : s ∈ S) : f s ∈ zpowers (f t) := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (ha ⟨q s, mem_map_of_mem q hs⟩)
    have hqn : q s = q t ^ n := by
      simpa only [← he, Subgroup.coe_zpow] using (congrArg Subtype.val hn).symm
    have hker : s * (t ^ n)⁻¹ ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hqn, mul_inv_cancel]
    have hfn : f s = f t ^ n := by
      have hh : f (s * (t ^ n)⁻¹) = 1 := hk hker
      simpa only [map_mul, map_inv, map_zpow, mul_inv_eq_one] using hh
    exact mem_zpowers_iff.mpr ⟨n, hfn.symm⟩
  have hfix : FixedPoints.subgroup (zpowers (f t)) V ≤
      FixedPoints.subgroup (S.map f) V := by
    intro v hv s
    obtain ⟨x, hx, he⟩ := s.property
    have hh := hv ⟨f x, hgen x hx⟩
    change (f x) v = v at hh
    change (s : MulAut V) v = v
    rwa [he] at hh
  exact (MulAut.card_le_fixed_card_pow_four_of_fourth_power_eq_one (f t) hf4).trans
    (Nat.pow_le_pow_left (card_le_of_le hfix) 4)
end

end Theory.GroupAction
