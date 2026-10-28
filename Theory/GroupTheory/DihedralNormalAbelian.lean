module
public import Theory.GroupTheory.DihedralAbelianIndexTwo
public import Theory.GroupTheory.SpecificGroups.DihedralSubgroupModels

/-!
# Abelian normal subgroups and small-index powers in dihedral two-groups

In a dihedral group of order at least sixteen, a reflection cannot belong
to a normal abelian subgroup: conjugating it by a rotation produces a
noncommuting reflection. A nonabelian subgroup of index two is dihedral
with half the rotation order, so that smaller rotation order bounds its
exponent. These two facts supply the model calculation in the abelian-core
argument of Aschbacher--Smith 2.5.21, printed p.565.
-/

public section
namespace DihedralGroup
open Subgroup

/-- Normal abelian subgroups of dihedral groups of order at least sixteen are rotations. -/
theorem normal_abelian_le_rotations {n : ℕ} (hn : 3 ≤ n)
    (B : Subgroup (DihedralGroup (2 ^ n))) [B.Normal] [IsMulCommutative B] :
    B ≤ zpowers (r 1) := by
  intro b hb
  cases b with
  | r i =>
    refine ⟨i.val, ?_⟩
    change (r 1 : DihedralGroup (2 ^ n)) ^ i.val = r i
    rw [r_one_pow, ZMod.natCast_zmod_val]
  | sr i =>
    have hc := (inferInstance : B.Normal).conj_mem (sr i) hb (r 1)
    have hh := B.le_centralizer hb _ hc
    have he : (4 : ZMod (2 ^ n)) = 0 := by
      simp only [inv_r, r_mul_sr, sr_mul_r, sr_mul_sr, r.injEq] at hh
      linear_combination hh
    have hd : 2 ^ n ∣ 4 := (ZMod.natCast_eq_zero_iff 4 (2 ^ n)).mp he
    have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
    have hge : 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    omega
end DihedralGroup

namespace DihedralGroup
open Subgroup
/-- Every element of a nonabelian subgroup of index two has the smaller rotation power bound. -/
theorem nonabelian_index_two_pow {n : ℕ} (hn : 3 ≤ n)
    (D : Subgroup (DihedralGroup (2 ^ n)))
    (hi : D.index = 2) (hD : ¬ IsMulCommutative D) :
    ∀ d ∈ D, d ^ (2 ^ (n - 1)) = 1 := by
  have hdcard : Nat.card D = 2 ^ n := by
    have h := D.index_mul_card
    rw [hi, DihedralGroup.nat_card] at h
    omega
  obtain hc | ⟨k, ⟨e⟩⟩ := subgroup_cyclic_or_dihedral_two_power D
  · exact (hD hc.isMulCommutative).elim
  have hpow : 2 ^ k = 2 ^ (n - 1) := by
    have he := Nat.card_congr e.toEquiv
    rw [hdcard, DihedralGroup.nat_card] at he
    have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
    omega
  have hdvd : 2 ∣ 2 ^ (n - 1) := dvd_pow_self 2 (by omega)
  intro d hd
  have hh := Monoid.pow_exponent_eq_one (⟨d, hd⟩ : D)
  rw [Monoid.exponent_eq_of_mulEquiv e, DihedralGroup.exponent, hpow] at hh
  change (⟨d, hd⟩ : D) ^ Nat.lcm (2 ^ (n - 1)) 2 = 1 at hh
  rw [Nat.lcm_eq_left hdvd] at hh
  exact congrArg Subtype.val hh
end DihedralGroup

namespace DihedralGroup
open Subgroup
/-- A nonabelian index-two subgroup forces the ambient dihedral order to be at least sixteen. -/
theorem parameter_ge_three_of_nonabelian_index_two {n : ℕ}
    (D : Subgroup (DihedralGroup (2 ^ n)))
    (hi : D.index = 2) (hD : ¬ IsMulCommutative D) : 3 ≤ n := by
  obtain hc | ⟨k, ⟨e⟩⟩ := subgroup_cyclic_or_dihedral_two_power D
  · exact (hD hc.isMulCommutative).elim
  have hk : 2 ≤ k := by
    by_contra! hk
    have hh : IsMulCommutative (DihedralGroup (2 ^ k)) := by
      apply DihedralGroup.commutative_iff.mpr
      interval_cases k <;> decide
    apply hD
    refine ⟨⟨fun a b => e.injective ?_⟩⟩
    simpa only [map_mul] using hh.is_comm.comm (e a) (e b)
  have hcard : Nat.card D = 2 * 2 ^ k := (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have he := D.index_mul_card
  rw [hi, hcard, DihedralGroup.nat_card] at he
  have hlarge : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  by_contra! hn
  have hsmall : 2 ^ n ≤ 4 := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 2)
  omega

end DihedralGroup
