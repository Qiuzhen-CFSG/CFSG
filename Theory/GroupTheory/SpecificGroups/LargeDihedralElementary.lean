module

public import GorensteinWalter.DihedralCore

/-!
# Elementary normal subgroups of large dihedral two-groups

In a dihedral group of order at least sixteen, a normal subgroup of exponent
two cannot contain a reflection: conjugating that reflection by a rotation
produces a second reflection whose product has order at least four. The
subgroup therefore lies in the cyclic rotation subgroup, and has order at
most two. This is the local exclusion used in Aschbacher–Smith E.2.7,
printed pp.220–221, after identifying the actual odd prime-field Sylow.
-/

public section
open Subgroup
namespace DihedralGroup

/-- A normal subgroup of exponent two in a large dihedral two-group has order at most two. -/
theorem elementary_normal_card_le_two_of_large {m : ℕ} (hm : 3 ≤ m)
    (V : Subgroup (DihedralGroup (2 ^ m))) [V.Normal]
    (hpow : ∀ x : V, x ^ 2 = 1) : Nat.card V ≤ 2 := by
  have hlarge : 8 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide : 0 < 2) hm
  have hno (i : ZMod (2 ^ m)) : sr i ∉ V := by
    intro hi
    have hconj := (inferInstance : V.Normal).conj_mem (sr i) hi (r 1)
    have hprod := V.mul_mem hi hconj
    have hp : (sr i * (r 1 * sr i * (r 1)⁻¹)) ^ 2 = 1 :=
      congrArg V.subtype (hpow ⟨_, hprod⟩)
    have he : (sr i * (r 1 * sr i * (r 1)⁻¹)) ^ 2 = r (-4 : ZMod (2 ^ m)) := by
      simp only [inv_r, r_mul_sr, sr_mul_r, sr_mul_sr, pow_two, r_mul_r]
      congr 1
      ring
    have hz : (4 : ZMod (2 ^ m)) = 0 := by
      rw [he] at hp
      exact neg_eq_zero.mp (r.inj hp)
    have hd : 2 ^ m ∣ 4 := (ZMod.natCast_eq_zero_iff 4 (2 ^ m)).mp hz
    have hh := Nat.le_of_dvd (by decide : 0 < 4) hd
    omega
  have hVR : V ≤ zpowers (r (1 : ZMod (2 ^ m))) := by
    intro x hx
    obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := GorensteinWalter.dihedralGroup_cases x
    · exact GorensteinWalter.r_mem_zpowers_r_one i
    · exact (hno i hx).elim
  let : IsCyclic V := Subgroup.isCyclic_of_le hVR
  have hd : Nat.card V ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  exact Nat.le_of_dvd (by decide : 0 < 2) hd

end DihedralGroup
