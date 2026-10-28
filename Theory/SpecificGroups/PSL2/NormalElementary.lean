module
public import Theory.SpecificGroups.PSL2.AdjacentPowerSylow
public import Theory.GroupTheory.DihedralNormalAbelian
public import Theory.ElementaryAbelian.Injective

/-!
# Normal elementary subgroups of large adjacent-power PSL₂ Sylows

For an odd prime p > 7 with p − 1 or p + 1 a power of two, the order
formula gives a dihedral Sylow subgroup of order at least sixteen.
Its normal abelian subgroups lie in the cyclic rotation subgroup, so a
normal elementary subgroup has order at most two. The bound is transported
through the specified model equivalence and the original Sylow subtype.

Source: Dickson's subgroup theorem, as used in Aschbacher--Smith 15.1.20(3),
printed p.1097. Only the explicit dihedral Sylow calculation is needed here.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2

private theorem sixteen_dvd_card_of_adjacent_power {p k : ℕ} [Fact p.Prime]
    (hp : 7 < p) (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k) :
    16 ∣ Nat.card PSL(2, ZMod p) := by
  have hpprime : p.Prime := Fact.out
  have hp9 : p ≠ 9 := by
    rintro rfl
    exact (by decide : ¬ Nat.Prime 9) hpprime
  have hpodd : Odd p := hpprime.odd_of_ne_two (by omega)
  have hk : 4 ≤ k := by
    by_contra! hh
    interval_cases k <;> norm_num at hpk <;> omega
  have h16 : 16 ∣ 2 ^ k := pow_dvd_pow 2 hk
  have hsub : 2 ∣ p - 1 := by
    obtain ⟨a,ha⟩ := hpodd
    exact ⟨a,by omega⟩
  have hadd : 2 ∣ p + 1 := by
    obtain ⟨a,ha⟩ := hpodd
    exact ⟨a+1,by omega⟩
  have h32 : 32 ∣ (p - 1) * (p + 1) := by
    rcases hpk with h | h
    · exact Nat.mul_dvd_mul (h ▸ h16) hadd
    · exact Nat.mul_dvd_mul hsub (h ▸ h16)
  have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ p by omega),
      Nat.sub_add_cancel (show 1 ≤ p ^ 2 by nlinarith)]
  rw [GorensteinWalter.psl2_card_formula (ZMod p)
    ⟨p,1,hpprime,hpodd,by omega,by simp⟩,Nat.card_zmod,hsq]
  exact Nat.dvd_div_of_mul_dvd (dvd_mul_of_dvd_right h32 p)

theorem normal_elementary_sylow_card_le_two
    {K : Type*} [Group K] [Finite K] {p k : ℕ} [Fact p.Prime]
    (hp : 7 < p) (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k)
    (e : K ≃* PSL(2,ZMod p)) (P : Sylow 2 K) (E : Subgroup P)
    [E.Normal] [IsElementaryAbelian 2 E] : Nat.card E ≤ 2 := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨m,hm,⟨f⟩⟩ := sylow_dihedral_of_adjacent_power (by omega : 7 ≤ p) hpk Q
  have hm3 : 3 ≤ m := by
    have h16 := Q.pow_dvd_card_of_pow_dvd_card (n := 4)
      (sixteen_dvd_card_of_adjacent_power hp hpk)
    rw [Nat.card_congr f.toEquiv,DihedralGroup.nat_card] at h16
    by_contra! hlow
    have hm2 : m = 2 := by omega
    rw [hm2] at h16
    norm_num at h16
  let g : P ≃* DihedralGroup (2^m) := (e.subgroupMap (P : Subgroup K)).trans f
  let D := E.map g.toMonoidHom
  let : D.Normal := (inferInstance : E.Normal).map g.toMonoidHom g.surjective
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map g.toMonoidHom
  have hD := DihedralGroup.normal_abelian_le_rotations hm3 D
  let : IsCyclic D := isCyclic_of_injective (inclusion hD) (inclusion_injective hD)
  have hd : Nat.card D ∣ 2 := by
    rw [←IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 D
  have hc := Nat.le_of_dvd (by decide : 0 < 2) hd
  rw [←Nat.card_congr (E.equivMapOfInjective g.toMonoidHom g.injective).toEquiv] at hc
  exact hc
end Theory.PSL2
