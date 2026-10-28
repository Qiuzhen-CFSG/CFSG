module
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.GroupAction.AutomorphismFixedSubgroup
import all Theory.Mathieu.M22.Properties.ThreeRank

/-!
# Odd three-parts of involutory M₂₂ fixed subgroups

The certified Sylow three subgroup has one regular orbit of size nine,
four orbits of size three with distinct kernels, and one fixed point in
its degree-22 action. Hence its transitive orbits are pairwise nonisomorphic.
A commuting involution preserves every orbit and acts there by an element
of odd order, so it is trivial. Full automorphism coverage by the design
normalizer transfers this fact to every abstract involution. Sylow conjugacy
then excludes nine from its fixed-subgroup order.

This proves the order separation required for Aschbacher–Smith E.6.23
(and E.6.18), without assuming the structural centralizer table in 16.1.5(5).
The internal import uses the original certified Sylow generators and their
small permutation tables; no second model or enumeration is introduced.
-/

open Subgroup
namespace Sporadic.Mathieu
private def orbitWord (a b : Fin 3) : Equiv.Perm (Fin 22) :=
  rankXPerm ^ a.val * rankYPerm ^ b.val

private theorem orbitWord_cube (a b : Fin 3) : orbitWord a b ^ 3 = 1 := by
  revert a b
  decide +kernel

private theorem orbit_separation (i j : Fin 22)
    (h : ∀ a b : Fin 3, orbitWord a b i = i ↔ orbitWord a b j = j) :
    ∃ a b : Fin 3, orbitWord a b i = j := by
  have hc : ∀ i j : Fin 22,
      (∀ a b : Fin 3, orbitWord a b i = i ↔ orbitWord a b j = j) →
        ∃ a b : Fin 3, orbitWord a b i = j := by decide +kernel
  exact hc i j h

private theorem perm_eq_one_of_commute (s : Equiv.Perm (Fin 22)) (hs : s ^ 2 = 1)
    (hx : Commute s rankXPerm) (hy : Commute s rankYPerm) : s = 1 := by
  have hc (a b : Fin 3) : Commute s (orbitWord a b) :=
    (hx.pow_right a.val).mul_right (hy.pow_right b.val)
  apply Equiv.ext
  intro i
  obtain ⟨a, b, hab⟩ := orbit_separation i (s i) (by
    intro a b
    have hcomm := Equiv.congr_fun (hc a b).eq i
    change s (orbitWord a b i) = orbitWord a b (s i) at hcomm
    rw [← hcomm]
    exact s.injective.eq_iff.symm)
  have hsq : s (s i) = i := Equiv.congr_fun hs i
  have hcomm := Equiv.congr_fun (hc a b).eq i
  change s (orbitWord a b i) = orbitWord a b (s i) at hcomm
  have htwo : orbitWord a b (orbitWord a b i) = i := by
    rw [hab, ← hcomm, hab, hsq]
  have hthree : orbitWord a b (orbitWord a b (orbitWord a b i)) = i :=
    Equiv.congr_fun (orbitWord_cube a b) i
  rw [htwo] at hthree
  exact hab.symm.trans hthree


private theorem automorphism_eq_one_of_fixes_three_sylow (r : MulAut M22)
    (hr : r ^ 2 = 1) (hfix : ∀ x ∈ m22ThreeElementary, r x = x) : r = 1 := by
  obtain ⟨s, rfl⟩ := m22DesignAutToAut_surjective r
  have hs : s ^ 2 = 1 := m22DesignAutToAut_injective (by
    rw [map_pow, map_one]
    exact hr)
  have hperm : s.val = 1 := perm_eq_one_of_commute s.val
    (by exact congrArg Subtype.val hs) (by
      have hx := hfix rankX ((show zpowers rankX ≤ m22ThreeElementary from le_sup_left) (mem_zpowers rankX))
      have he := congrArg Subtype.val hx
      rw [m22DesignAutToAut_apply_perm] at he
      exact mul_inv_eq_iff_eq_mul.mp he) (by
      have hy := hfix rankY ((show zpowers rankY ≤ m22ThreeElementary from le_sup_right) (mem_zpowers rankY))
      have he := congrArg Subtype.val hy
      rw [m22DesignAutToAut_apply_perm] at he
      exact mul_inv_eq_iff_eq_mul.mp he)
  have hsid : s = 1 := Subtype.ext hperm
  rw [hsid, map_one]

public theorem m22_involution_not_nine_dvd_fixed_card (r : MulAut M22)
    (hr : orderOf r = 2) : ¬ 9 ∣ Nat.card r.fixedSubgroup := by
  intro hd
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2) hd
  let K : Subgroup M22 := H.map r.fixedSubgroup.subtype
  have hK : Nat.card K = 3 ^ 2 :=
    (card_map_of_injective r.fixedSubgroup.subtype_injective).trans hH
  have hi : ¬ 3 ∣ K.index := by
    have h := K.card_mul_index
    rw [hK, m22_order] at h
    have he : K.index = 49280 := by omega
    rw [he]
    norm_num
  let P : Sylow 3 M22 := (IsPGroup.of_card hK).toSylow hi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 P m22ThreeSylow
  let c : MulAut M22 := MulAut.conj g
  let t : MulAut M22 := c * r * c⁻¹
  have ht : t ^ 2 = 1 := by
    dsimp [t]
    change (MulAut.conj c r) ^ 2 = 1
    rw [← map_pow, (orderOf_eq_prime_iff.mp hr).1, map_one]
  have hf : ∀ x ∈ m22ThreeElementary, t x = x := by
    intro x hx
    have hm : x ∈ (g • P : Sylow 3 M22) := by
      rw [hg]
      exact hx
    obtain ⟨y, hy, he⟩ := mem_map.mp hm
    have hyK : y ∈ K := hy
    obtain ⟨z, hz, hzy⟩ := mem_map.mp hyK
    have hfixed : r y = y := hzy ▸ (MulAut.mem_fixedSubgroup r z).mp z.property
    rw [← he]
    change c (r (c⁻¹ (c y))) = c y
    rw [MulAut.inv_apply, MulEquiv.symm_apply_apply, hfixed]
  have he := automorphism_eq_one_of_fixes_three_sylow t ht hf
  have ho : orderOf t = 2 := ((MulAut.conj c).orderOf_eq r).trans hr
  rw [he, orderOf_one] at ho
  omega
/-- The alternating-six order cannot divide an involutory fixed subgroup. -/
public theorem m22_involution_not_360_dvd_fixed_card (r : MulAut M22)
    (hr : orderOf r = 2) : ¬ 360 ∣ Nat.card r.fixedSubgroup :=
  fun h => m22_involution_not_nine_dvd_fixed_card r hr
    (dvd_trans (by norm_num : 9 ∣ 360) h)

/-- The alternating-seven order cannot divide an involutory fixed subgroup. -/
public theorem m22_involution_not_2520_dvd_fixed_card (r : MulAut M22)
    (hr : orderOf r = 2) : ¬ 2520 ∣ Nat.card r.fixedSubgroup :=
  fun h => m22_involution_not_nine_dvd_fixed_card r hr
    (dvd_trans (by norm_num : 9 ∣ 2520) h)

end Sporadic.Mathieu
