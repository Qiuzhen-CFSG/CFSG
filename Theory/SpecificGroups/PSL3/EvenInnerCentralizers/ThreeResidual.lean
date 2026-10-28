module

public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.MarkedInvariants
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The exceptional three-residual of a binary PSL₃ root centralizer

For even n > 2, the exact projective torus order (2ⁿ − 1)/3 has a
prime divisor p > 3. A field unit of order p gives a torus element in
O³(C) with nontrivial cubic weights on both noncentral Heisenberg roots.
Inside O³(C), that odd element belongs to O²(O³(C)); its commutators
supply both roots and hence their central commutators. The remaining
torus factors have odd order. Thus O³(C) is two-perfect.

The existing marked centralizer computation identifies O²(C) = C;
transport through this actual equivalence also proves the iterated result.
The cube-root scalar kernel and the full unitriangular embedding are
retained throughout. No assertion is made at n = 2.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(1), the inner case of 16.4.8, and Notation 16.5.5,
printed pp.1171, 1188 and 1197.
-/

public section

open Subgroup Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3.EvenInnerCentralizers
open Matrix.PSL3.EvenInnerCentralizers.MarkedInvariants
namespace Matrix.PSL3.EvenInnerCentralizers.ThreeResidual
variable (F : Type*) [Field F] [Finite F]

private theorem even_parameters {n : ℕ} (hn : 2 < n) (he : Even n) :
    3 < n ∧ 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := he
  constructor
  · omega
  · rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num

private theorem binary_char {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    ringChar F = 2 := by
  let := Fintype.ofFinite F
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, hF]
  exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt hn))

omit [Finite F] in
private theorem subgroup_twoPerfect [CharP F 2] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (S : Subgroup (centralizer F))
    (hU : (unipotentInCentralizer F).range ≤ S)
    (a : Fˣ) (ha : torus F a ∈ S) (hcube : a ^ 3 ≠ 1) :
    IsPPerfect 2 S := by
  let f : U F →* S := (unipotentInCentralizer F).codRestrict S (fun u => hU ⟨u, rfl⟩)
  let t : S := ⟨torus F a, ha⟩
  have ht : t ∈ pResidual 2 S := by
    apply mem_pResidual_of_orderOf_coprime
    rw [← Subgroup.orderOf_coe]
    exact (units_odd F hF hn).coprime_two_left.of_dvd_right
      ((orderOf_map_dvd (torus F) a).trans (orderOf_dvd_natCard a))
  have hfirst : (a : F)^3 ≠ 1 := fun h => hcube (Units.ext h)
  have hsecond : (↑a⁻¹ : F)^3 ≠ 1 := by
    intro h
    have hi : (a⁻¹)^3 = 1 := Units.ext h
    exact hcube (by simpa only [← inv_pow, inv_inv, inv_one] using congrArg Inv.inv hi)
  have hroots : f.range ≤ pResidual 2 S := by
    apply range_le_of_roots F f
    · apply scalar_root_le_normal _ _ t ht ((a : F)^3) hfirst
      intro x
      apply Subtype.ext
      simpa only [MonoidHom.comp_apply, firstRoot, MonoidHom.coe_mk, OneHom.coe_mk,
        toAdd_ofAdd, mul_zero, f, t, Subgroup.coe_mul, Subgroup.coe_inv,
        MonoidHom.codRestrict_apply] using torus_conjugate F a (⟨x, 0, 0⟩ : U F)
    · apply scalar_root_le_normal _ _ t ht ((↑a⁻¹ : F)^3) hsecond
      intro x
      apply Subtype.ext
      simpa only [MonoidHom.comp_apply, secondRoot, MonoidHom.coe_mk, OneHom.coe_mk,
        toAdd_ofAdd, mul_zero, f, t, Subgroup.coe_mul, Subgroup.coe_inv,
        MonoidHom.codRestrict_apply] using torus_conjugate F a (⟨0, x, 0⟩ : U F)
  apply (pResidual_eq_top_iff 2 S).mp
  apply top_unique
  intro g _
  obtain ⟨b, u, he⟩ := centralizer_factorization F g.val
  have hb : torus F b ∈ S := by
    have := S.mul_mem g.property (S.inv_mem (hU ⟨u, rfl⟩))
    simpa only [he, mul_inv_cancel_right] using this
  have ht' : (⟨torus F b, hb⟩ : S) ∈ pResidual 2 S := by
    apply mem_pResidual_of_orderOf_coprime
    rw [← Subgroup.orderOf_coe]
    exact (units_odd F hF hn).coprime_two_left.of_dvd_right
      ((orderOf_map_dvd (torus F) b).trans (orderOf_dvd_natCard b))
  have hu : f u ∈ pResidual 2 S := hroots ⟨u, rfl⟩
  have hg : g = (⟨torus F b, hb⟩ : S) * f u := Subtype.ext he
  rw [hg]
  exact (pResidual 2 S).mul_mem ht' hu

/-- The three-residual of the actual root centralizer has no nontrivial two-group quotient. -/
theorem threeResidual_twoPerfect {n : ℕ} (hn : 2 < n) (he : Even n)
    (hF : Nat.card F = 2 ^ n) : IsPPerfect 2 (pResidual 3 (centralizer F)) := by
  let : CharP F 2 := ringChar.of_eq (binary_char F (by omega) hF)
  have hU : (unipotentInCentralizer F).range ≤ pResidual 3 (centralizer F) := by
    intro x hx
    apply mem_pResidual_of_orderOf_coprime
    have hc := (unipotent_isTwoGroup F hF).orderOf_coprime
      (by decide : Nat.Coprime 2 3) (⟨x, hx⟩ : (unipotentInCentralizer F).range)
    rw [← Subgroup.orderOf_coe] at hc
    exact hc.symm
  obtain ⟨p, hp, hp3, hpd⟩ :=
    Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub (even_parameters hn he).1
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by
    rwa [Nat.card_units, hF])
  have hcube : a ^ 3 ≠ 1 := by
    intro h
    have hd : p ∣ 3 := ha ▸ orderOf_dvd_of_pow_eq_one h
    have := Nat.le_of_dvd (by decide : 0 < 3) hd
    omega
  have htorus : torus F a ∈ pResidual 3 (centralizer F) := by
    apply mem_pResidual_of_orderOf_coprime
    apply Nat.Coprime.of_dvd_right (orderOf_map_dvd (torus F) a)
    rw [ha]
    exact (hp.coprime_iff_not_dvd.mpr (by
      intro hd
      have := Nat.le_of_dvd (by decide : 0 < 3) hd
      omega)).symm
  exact subgroup_twoPerfect F (by omega) hF _ hU a htorus hcube

/-- Apply the source modification to the actual two-residual, retaining both subgroup inclusions. -/
theorem twoThreeResidual_twoPerfect {n : ℕ} (hn : 2 < n) (he : Even n)
    (hF : Nat.card F = 2 ^ n) :
    IsPPerfect 2 (pResidual 3 (pResidual 2 (centralizer F))) := by
  have hpar := even_parameters hn he
  let e : pResidual 2 (centralizer F) ≃* centralizer F :=
    (MulEquiv.subgroupCongr (twoResidual_eq_top F hF hpar.1 hpar.2)).trans topEquiv
  let d : pResidual 3 (pResidual 2 (centralizer F)) ≃* pResidual 3 (centralizer F) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_pResidual 3 e))
  exact (threeResidual_twoPerfect F hn he hF).of_surjective d.symm.toMonoidHom d.symm.surjective
end Matrix.PSL3.EvenInnerCentralizers.ThreeResidual
