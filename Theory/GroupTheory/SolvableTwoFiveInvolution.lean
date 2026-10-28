module
public import Theory.GroupTheory.SolvableThreePartCore

/-!
# The fixed involution of a solvable two-five group

If the order divides 2^a·5 and is divisible by eight, the two-core is
nontrivial: otherwise the cyclic five-core is self-centralizing and its
automorphism group cannot accommodate the two-part. A unique involution
in a Sylow subgroup is then the unique involution of the characteristic
two-core, so every ambient automorphism fixes it.

The two-core calculation follows the existing private argument in
Classical/SylowMarkedSL2/SolvableIntersection. The consumer is the odd
radical alternative in Aschbacher–Smith 5.2.2, printed pp.648–649.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TwoFive

/-- The two-core is nontrivial when the two-part is at least eight and the odd part divides five. -/
theorem twoCore_ne_bot
    {Y : Type*} [Group Y] [Finite Y] (hs : Group.IsSolvable Y)
    {a : ℕ} (hd : Nat.card Y ∣ 2^a * 5) (h8 : 8 ∣ Nat.card Y) :
    pCore 2 Y ≠ ⊥ := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro htwo
  have hf : fittingSubgroup Y = pCore 5 Y := by
    apply le_antisymm _ (pCore_le_fitting Y 5)
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    have hp := Nat.prime_of_mem_primeFactors p.val.property
    have hh := (Nat.dvd_of_mem_primeFactors p.val.property).trans hd
    rcases hp.dvd_mul.mp hh with h | h
    · have he : p.val.val = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h)
      rw [he,htwo]
      exact bot_le
    · have he : p.val.val = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h
      rw [he]
  let N := pCore 5 Y
  have hc : Nat.card N ∣ 5 := by
    obtain ⟨b,hb⟩ := (pCore_isPGroup (p := 5) (G := Y)).exists_card_eq
    have hcop : Nat.Coprime (Nat.card N) (2^a) := by
      rw [hb]
      exact ((by decide : Nat.Coprime 5 2).pow_left b).pow_right a
    exact hcop.dvd_of_dvd_mul_left (N.card_subgroup_dvd_card.trans hd)
  let : IsCyclic N := isCyclic_of_card_dvd_prime hc
  have haut : ¬ 8 ∣ Nat.card (MulAut N) := by
    rw [IsCyclic.card_mulAut]
    rcases (Nat.dvd_prime Nat.prime_five).mp hc with hc | hc <;> rw [hc] <;> decide
  let f : Y →* MulAut N := MulAut.conjNormal
  have hk : f.ker ≤ N := by
    apply le_trans _ (show centralizer (N : Set Y) ≤ N from by
      change centralizer (pCore 5 Y : Set Y) ≤ pCore 5 Y
      rw [←hf]
      exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs)
    intro y hy
    apply mem_centralizer_iff.mpr
    intro x hx
    have hh := congrArg (fun b : MulAut N => (b ⟨x,hx⟩ : Y)) hy
    change y*x*y⁻¹=x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hcop : Nat.Coprime 8 (Nat.card f.ker) :=
    (by decide : Nat.Coprime 8 5).of_dvd_right ((card_dvd_of_le hk).trans hc)
  apply haut
  apply dvd_trans _ f.range.card_subgroup_dvd_card
  apply hcop.dvd_of_dvd_mul_left
  rwa [←index_ker,card_mul_index]

/-- A unique Sylow involution is fixed by every automorphism of the actual solvable two-five group. -/
theorem fixed_involution
    {Y : Type*} [Group Y] [Finite Y] (hs : Group.IsSolvable Y)
    {a : ℕ} (hd : Nat.card Y ∣ 2^a * 5) (h8 : 8 ∣ Nat.card Y)
    (S : Sylow 2 Y)
    (hu : ∀ x y : S, orderOf x = 2 → orderOf y = 2 → x = y)
    (z : S) (hz : orderOf z = 2) (φ : MulAut Y) : φ z = z := by
  have hN := twoCore_ne_bot hs hd h8
  have hc : 2 ∣ Nat.card (pCore 2 Y) :=
    pCore_isPGroup.card_eq_or_dvd.resolve_left (fun he => hN (card_eq_one.mp he))
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := pCore 2 Y) 2 hc
  have hNS : pCore 2 Y ≤ (S : Subgroup Y) := pCore_isPGroup.le_sylow_of_normal S
  have hxz : (x : Y) = z := congrArg Subtype.val
    (hu ⟨x,hNS x.property⟩ z ((orderOf_coe _).symm.trans ((orderOf_coe x).trans hx)) hz)
  have hzN : (z : Y) ∈ pCore 2 Y := hxz ▸ x.property
  have hφN : φ (z : Y) ∈ pCore 2 Y :=
    characteristic_iff_le_comap.mp inferInstance φ hzN
  exact congrArg Subtype.val (hu ⟨φ z,hNS hφN⟩ z
    ((orderOf_coe _).symm.trans ((φ.orderOf_eq _).trans ((orderOf_coe z).trans hz))) hz)

end Theory.GroupTheory.TwoFive
