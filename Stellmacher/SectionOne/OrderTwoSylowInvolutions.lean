module

public import Stellmacher.SectionOne.Defs
public import Mathlib.GroupTheory.Transfer

/-!
# Involutions when a Sylow 2-subgroup has order two

This module isolates the elementary group-theoretic input for the order-two
base case in the proof of Stellmacher (1.6).  If a finite group has a Sylow
2-subgroup `S` of order two, distinct involutions cannot commute, while the
product of any two involutions lies in `O_{2'}(G)` and has odd order.

The proof uses Burnside transfer.  Since `S` has prime order it is cyclic,
and because 2 is the least prime divisor of `|G|`, the transfer kernel is a
normal subgroup of odd order.  An involution cannot lie in that kernel, so
every involution has the unique nonidentity image in `S`.  Products of two
involutions therefore belong to the kernel, which is contained in the
`2'`-core.  Finally, commuting distinct involutions would have an involutory
product, contradicting the odd-order conclusion.

Source: the order-two base case in `refs/latex/stellmacher-n-group.tex`,
line 440.
-/

namespace Stellmacher.SectionOne

universe u

/-- The involution structure forced by a Sylow 2-subgroup of order two. -/
public theorem order_two_sylow_involution_structure
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (hScard : Nat.card (S : Subgroup G) = 2) :
    (∀ {x y : G}, IsInvolution x → IsInvolution y → x ≠ y →
      ¬ Commute x y) ∧
      (∀ {x y : G}, IsInvolution x → IsInvolution y →
        x * y ∈ pPrimeCore 2 G ∧ Odd (orderOf (x * y))) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo_dvd_G : 2 ∣ Nat.card G := by
    rw [← hScard]
    exact Subgroup.card_subgroup_dvd_card (S : Subgroup G)
  have hmin : (Nat.card G).minFac = 2 :=
    (Nat.minFac_eq_two_iff (Nat.card G)).2 htwo_dvd_G
  have hScyclic : IsCyclic S := isCyclic_of_prime_card hScard
  let hNC : Subgroup.normalizer (S : Set G) ≤
      Subgroup.centralizer (S : Set G) :=
    hScyclic.normalizer_le_centralizer hmin
  let f : G →* S := MonoidHom.transferSylow S hNC
  let N : Subgroup G := f.ker
  have hNnot : ¬ 2 ∣ Nat.card N := by
    simpa [N, f] using MonoidHom.not_dvd_card_ker_transferSylow S hNC
  have hNcop : Nat.Coprime 2 (Nat.card N) :=
    Nat.prime_two.coprime_iff_not_dvd.mpr hNnot
  have hNnormal : N.Normal := by infer_instance
  have hNlecore : N ≤ pPrimeCore 2 G := le_sSup ⟨hNnormal, hNcop⟩
  have hproduct : ∀ {x y : G}, IsInvolution x → IsInvolution y →
      x * y ∈ pPrimeCore 2 G ∧ Odd (orderOf (x * y)) := by
    intro x y hx hy
    have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
    have hyorder : orderOf y = 2 := orderOf_eq_prime hy.2 hy.1
    have hfxne : f x ≠ 1 := by
      intro hfx
      have hxN : x ∈ N := by
        change f x = 1
        exact hfx
      apply hNnot
      rw [← hxorder]
      exact Subgroup.orderOf_dvd_natCard N hxN
    have hfyne : f y ≠ 1 := by
      intro hfy
      have hyN : y ∈ N := by
        change f y = 1
        exact hfy
      apply hNnot
      rw [← hyorder]
      exact Subgroup.orderOf_dvd_natCard N hyN
    obtain ⟨t, _htne, htunique⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hScard
    have hfxy : f x = f y :=
      (htunique (f x) hfxne).trans (htunique (f y) hfyne).symm
    have hxyN : x * y ∈ N := by
      change f (x * y) = 1
      rw [map_mul, hfxy, ← pow_two, ← map_pow, hy.2, map_one]
    have hxycore : x * y ∈ pPrimeCore 2 G := hNlecore hxyN
    refine ⟨hxycore, ?_⟩
    have hcoreodd : Odd (Nat.card (pPrimeCore 2 G)) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))
    exact Odd.of_dvd_nat hcoreodd
      (Subgroup.orderOf_dvd_natCard (pPrimeCore 2 G) hxycore)
  refine ⟨?_, hproduct⟩
  intro x y hx hy hxyne hcomm
  have hyorder : orderOf y = 2 := orderOf_eq_prime hy.2 hy.1
  have hprodne : x * y ≠ 1 := by
    intro hprod
    have hxeq : x = y⁻¹ := mul_eq_one_iff_eq_inv.mp hprod
    exact hxyne (hxeq.trans (inv_eq_self_of_orderOf_eq_two hyorder))
  have hprodsq : (x * y) ^ 2 = 1 := by
    rw [hcomm.mul_pow, hx.2, hy.2, one_mul]
  have hprodorder : orderOf (x * y) = 2 :=
    orderOf_eq_prime hprodsq hprodne
  have hprododd := (hproduct hx hy).2
  rw [hprodorder] at hprododd
  obtain ⟨k, hk⟩ := hprododd
  omega

end Stellmacher.SectionOne

