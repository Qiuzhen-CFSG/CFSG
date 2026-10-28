module

public import Theory.GroupTheory.PResidual.TwoThreeComparison
public import Theory.GroupTheory.PResidual.PrimePowerGeneration
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Cubic generation of a two-perfect {2,3}-group

If nine does not divide its order, every element of three-power order has
order one or three. The prime-to-three residual is therefore the cubic
closure. In a {2,3}-group it is the two-residual, so two-perfectness gives
generation by the cubic elements.

Source: the subgroup recovery in Aschbacher–Smith 13.3.9, printed p.887.
-/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]

theorem cubic_closure_eq_top_of_twoPerfect
    (hG:IsPiGroup twoThreePrimes G) (hp:IsPPerfect 2 G) (h9:¬9∣Nat.card G) :
    closure {x:G|orderOf x=3}=⊤ := by
  have he:closure {x:G|∃n:ℕ,x^(3^n)=1}=⊤ := by
    rw [←primeToResidual_eq_closure_prime_power,←twoResidual_eq_primeToResidual_three hG,
      (pResidual_eq_top_iff 2 G).mpr hp]
  apply top_unique
  rw [←he]
  apply (closure_le _).mpr
  rintro x ⟨n,hn⟩
  obtain ⟨k,hkn,hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hn)
  have hk1:k≤1 := by
    by_contra hh
    apply h9
    have hd:3^2∣3^k := pow_dvd_pow 3 (by omega)
    exact hd.trans (hk ▸ _root_.orderOf_dvd_natCard x)
  interval_cases k
  · have hx:x=1 := orderOf_eq_one_iff.mp (by simpa using hk)
    exact hx ▸ one_mem _
  · exact subset_closure (by simpa using hk)
end Subgroup

