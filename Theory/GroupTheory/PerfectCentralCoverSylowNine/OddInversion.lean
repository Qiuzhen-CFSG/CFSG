module

public import Theory.GroupTheory.PerfectCentralCoverSimultaneousInversion

/-!
# Prime inequality form of simultaneous inversion

The common simultaneous-inversion theorem is defined once in
`PerfectCentralCoverSimultaneousInversion`. For a prime, the inequality
p ≠ 2 supplies its coprimality hypothesis. This wrapper retains the
odd-prime convention used by the Rudvalis central-cover calculations.

Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407.
-/

open scoped commutatorElement
open Subgroup
namespace PerfectCentralCovering

/-- Simultaneous inversion of an odd two-generator Sylow subgroup excludes
its prime from every finite perfect central kernel. -/
public theorem not_dvd_card_kernel_of_simultaneous_inversion_of_ne_two
    {E G : Type*} [Group E] [Finite E] [Group.IsPerfect E] [Group G] [Finite G]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (Q : Sylow p G) (x y r : G)
    (hQ : closure ({x, y} : Set G) = (Q : Subgroup G))
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : ⁅x, y⁆ ≠ 1)
    (hxz : Commute x ⁅x, y⁆) (hyz : Commute y ⁅x, y⁆)
    (hrx : r * x * r⁻¹ = x⁻¹) (hry : r * y * r⁻¹ = y⁻¹)
    (hrz : Commute r ⁅x, y⁆) : ¬ p ∣ Nat.card f.ker := by
  have hp2 : p.Coprime 2 :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun h =>
      hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h))
  exact not_dvd_card_kernel_of_simultaneous_inversion
    f hf hk hp2 Q x y r hQ hx hy hz hxz hyz hrx hry hrz

end PerfectCentralCovering
