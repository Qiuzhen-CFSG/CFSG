module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.LinearCubic

/-!
# Nondefining kernel support in degree four

For an actual finite perfect central cover of PSL₄(F), with |F|=p prime,
every odd kernel prime different from p divides p²−1. The cubic and quartic
branches are discharged by actual cyclic subgroups and Sylow transport in
the imported modules. The remaining linear torus branches and the unitary
family are required before the full nondefining-kernel exclusion is available.

This support theorem concerns the literal given covering homomorphism.
It uses no universal-cover or natural-lift hypothesis. Source:
Aschbacher–Smith A.2.17, printed p.39, with the conventions of
I.1.1–I.1.2, printed p.407.
-/

open PerfectCentralCovering
open scoped MatrixGroups

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining

/-- The linear family is reduced to exactly the quadratic torus support. -/
public theorem linear_prime_dvd_kernel_dvd_sq_sub_one
    {F : Type*} [Field F] [Finite F] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p) (hr2 : r ≠ 2) (hrp : r ≠ p)
    {E : Type*} [Group E] [Finite E] (f : Cover E PSL(4, F))
    (hd : r ∣ Nat.card f.toMonoidHom.ker) : r ∣ p ^ 2 - 1 := by
  by_contra h
  exact linear_not_dvd_kernel_of_not_dvd_sq_sub_one hF hr2 hrp h f hd

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining
