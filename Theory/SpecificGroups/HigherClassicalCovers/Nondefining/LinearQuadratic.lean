module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.LinearQuadratic.SplitNorm
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.LinearQuadratic.Split
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.LinearQuadratic.Nonsplit

/-!
# Quadratic-torus primes in degree-four linear covering kernels

For every finite perfect central cover of the literal PSL₄(F), where |F| = p
is an odd prime, no odd prime r different from p and dividing p²−1 divides
the covering kernel. Factoring p²−1 separates the split and nonsplit torus
branches. The split branch uses its rank-three torus and a cubic supplement,
including when r = 3; the nonsplit branch uses two quadratic-field blocks.
Both branches construct the abelian preimages and the indices needed for
central transfer on the given covering homomorphism.

This is the quadratic-prime part of the degree-four linear covering input
used in Aschbacher–Smith A.2.17, printed p.39. It retains all odd p, including
p = 3, before any restriction on p−1 is deduced from quasithinness. Covering
and transfer conventions are those of I.1.1–I.1.2, printed p.407.
-/

open scoped MatrixGroups

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining

/-- Odd quadratic-torus primes do not divide the kernel of any finite perfect
central cover of PSL₄ over a field of odd prime order. -/
public theorem linear_not_dvd_kernel_of_dvd_sq_sub_one
    {F : Type*} [Field F] [Finite F] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p) (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (htwo : r ∣ p ^ 2 - 1)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E PSL(4, F)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  have hfactor : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    calc
      p ^ 2 - 1 = p ^ 2 - 1 ^ 2 := by simp
      _ = (p - 1) * (p + 1) := by rw [Nat.sq_sub_sq]; ac_rfl
  rw [hfactor] at htwo
  rcases (Fact.out : r.Prime).dvd_mul.mp htwo with hminus | hplus
  · exact linear_not_dvd_kernel_of_dvd_sub_one hF hp2 hr2 hrp hminus f
  · exact linear_not_dvd_kernel_of_dvd_add_one hF hp2 hr2 hrp hplus f

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining
