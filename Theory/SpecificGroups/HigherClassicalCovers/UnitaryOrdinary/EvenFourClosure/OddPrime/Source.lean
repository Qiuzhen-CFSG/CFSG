module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime.SplitPrimaryBound
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointIndex

/-!
# All odd-primary kernels of binary unitary four-space covers

The proved local torus calculations force any odd kernel prime to divide q-1.
The exact count of the actual isotropic-point orbit supplies the outstanding
point-parabolic index. The split-primary valuation and torus transfer then
exclude that last possibility. This argument includes q=2; it makes no claim
that its exceptional two-primary multiplier vanishes.

Source: Aschbacher--Smith A.2.18, p.40, and I.1.3--4, pp.407--408.
-/

public section
open BenderSuzuki.MatrixGroups PerfectCentralCovering
open Theory.SpecificGroups.ClassicalUnitary
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime

/-- No odd prime divides any actual binary SU4 covering kernel, including the smallest field. -/
theorem not_dvd_kernel_binary
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {E : Type*} [Group E] [Finite E] (d : Cover E (Standard J)) :
    ¬ p ∣ Nat.card d.toMonoidHom.ker := by
  intro hd
  have hm := kernel_prime_dvd_predecessor J n hn hcard hconj hp d hd
  exact not_dvd_kernel_of_split_point_index_eq J n hn hcard hconj hp hm
    (UnitaryFourPointIndex.binary_point_index J n hn hcard hconj) d hd

/-- The entire kernel is a two-group; no same-universe restriction on the covering group is needed. -/
theorem kernel_isTwoGroup_binary
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {E : Type*} [Group E] [Finite E] (d : Cover E (Standard J)) :
    IsPGroup 2 d.toMonoidHom.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  have heq : p = 2 := by
    by_contra hn2
    let : Fact p.Prime := ⟨hpp⟩
    exact not_dvd_kernel_binary J n hn hcard hconj hn2 d hpd
  norm_num [heq]

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime
