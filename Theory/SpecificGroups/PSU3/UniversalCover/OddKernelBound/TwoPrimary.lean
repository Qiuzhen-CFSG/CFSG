module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.TwoPrimary.GeometryData
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.TwoPrimary.LocalTransfer
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.TwoPrimary.Geometry
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.TwoPrimary.UnitaryDerived
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# The odd-parameter PSU₃ two-primary multiplier

The determinant-corrected GU₂ block centralizer has odd index in SU₃.
After projectivization its kernel has odd order. The transfer theorem in
`LocalTransfer` therefore reduces the two-primary multiplier of PSU₃ to
the derived kernels of central two-group extensions of the actual GU₂.

`Geometry` constructs this map for the original arbitrary Hermitian form,
and `UnitaryDerived` proves the local calculation, including at q = 3.
Combining them excludes two from every finite perfect central kernel and
from the literal universal projection, for every positive odd-prime-power
parameter. The prime-or-prime-square specialization discharges `htwo` in
`card_kernel_dvd_gcd_of_primary`; the other primary bounds remain separate.
The conditional local applications are retained as reusable interfaces.

Source: Aschbacher--Smith I.1.3(2), I.1.4(2), printed pp.407--408
(PDF pp.418--419); GLS3, Theorem 6.1.4 and Tables 6.1.2--3.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.TwoPrimary
universe u v
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- Apply the intrinsic GU₂ calculation to the specified projective local
map, then transfer to the original arbitrary perfect central cover. -/
theorem not_two_dvd_kernel_of_unitary_local
    (d : UnitaryLocalData J)
    (hlocal : TwoKernelDerivedTrivial.{max v u, u} d.form.unitarySubgroup)
    {E : Type v} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  apply f.not_two_dvd_kernel_of_local_derived d.subgroup d.odd_index
  exact twoKernelDerivedTrivial_of_odd_surjection d.map d.surjective d.odd_kernel hlocal

/-- The same local reduction for the constructed universal projection,
with its geometric witness and GU₂ calculation explicit. -/
theorem not_two_dvd_universal_kernel_of_unitary_local
    {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he1 : 1 ≤ e)
    (hcard : Nat.card F = (p ^ e) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    (d : UnitaryLocalData J)
    (hlocal : TwoKernelDerivedTrivial.{u, u} d.form.unitarySubgroup) :
    ¬ 2 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  have hq : 2 < p ^ e := hp2.trans_le (Nat.le_self_pow (by omega) p)
  let := projective_isQuasisimple J hq hcard hconj
  exact not_two_dvd_kernel_of_unitary_local J d hlocal
    (universalCover (ProjectiveSpecialUnitaryMatrixGroup J))

/-- Two does not divide any finite perfect central kernel of the actual PSU₃
at an odd prime power. The arbitrary form and extension universe are retained;
the local geometry and derived-kernel premises are both discharged. -/
theorem not_two_dvd_kernel_of_odd_prime_power
    {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 1 ≤ e)
    (hcard : Nat.card F = (p ^ e) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    {E : Type v} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨d⟩ := nonempty_unitaryLocalData_of_odd_prime_power J hp hodd hcard hconj
  refine not_two_dvd_kernel_of_unitary_local J d ?_ f
  exact unitary_twoKernelDerivedTrivial d.form d.gram_eq_one hp hodd he hcard
    (fun x => by rw [d.conj_eq]; exact hconj x)

/-- The exact two-primary input to `card_kernel_dvd_gcd_of_primary`, including
p = 3 and p = 5 at both exponents one and two. -/
theorem not_two_dvd_kernel
    {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he1 : 1 ≤ e) (_he2 : e ≤ 2)
    (hcard : Nat.card F = (p ^ e) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    {E : Type v} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker :=
  not_two_dvd_kernel_of_odd_prime_power J hp hodd he1 hcard hconj f

/-- The actual universal projection has odd-order kernel at every positive
odd-prime-power parameter, with no local input left as a hypothesis. -/
theorem not_two_dvd_universal_kernel_of_odd_prime_power
    {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 1 ≤ e)
    (hcard : Nat.card F = (p ^ e) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (p ^ e)) :
    ¬ 2 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
  obtain ⟨d⟩ := nonempty_unitaryLocalData_of_odd_prime_power J hp hodd hcard hconj
  apply not_two_dvd_universal_kernel_of_unitary_local J hp hodd he hcard hconj d
  exact unitary_twoKernelDerivedTrivial d.form d.gram_eq_one hp hodd he hcard
    (fun x => by rw [d.conj_eq]; exact hconj x)

/-- The universal-kernel two-primary exclusion at the source's prime and
prime-square parameters. -/
theorem not_two_dvd_universal_kernel
    {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he1 : 1 ≤ e) (_he2 : e ≤ 2)
    (hcard : Nat.card F = (p ^ e) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (p ^ e)) :
    ¬ 2 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker :=
  not_two_dvd_universal_kernel_of_odd_prime_power J hp hodd he1 hcard hconj

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.TwoPrimary
