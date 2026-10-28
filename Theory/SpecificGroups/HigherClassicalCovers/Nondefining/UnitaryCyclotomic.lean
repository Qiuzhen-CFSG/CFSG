module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic.QuarticExterior
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Theory.LinearAlgebra.FiniteProjectiveMatrixGroup
public import Theory.GroupTheory.PerfectCentralCover

/-!
# Cyclotomic support of degree-four unitary covering kernels

Over a field of order p², the natural special unitary group embeds in
GL₄(p²). The cyclic-Sylow argument for arbitrary finite fields excludes
every odd nondefining prime outside p⁴−1. This includes all primes in
p²−p+1 allowed by the hypothesis r ∤ p²−1. The proof transports Sylow
subgroups through the actual SU-to-PGL image map for the original form.

For the remaining primes r ∣ p²+1, the actual exterior-square action
over the fixed field has dimension six and scalar-sign kernel. An odd
Sylow subgroup acts faithfully, and the quartic field torus in GL₆(p)
proves its cyclicity. This completes every prime outside p²−1, including
five for PSU₄(3), without a multiplier or universality premise.

Source: the degree-four nondefining-kernel input in Aschbacher–Smith
A.2.17, printed p.39; perfect central coverings and the cyclic-Sylow
exclusion in I.1.1–I.1.2, printed p.407. Only the requested odd
nondefining support is proved; no exact multiplier value is asserted.
-/

open BenderSuzuki.MatrixGroups PerfectCentralCovering
open Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining

variable {F : Type*} [Field F] [Finite F]

/-- Cyclicity descends along the actual projective-image map, with the
original Hermitian form retained. -/
public theorem unitary_sylow_isCyclic_of_special_sylow
    (J : HermitianForm 4 F) {r : ℕ} [Fact r.Prime]
    (hcyclic : ∀ Q : Sylow r J.specialSubgroup, IsCyclic Q)
    (P : Sylow r (ProjectiveSpecialUnitaryMatrixGroup J)) : IsCyclic P := by
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective (project_surjective J) r P
  let := hcyclic Q
  have hc : IsCyclic ((Q : Subgroup J.specialSubgroup).map (project J)) :=
    isCyclic_of_surjective _ ((project J).subgroupMap_surjective (Q : Subgroup J.specialSubgroup))
  rwa [← Sylow.coe_mapSurjective (project_surjective J), hQ] at hc

/-- Transfer applies to every finite perfect central cover of the literal
projective image once the special unitary Sylow calculation is supplied. -/
public theorem unitary_not_dvd_kernel_of_special_sylow
    (J : HermitianForm 4 F) {r : ℕ} [Fact r.Prime]
    (hcyclic : ∀ Q : Sylow r J.specialSubgroup, IsCyclic Q)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker :=
  f.not_dvd_card_multiplier_of_isCyclic_sylow
    (unitary_sylow_isCyclic_of_special_sylow J hcyclic)

/-- The genuine special unitary Sylow subgroups outside p(p⁴−1) are cyclic.
This uses only their faithful natural action over the field of order p². -/
public theorem unitary_special_sylow_isCyclic_of_not_dvd_fourth_sub_one
    (J : HermitianForm 4 F) {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p ^ 2) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (hfour : ¬ r ∣ p ^ 4 - 1) (P : Sylow r J.specialSubgroup) : IsCyclic P := by
  apply UnitaryCyclotomic.subgroup_isCyclic_of_not_dvd_sq_sub_one
    hr2 ?_ ?_ J.specialSubgroup (P : Subgroup J.specialSubgroup) P.isPGroup'
  · rw [hF]
    intro hd
    exact hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) (Fact.out : p.Prime)).mp
      ((Fact.out : r.Prime).dvd_of_dvd_pow hd))
  · simpa only [hF, ← pow_mul] using hfour

/-- The nondefining kernel exclusion outside p⁴−1, without a restriction
on the form or an assumption about its natural central covering. -/
public theorem unitary_not_dvd_kernel_of_not_dvd_fourth_sub_one
    (J : HermitianForm 4 F) {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p ^ 2) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (hfour : ¬ r ∣ p ^ 4 - 1)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker :=
  unitary_not_dvd_kernel_of_special_sylow J
    (unitary_special_sylow_isCyclic_of_not_dvd_fourth_sub_one J hF hr2 hrp hfour) f

private theorem fourth_sub_one (p : ℕ) :
    p ^ 4 - 1 = (p ^ 2 - 1) * (p ^ 2 + 1) := by
  calc
    p ^ 4 - 1 = (p ^ 2) ^ 2 - 1 ^ 2 := by ring_nf
    _ = (p ^ 2 - 1) * (p ^ 2 + 1) := by rw [Nat.sq_sub_sq]; ac_rfl

/-- Among primes outside p²−1, only the quartic unitary primes p²+1
can remain in a perfect central kernel after the linear Sylow argument. -/
public theorem unitary_kernel_prime_dvd_sq_add_one
    (J : HermitianForm 4 F) {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p ^ 2) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (htwo : ¬ r ∣ p ^ 2 - 1)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J))
    (hd : r ∣ Nat.card f.toMonoidHom.ker) : r ∣ p ^ 2 + 1 := by
  by_contra hplus
  apply unitary_not_dvd_kernel_of_not_dvd_fourth_sub_one J hF hr2 hrp ?_ f hd
  rw [fourth_sub_one]
  exact (Fact.out : r.Prime).not_dvd_mul htwo hplus

/-- In particular the complete p²−p+1 branch is excluded, using the
original covering map. No unitary order formula is needed. -/
public theorem unitary_not_dvd_kernel_of_dvd_sq_sub_add_one
    (J : HermitianForm 4 F) {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p ^ 2) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (htwo : ¬ r ∣ p ^ 2 - 1) (hcycl : r ∣ p ^ 2 - p + 1)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  intro hd
  have hplus := unitary_kernel_prime_dvd_sq_add_one J hF hr2 hrp htwo f hd
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp2 : p ≤ p ^ 2 := by nlinarith
  have he : p ^ 2 + 1 - (p ^ 2 - p + 1) = p := by omega
  have hdivp : r ∣ p := he ▸ Nat.dvd_sub hplus hcycl
  exact hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) (Fact.out : p.Prime)).mp hdivp)

/-- Every odd nondefining prime outside p²−1 has cyclic Sylow subgroups
in the actual projective special unitary group of the original form. -/
public theorem unitary_sylow_isCyclic_of_not_dvd_sq_sub_one
    (J : HermitianForm 4 F) {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (hr2 : r ≠ 2) (hrp : r ≠ p) (htwo : ¬ r ∣ p ^ 2 - 1)
    (P : Sylow r (ProjectiveSpecialUnitaryMatrixGroup J)) : IsCyclic P := by
  apply unitary_sylow_isCyclic_of_special_sylow J ?_ P
  intro Q
  by_cases hplus : r ∣ p ^ 2 + 1
  · exact UnitaryCyclotomic.special_sylow_isCyclic_of_dvd_sq_add_one
      J hF hconj hr2 hrp hplus Q
  apply unitary_special_sylow_isCyclic_of_not_dvd_fourth_sub_one J hF hr2 hrp ?_ Q
  rw [fourth_sub_one]
  exact (Fact.out : r.Prime).not_dvd_mul htwo hplus

/-- The complete complementary unitary family: no odd nondefining prime
outside p²−1 divides the kernel of any finite perfect central cover of PSU₄(p).
The original form, its Frobenius and its actual projective image are retained. -/
public theorem unitary_not_dvd_kernel_of_not_dvd_sq_sub_one
    (J : HermitianForm 4 F) {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (hr2 : r ≠ 2) (hrp : r ≠ p) (htwo : ¬ r ∣ p ^ 2 - 1)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker :=
  f.not_dvd_card_multiplier_of_isCyclic_sylow
    (unitary_sylow_isCyclic_of_not_dvd_sq_sub_one J hF hconj hr2 hrp htwo)

/-- In particular five cannot divide a perfect central kernel over PSU₄(3),
closing the prime left by the ambient GL₄(9) order calculation. -/
public theorem unitary_not_five_dvd_kernel_of_card_nine
    (J : HermitianForm 4 F) (hF : Nat.card F = 9) (hconj : ∀ x, J.conj x = x ^ 3)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 5 ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact unitary_not_dvd_kernel_of_not_dvd_sq_sub_one J hF hconj
    (by decide) (by decide) (by decide) f

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining
