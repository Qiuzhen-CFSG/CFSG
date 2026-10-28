module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.PrimeField
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.PrimeSquare
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.TwoPrimary
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic
public import Theory.SpecificGroups.SU3.OddThreeLocal.CyclicSylow
public import Mathlib.Data.Nat.Factors

/-!
# The odd-parameter PSU₃ multiplier bound

For q = p^e, p an odd prime and 1 ≤ e ≤ 2, every finite perfect central
cover of the actual PSU(J) has kernel order dividing gcd(3,q+1).
The constructed universal projection therefore has kernel order at most
gcd(3,q+1), including p = 3 and p = 5 at both exponents.

The defining-prime calculations for prime and prime-square parameters,
the GU₂ two-primary calculation and the cross-characteristic torus bounds
exclude every prime other than three and exclude nine. Cyclic Sylow
three-subgroups exclude three when q ≡ 1 modulo three. Prime factorization
then gives the claimed divisibility. All local witnesses and transports to
arbitrary Hermitian forms are supplied by the imported proofs.

The earlier conditional primary reductions remain available. The final
`card_kernel_dvd_gcd`, `universal_kernel_dvd_gcd` and `universal_kernel_bound`
discharge all their extra premises. The scalar kernel of SU(J) → PSU(J)
is not used as an upper bound on an arbitrary perfect central cover.

Source: Aschbacher–Smith I.1.3(2), I.1.4(2), printed pp.407–408
(PDF pp.418–419), with A.2.2–3; GLS3, Theorem 6.1.4 and Tables 6.1.2–3.
-/

public section

open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- Cyclic Sylow three-subgroups exclude three from every perfect-cover kernel. -/
theorem not_three_dvd_kernel_of_mod_one {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (hmod : q % 3 = 1) {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
  apply f.not_dvd_card_multiplier_of_isCyclic_sylow
  intro S
  exact OddThreeLocal.cyclic_three_sylow_of_mod_one J q hq hmod hcard
    (card_fixed J hcard hconj) S

/-- Three is excluded at square parameters away from characteristic three. -/
theorem not_three_dvd_kernel_of_square {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hcard : Nat.card F = (p ^ 2) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ 2))
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
  have hm0 : p % 3 ≠ 0 := by
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.dvd_of_mod_eq_zero h)).symm
  have hm : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have hmod : (p ^ 2) % 3 = 1 := by
    rcases hm with hm | hm <;> simp [Nat.pow_mod, hm]
  exact not_three_dvd_kernel_of_mod_one J (one_lt_pow₀ hp.one_lt (by decide))
    hcard hconj hmod f

private theorem dvd_three_of_primary {n : ℕ} (hn : n ≠ 0)
    (hprimes : ∀ r : ℕ, r.Prime → r ≠ 3 → ¬ r ∣ n) (h9 : ¬ 9 ∣ n) : n ∣ 3 := by
  have he : n = 3 ^ n.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hn (fun hr hd => by
      by_contra hne
      exact hprimes _ hr hne hd)
  have hk : n.primeFactorsList.length ≤ 1 := by
    by_contra h
    apply h9
    rw [he]
    exact pow_dvd_pow 3 (by omega : 2 ≤ n.primeFactorsList.length)
  rw [he]
  simpa only [pow_one] using pow_dvd_pow 3 hk

/-- Assemble the primary bounds on an arbitrary cover, discharging the prime-field defining part and the cyclic three-primary cases. -/
theorem card_kernel_dvd_gcd_of_primary {p e : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J))
    (hsquare : e = 2 → ¬ p ∣ Nat.card f.toMonoidHom.ker)
    (htwo : ¬ 2 ∣ Nat.card f.toMonoidHom.ker)
    (hother : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p →
      ¬ r ∣ Nat.card f.toMonoidHom.ker)
    (hthree : (p ^ e) % 3 = 2 → ¬ 9 ∣ Nat.card f.toMonoidHom.ker) :
    Nat.card f.toMonoidHom.ker ∣ Nat.gcd 3 (p ^ e + 1) := by
  have hdef : ¬ p ∣ Nat.card f.toMonoidHom.ker := by
    rcases (show e = 1 ∨ e = 2 by omega) with rfl | he
    · exact not_defining_prime_dvd_kernel J hp hodd
        (by simpa only [pow_one] using hcard)
        (by simpa only [pow_one] using hconj) f
    · exact hsquare he
  have hnot3 (hm : (p ^ e) % 3 ≠ 2) : ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
    by_cases hp3 : p = 3
    · simpa only [hp3] using hdef
    have hmod0 : (p ^ e) % 3 ≠ 0 := by
      intro h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h))).symm
    have hmod : (p ^ e) % 3 = 1 := by omega
    exact not_three_dvd_kernel_of_mod_one J
      (one_lt_pow₀ hp.one_lt (by omega)) hcard hconj hmod f
  have hd3 : Nat.card f.toMonoidHom.ker ∣ 3 := by
    apply dvd_three_of_primary (Nat.ne_of_gt Nat.card_pos)
    · intro r hr hr3
      by_cases hr2 : r = 2
      · simpa only [hr2] using htwo
      by_cases hrp : r = p
      · simpa only [hrp] using hdef
      exact hother r hr hr2 hr3 hrp
    · by_cases hm : (p ^ e) % 3 = 2
      · exact hthree hm
      · exact fun h => hnot3 hm ((by decide : 3 ∣ 9).trans h)
  apply Nat.dvd_gcd hd3
  rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with hn | hn
  · rw [hn]
    exact one_dvd _
  · have hm : (p ^ e) % 3 = 2 := by
      by_contra hm
      exact hnot3 hm (by rw [hn])
    rw [hn]
    exact Nat.dvd_of_mod_eq_zero (by omega)

/-- Apply the primary reduction to the actual universal cover. The four displayed primary premises remain mathematical obligations. -/
theorem universal_kernel_bound_of_primary {p e : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    (hsquare : e = 2 → ¬ p ∣ Nat.card (PerfectCentralCovering.universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (htwo : ¬ 2 ∣ Nat.card (PerfectCentralCovering.universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hother : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p →
      ¬ r ∣ Nat.card (PerfectCentralCovering.universalProjection
        (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hthree : (p ^ e) % 3 = 2 → ¬ 9 ∣ Nat.card (PerfectCentralCovering.universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker) :
    Nat.card (PerfectCentralCovering.universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker ≤ Nat.gcd 3 (p ^ e + 1) := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  have hq : 2 < p ^ e := hp2.trans_le (Nat.le_self_pow (by omega) p)
  let := projective_isQuasisimple J hq hcard hconj
  have hd := card_kernel_dvd_gcd_of_primary J hp hodd he1 he2 hcard hconj
    (PerfectCentralCovering.universalCover (ProjectiveSpecialUnitaryMatrixGroup J))
    hsquare htwo hother hthree
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by decide)) hd

/-- Every finite perfect central cover has kernel order dividing gcd(3,q+1)
at the source's odd prime and prime-square parameters. All primary inputs
are discharged, including those at p = 3 and p = 5. -/
theorem card_kernel_dvd_gcd {p e : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card f.toMonoidHom.ker ∣ Nat.gcd 3 (p ^ e + 1) := by
  apply card_kernel_dvd_gcd_of_primary J hp hodd he1 he2 hcard hconj f
  · rintro rfl
    exact PrimeSquare.not_defining_prime_dvd_kernel J f hp hodd hcard hconj
  · exact TwoPrimary.not_two_dvd_kernel J hp hodd he1 he2 hcard hconj f
  · intro r hr hr2 hr3 hrp
    exact OddCrossCharacteristic.not_dvd_kernel J hp he1 hr hr2 hr3 hrp hcard hconj f
  · intro hm
    exact OddCrossCharacteristic.not_nine_dvd_kernel J hcard hconj hm f

/-- Divisibility for the literal constructed universal projection, with no
additional multiplier or local-geometry premise. -/
theorem universal_kernel_dvd_gcd {p e : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e)) :
    Nat.card (PerfectCentralCovering.universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker ∣ Nat.gcd 3 (p ^ e + 1) := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  have hq : 2 < p ^ e := hp2.trans_le (Nat.le_self_pow (by omega) p)
  let := projective_isQuasisimple J hq hcard hconj
  exact card_kernel_dvd_gcd J hp hodd he1 he2 hcard hconj
    (PerfectCentralCovering.universalCover (ProjectiveSpecialUnitaryMatrixGroup J))

/-- The source odd-parameter PSU₃ universal-kernel upper bound for every
Hermitian form, every odd prime, and both permitted exponents. -/
theorem universal_kernel_bound {p e : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e)) :
    Nat.card (PerfectCentralCovering.universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker ≤ Nat.gcd 3 (p ^ e + 1) :=
  Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by decide))
    (universal_kernel_dvd_gcd J hp hodd he1 he2 hcard hconj)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound
