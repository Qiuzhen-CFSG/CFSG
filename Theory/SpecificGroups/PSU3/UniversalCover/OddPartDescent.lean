module

public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound
public import Theory.GroupTheory.CoveringComparisonKernelCard
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Unitary cover descent from the odd part of the universal kernel

The constructed universal cover maps onto the actual SU₃ scalar cover.
Its comparison kernel is a two-group as soon as the odd-primary bounds
leave exactly the scalar factor gcd(3,q+1). In a target with trivial
two-core that comparison kernel vanishes. The resulting map from SU₃
retains the specified projection to PSU₃; SU₃ universality is not needed.

The even and odd parameter theorems retain precisely the outstanding
odd-primary calculations. No exclusion of two from the universal kernel
is assumed. The final theorem applies the odd-parameter primary assembly
directly to an original odd-center quotient, as used in A.2.17.

Source: Aschbacher–Smith A.2.17 and A.3.6, printed pp.39–40 and 43–45;
the covering convention and scalar kernels are I.1.1–I.1.4, pp.407–408.
-/

public section
noncomputable section

open Subgroup Theory.GroupTheory PerfectCentralCovering
open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddPartDescent
universe u v
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- Odd-primary control of the constructed universal kernel gives the
prescribed scalar-cover lift to every quasisimple target with trivial O₂. -/
theorem exists_lift_of_odd_primary {q : ℕ} (hq : 2 < q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (hother : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 →
      ¬ r ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hnot3 : q % 3 ≠ 2 →
      ¬ 3 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hnine : q % 3 = 2 →
      ¬ 9 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    {L : Type v} [Group L] [Finite L] [IsQuasisimple L]
    (f : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f)
    (hcore : pCore 2 L = ⊥) :
    ∃ k : J.specialSubgroup →* L, Function.Surjective k ∧
      f.comp k = J.specialToProjective := by
  let := special_isQuasisimple J hq hcard hconj
  let := projective_isQuasisimple J hq hcard hconj
  let c := universalQuasisimpleCover (ProjectiveSpecialUnitaryMatrixGroup J)
  let π := covering J
  have hcH : Covering.IsUniversal.{u,u,u} c := universalQuasisimpleCover_isUniversal _
  let a := hcH.lift π
  have ha := hcH.lift_fac π
  have hcount : Nat.card c.toMonoidHom.ker =
      Nat.card a.toMonoidHom.ker * Nat.gcd 3 (q + 1) := by
    have h := kernel_card_eq_mul_of_surjective_factor
      c.toMonoidHom π.toMonoidHom a.toMonoidHom π.surjective a.surjective
      (congrArg Covering.toMonoidHom ha)
    change Nat.card c.toMonoidHom.ker =
      Nat.card a.toMonoidHom.ker * Nat.card (covering J).toMonoidHom.ker at h
    simpa only [covering_toMonoidHom, card_kernel J hcard hconj] using h
  have htwo : IsPGroup 2 a.toMonoidHom.ker := by
    apply IsPGroup.of_card
    apply Nat.eq_prime_pow_of_unique_prime_dvd (Nat.ne_of_gt Nat.card_pos)
    intro r hr hdr
    by_contra hr2
    have hd : r ∣ Nat.card c.toMonoidHom.ker := by
      rw [hcount]
      exact dvd_mul_of_dvd_left hdr _
    by_cases hr3 : r = 3
    · subst r
      by_cases hm : q % 3 = 2
      · apply hnine hm
        change 9 ∣ Nat.card c.toMonoidHom.ker
        have hg : Nat.gcd 3 (q + 1) = 3 := by
          rw [Nat.gcd_comm]
          exact Nat.gcd_eq_right_iff_dvd.mpr (Nat.dvd_of_mod_eq_zero (by omega))
        rw [hcount, hg]
        exact Nat.mul_dvd_mul hdr (dvd_refl 3)
      · exact hnot3 hm hd
    · exact hother r hr hr2 hr3 hd
  let g : Covering L (ProjectiveSpecialUnitaryMatrixGroup J) := ⟨f, hf⟩
  have hcL : Covering.IsUniversal.{u,u,v} c := universalQuasisimpleCover_isUniversal _
  obtain ⟨k, hk⟩ := hcL.exists_covering_of_pGroup_kernel (p := 2) a π ha htwo g hcore
  have hh := congrArg Covering.toMonoidHom hk
  change f.comp k.toMonoidHom = (covering J).toMonoidHom at hh
  rw [covering_toMonoidHom] at hh
  exact ⟨k.toMonoidHom, k.surjective, hh⟩

/-- Characteristic-two descent, including q=8. Only primes above three
and the possible extra three-primary factor remain to be excluded. -/
theorem exists_lift_even {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hlarge : ∀ r : ℕ, r.Prime → 3 < r →
      ¬ r ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hnine : Odd n →
      ¬ 9 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    {L : Type v} [Group L] [Finite L] [IsQuasisimple L]
    (f : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f)
    (hcore : pCore 2 L = ⊥) :
    ∃ k : J.specialSubgroup →* L, Function.Surjective k ∧
      f.comp k = J.specialToProjective := by
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  apply exists_lift_of_odd_primary J hq hcard hconj
    (fun r hr hr2 hr3 => hlarge r hr (by have := hr.two_le; omega)) _ _ f hf hcore
  · intro hm
    have he : Even n := by
      rcases Nat.even_or_odd n with he | ⟨k, hk⟩
      · exact he
      · exfalso
        apply hm
        rw [hk, pow_succ, pow_mul]
        simp [Nat.mul_mod, Nat.pow_mod]
    exact EvenKernelBound.not_three_dvd_universal_kernel_of_even J hn he hcard hconj
  · intro hm
    apply hnine
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ho
    · exfalso
      rw [hk, ← two_mul, pow_mul] at hm
      norm_num [Nat.pow_mod] at hm
    · exact ho

/-- Odd prime and prime-square descent. Prime-field defining exclusion
and cyclic-Sylow three-exclusion are discharged by their proved theorems. -/
theorem exists_lift_odd {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    (hsquare : e = 2 →
      ¬ p ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hother : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p →
      ¬ r ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hnine : (p ^ e) % 3 = 2 →
      ¬ 9 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    {L : Type v} [Group L] [Finite L] [IsQuasisimple L]
    (f : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f)
    (hcore : pCore 2 L = ⊥) :
    ∃ k : J.specialSubgroup →* L, Function.Surjective k ∧
      f.comp k = J.specialToProjective := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  have hq : 2 < p ^ e := hp2.trans_le (Nat.le_self_pow (by omega) p)
  let := projective_isQuasisimple J hq hcard hconj
  have hdef : ¬ p ∣ Nat.card (universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
    rcases (show e = 1 ∨ e = 2 by omega) with rfl | he
    · exact OddKernelBound.not_defining_prime_dvd_kernel J hp hodd
        (by simpa only [pow_one] using hcard)
        (by simpa only [pow_one] using hconj) (universalCover _)
    · exact hsquare he
  apply exists_lift_of_odd_primary J hq hcard hconj _ _ hnine f hf hcore
  · intro r hr hr2 hr3
    by_cases hrp : r = p
    · simpa only [hrp] using hdef
    · exact hother r hr hr2 hr3 hrp
  · intro hm
    by_cases hp3 : p = 3
    · simpa only [hp3] using hdef
    have hm0 : (p ^ e) % 3 ≠ 0 := by
      intro h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h))).symm
    exact OddKernelBound.not_three_dvd_kernel_of_mod_one J (by omega)
      hcard hconj (by omega) (universalCover _)

/-- The A.2 odd-center input supplies the missing two-exclusion on the
original quotient map itself; no universal two-primary theorem is used. -/
theorem center_card_dvd_gcd_of_odd_center {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    {L : Type v} [Group L] [Finite L] [Group.IsPerfect L]
    (j : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hcenter : Odd (Nat.card (center L)))
    (hsquare : e = 2 → ¬ p ∣ Nat.card (center L))
    (hother : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p →
      ¬ r ∣ Nat.card (center L))
    (hnine : (p ^ e) % 3 = 2 → ¬ 9 ∣ Nat.card (center L)) :
    Nat.card (center L) ∣ Nat.gcd 3 (p ^ e + 1) := by
  simpa only [centralQuotientCover_ker] using
    OddKernelBound.card_kernel_dvd_gcd_of_primary J hp hodd he1 he2 hcard hconj
      (centralQuotientCover j)
      (by simpa only [centralQuotientCover_ker] using hsquare)
      (by simpa only [centralQuotientCover_ker] using hcenter.not_two_dvd_nat)
      (by simpa only [centralQuotientCover_ker] using hother)
      (by simpa only [centralQuotientCover_ker] using hnine)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddPartDescent
