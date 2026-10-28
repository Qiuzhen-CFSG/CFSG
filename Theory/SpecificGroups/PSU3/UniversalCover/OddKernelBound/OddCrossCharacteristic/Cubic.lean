module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.Representation.CyclotomicPrimeCyclicity
public import Theory.Representation.GeneralLinearNatural
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# The cubic-factor primes of PSU₃ perfect central kernels

If r ≠ 3 divides q² − q + 1, the coefficient-field order q² has
multiplicative order three modulo r. Lift a projective Sylow r-subgroup
through the actual special-to-projective surjection. Its faithful natural
three-dimensional action identifies it with a subgroup of the units of a
finite endomorphism field, so it is cyclic. Its projective image is cyclic
too, and central transfer excludes r from every finite perfect-cover kernel.
No choice of Gram matrix or bound on the field degree is required.

Source: Aschbacher–Smith I.1.2–I.1.4, printed pp.407–408 (PDF pp.418–419);
GLS3, Theorem 6.1.4, Tables 6.1.2–3. The finite endomorphism-field argument
is the characteristic-independent theorem in CyclotomicPrimeCyclicity.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic

private theorem cubic_order {q r : ℕ} (hq : 1 ≤ q) (hr : r.Prime)
    (hr3 : r ≠ 3) (hd : r ∣ q ^ 2 - q + 1) :
    orderOf ((q : ZMod r) ^ 2) = 3 := by
  let : Fact r.Prime := ⟨hr⟩
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hz : (q : ZMod r) ^ 2 - (q : ZMod r) + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ r).mpr hd
    simpa only [Nat.cast_add, Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_one] using h
  have h3 : (q : ZMod r) ^ 3 = -1 := by
    linear_combination ((q : ZMod r) + 1) * hz
  have h6 : ((q : ZMod r) ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by decide, pow_mul, h3]
    ring
  have hne : (q : ZMod r) ^ 2 ≠ 1 := by
    intro he
    have hqval : (q : ZMod r) = 2 := by linear_combination -hz + he
    have hzero : (3 : ZMod r) = 0 := by rw [hqval] at hz; norm_num at hz ⊢; exact hz
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      ((ZMod.natCast_eq_zero_iff 3 r).mp hzero))
  exact orderOf_eq_prime h6 hne

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- Every Sylow subgroup at a non-three cubic-factor prime is cyclic. -/
theorem sylow_isCyclic_of_dvd_cubic {q r : ℕ} (hq : 1 < q)
    (hr : r.Prime) (hr3 : r ≠ 3) (hd : r ∣ q ^ 2 - q + 1)
    (hcard : Nat.card F = q ^ 2)
    (Q : Sylow r (ProjectiveSpecialUnitaryMatrixGroup J)) : IsCyclic Q := by
  classical
  let : Fact r.Prime := ⟨hr⟩
  let : Fintype F := Fintype.ofFinite F
  have horder := cubic_order (by omega : 1 ≤ q) hr hr3 hd
  have hqnot : ¬ r ∣ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hcard]
    intro hdq
    have hz := (ZMod.natCast_eq_zero_iff (q ^ 2) r).mpr hdq
    rw [Nat.cast_pow] at hz
    rw [hz, orderOf_zero] at horder
    omega
  have hrF : (r : F) ≠ 0 := by
    intro hz
    let : CharP F r := (CharP.charP_iff_prime_eq_zero hr).mpr hz
    obtain ⟨n, _, hn⟩ := FiniteField.card F r
    exact hqnot (hn ▸ dvd_pow_self r n.pos.ne')
  obtain ⟨P, hPQ⟩ := Sylow.mapSurjective_surjective J.specialToProjective_surjective r Q
  let rho : Representation F P (Fin 3 → F) :=
    (Representation.generalLinearNatural 3).comp
      (J.specialSubgroup.subtype.comp (P : Subgroup J.specialSubgroup).subtype)
  have hinj : Function.Injective rho :=
    (Representation.generalLinearNatural_injective 3).comp
      (J.specialSubgroup.subtype_injective.comp (P : Subgroup J.specialSubgroup).subtype_injective)
  let hcyc : IsCyclic P :=
    Representation.CyclotomicPrimeCyclicity.isCyclic_of_minimal_degree P.isPGroup' hrF hqnot
      rho hinj (by simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
        mul_one, ← Nat.card_eq_fintype_card, hcard, Nat.cast_pow, horder, Nat.card_fin] using (le_refl 3))
  have hm : (P : Subgroup J.specialSubgroup).map J.specialToProjective =
      (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [← Sylow.coe_mapSurjective J.specialToProjective_surjective, hPQ]
  rw [← hm]
  exact isCyclic_of_surjective (J.specialToProjective.subgroupMap (P : Subgroup _))
    (J.specialToProjective.subgroupMap_surjective (P : Subgroup _))

/-- The cubic-factor exclusion for the literal kernel of an arbitrary cover. -/
theorem not_dvd_kernel_of_dvd_cubic {q r : ℕ} (hq : 1 < q)
    (hr : r.Prime) (hr3 : r ≠ 3) (hd : r ∣ q ^ 2 - q + 1)
    (hcard : Nat.card F = q ^ 2)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact r.Prime := ⟨hr⟩
  exact f.not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic_of_dvd_cubic J hq hr hr3 hd hcard)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic
