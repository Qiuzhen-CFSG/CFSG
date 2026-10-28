module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.Cubic
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.SingerTorus.Descent

/-!
# The even-field Singer-prime transfer exclusion

The faithful three-dimensional special-unitary action makes every Sylow
subgroup at a prime p > 3 dividing q²−q+1 cyclic. The already proved cubic
argument has no odd-characteristic hypothesis, so it applies to q=2ⁿ.
Cyclic-Sylow transfer excludes p from every finite perfect central-cover
kernel and from the literal universal projection for n≥2. These conclusions
hold for the original arbitrary Hermitian form without an extra torus premise.

The explicit maximal-torus construction is a separate obligation. The
imported Descent module supplies its projective order, index, Sylow placement
and normalizer transport conditional on an actual special-unitary torus.
It does not assert that this torus or its order-three normalizer actor exists.

Source: Aschbacher–Smith I.1.2–I.1.4, printed pp.407–408 (PDF pp.418–419),
and GLS III, Theorems 6.1.4 and 6.5.3(c). The special torus has order q²−q+1;
its projective image has order (q²−q+1)/gcd(3,q+1).
-/

public section

open Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.SingerTorus
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- Cyclicity at the Singer primes for the original arbitrary Hermitian form.
The finite endomorphism-field proof does not require a constructed maximal torus. -/
theorem sylow_isCyclic_of_dvd_singer {q p : ℕ} (hq : 1 < q)
    (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ q ^ 2 - q + 1)
    (hcard : Nat.card F = q ^ 2)
    (S : Sylow p (ProjectiveSpecialUnitaryMatrixGroup J)) : IsCyclic S :=
  OddKernelBound.OddCrossCharacteristic.sylow_isCyclic_of_dvd_cubic J hq hp
    (by omega) hd hcard S

/-- The Singer-prime exclusion in every finite perfect central cover. -/
theorem not_dvd_cover_kernel_of_dvd_singer {q p : ℕ} (hq : 1 < q)
    (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ q ^ 2 - q + 1)
    (hcard : Nat.card F = q ^ 2) {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  exact f.not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic_of_dvd_singer J hq hp hp3 hd hcard)

/-- The remaining cubic-factor branch for the literal even-field universal
projection, with no torus-construction or normalizer premise. -/
theorem not_dvd_universal_kernel_of_dvd_singer {n p : ℕ} (hn : 2 ≤ n)
    (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ¬ p ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  let := projective_isQuasisimple J hq hcard hconj
  exact not_dvd_cover_kernel_of_dvd_singer J (by omega) hp hp3 hd hcard (universalCover _)


/-- An actual standard-form special torus and its normalizer yield the
projective torus in the original form. The two construction premises remain
explicit here; they are not assumed by the kernel exclusion above. -/
theorem exists_configuration_of_standard_special {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (T : Subgroup (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J).specialSubgroup)
    [IsCyclic T]
    (hk : (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J).specialToProjective.ker ≤ T)
    (hT : Nat.card T = q ^ 2 - q + 1)
    (hN : T.relIndex (normalizer (T : Set _)) = 3) :
    ∃ H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      IsCyclic H ∧ Nat.card H = (q ^ 2 - q + 1) / Nat.gcd 3 (q + 1) ∧
      H.index = q ^ 3 * (q - 1) * (q + 1) ^ 2 ∧
      H.relIndex (normalizer (H : Set _)) = 3 := by
  have h := image_configuration
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) T hk hq hT hN hcard hconj
  let := h.1
  exact standard_configuration_transport J hcard hconj _ h.2.1 h.2.2.1 h.2.2.2.1

/-- The literal torus-to-transfer application. This discharges the cyclic
Sylow premise of I.1.2 from the torus's actual embedding and index. -/
theorem not_dvd_cover_kernel_of_special_torus {q p : ℕ} (hq : 1 < q)
    (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ q ^ 2 - q + 1)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (T : Subgroup J.specialSubgroup) [IsCyclic T]
    (hk : J.specialToProjective.ker ≤ T) (hT : Nat.card T = q ^ 2 - q + 1)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, _, hQ⟩ := image_sylow_configuration J T hk hq hT hp hp3 hd hcard hconj
  exact f.not_dvd_card_multiplier_of_isCyclic_sylow
    (fun P => (P.equiv Q).isCyclic.mpr hQ)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.SingerTorus
