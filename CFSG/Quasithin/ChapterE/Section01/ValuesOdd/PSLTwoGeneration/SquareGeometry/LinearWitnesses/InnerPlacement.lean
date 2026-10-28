module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.Structure
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Actors
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.Tori
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.Nine

/-!
# Prime-square PSL₂ local subgroup placement

A proper overgroup of the weak-closure normalizer forces a four-group from
the elementary family to occur in the ambient Sylow. A prime divisor of
an involution torus absent from the corresponding centralizer inside the
overgroup then supplies an escaping dihedral local model through that actor.
The construction retains the literal Sylow intersection and requires no
containment of the whole ambient Sylow in the local subgroup.

For p ≥ 5, the missing-prime calculation includes the genuine subfield
PGL₂(p) overgroups in Dickson's classification. For p = 3, the paired S₄
normalizers in PSL₂(9) supply the escaping subgroup, retaining the two
four-group fusion classes. Together these prove the unconditional inner
placement input of `largeFamilyEscape_of_linear_model_geometry`, including
p = 3 and p = 5. Intrinsic E1 verification remains in `PrimeGeometry.OddSections`.

Source: Aschbacher--Smith, A.2.3(2), E.1.2 and E.1.14(6), printed pp.33,
209--210 and 214; the last cites Aschbacher (1982), Lemma 4.10.
-/

public section

open Subgroup GorensteinWalter

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement

/-- The numerical prime-separation calculation supplies the exact inner
placement input of `largeFamilyEscape_of_linear_model_geometry`. -/
theorem concreteLocalGeometryAt_of_missing_centralizer_primes
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2)
    (T : Sylow 2 (PSL2 F))
    (hsep : ∀ A M : Subgroup (PSL2 F), IsKleinFour A →
      A ≤ (T : Subgroup (PSL2 F)) → IsCoatom M → (T : Subgroup (PSL2 F)) ≤ M →
      ∃ (z : PSL2 F) (r : ℕ), z ∈ A ∧ z ≠ 1 ∧ r.Prime ∧ Odd r ∧
        r ∣ (p ^ 2 - 1) / 2 ∧
        ¬ r ∣ Nat.card ((centralizer ({z} : Set (PSL2 F))).subgroupOf M)) :
    PrimeGeometry.ConcreteLocalGeometryAt T := by
  intro Ω hΩ hlarge M hM hTM hNM
  obtain ⟨A, hAΩ, hAT, hA⟩ := PrimeGeometry.Inner.exists_four_group_actor
    (F := F) ⟨p, 2, hp, hodd, by decide, hF⟩ (MulEquiv.refl (PSL2 F))
    T Ω hΩ hlarge M hM.1 hNM
  obtain ⟨z, r, hzA, hz1, hr, hro, hrq, hrM⟩ := hsep A M hA hAT hM hTM
  exact ⟨A, hAΩ, hAT, hA, local_witness_of_missing_centralizer_prime
    hp hodd hF T A M hA hAT z hzA hz1 hr hro hrq hrM⟩

/-- Every prime-square PSL₂ model has the concrete local geometry required
by the inner branch of `largeFamilyEscape_of_linear_model_geometry`.
All prime-separation and paired-normalizer premises are discharged. -/
theorem concreteLocalGeometryAt
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hlarge : 5 < p ^ 2)
    (hF : Nat.card F = p ^ 2) :
    ∀ T : Sylow 2 (PSL2 F), PrimeGeometry.ConcreteLocalGeometryAt T := by
  intro T
  by_cases hp3 : p = 3
  · subst p
    exact Nine.concreteLocalGeometryAt (by simpa using hF) T
  · have hp5 : 5 ≤ p := by
      have hpge3 : 3 ≤ p := by nlinarith
      obtain ⟨k, hk⟩ := hodd
      omega
    exact concreteLocalGeometryAt_of_missing_centralizer_primes hp hodd hF T
      (CentralizerPrimes.missing_centralizer_prime hp hodd hp5 hF T)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement
