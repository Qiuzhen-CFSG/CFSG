module

public import Theory.SpecificGroups.ProjectiveLinearThree
public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental
public import Mathlib.GroupTheory.Index

/-!
# Three-divisibility of unitary groups in every dimension

The actual PSU₂–PSL₂ comparison works over both odd and even fixed fields.
Consequently the covering SU₂ also has order divisible by three. In dimensions
at least three its identity-form block injects into the projective unitary group;
orthonormalization transports that conclusion to every stored Hermitian form.
This uses the precise q-Frobenius convention of the classical catalogue.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1.1.5(3) and 15.3.34; Huppert II.10.4 supplies orthonormalization.
-/

public noncomputable section
namespace Theory.SpecificGroups.PrimeToFifteen.Classical
open Matrix BenderSuzuki.MatrixGroups
open ClassicalUnitary
variable {F : Type*} [Field F] [Finite F]

/-- The two-dimensional unitary alias has order divisible by three. -/
theorem unitaryTwo_three_dvd (J : HermitianForm 2 F) {q : ℕ}
    (hq : IsPrimePow q) (hc : Nat.card F = q ^ 2)
    (hj : ∀ x, J.conj x = x ^ q) :
    3 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have he : Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃*
      ProjectiveSpecialLinearGroup (Fin 2) (FixedBy.subfield F J.conj)) := by
    rcases Nat.even_or_odd q with hqeven | hqodd
    · let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := by
        apply ringChar.of_eq
        apply FiniteField.even_card_iff_char_two.mpr
        rw [← Nat.card_eq_fintype_card, hc]
        exact Nat.mod_eq_zero_of_dvd
          (even_iff_two_dvd.mp (hqeven.pow_of_ne_zero (by decide : (2 : ℕ) ≠ 0)))
      exact UnitaryRootNormalizer.nonempty_projectiveTwoEquiv J hc
        (J.fixed_card_prime_power hq hc hj)
    · exact J.nonempty_projectiveTwoEquiv_odd hq hqodd hc hj
  obtain ⟨e⟩ := he
  rw [Nat.card_congr e.toEquiv]
  exact ProjectiveSpecialLinearGroup.three_dvd_card _ 2 le_rfl

/-- All projective unitary carriers of dimension at least two have a factor three. -/
theorem unitary_three_dvd {n q : ℕ} (J : HermitianForm n F) (hn : 2 ≤ n)
    (hq : IsPrimePow q) (hc : Nat.card F = q ^ 2)
    (hj : ∀ x, J.conj x = x ^ q) :
    3 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  by_cases htwo : n = 2
  · subst n
    exact unitaryTwo_three_dvd J hq hc hj
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n-2, by omega⟩
  let : NeZero k := ⟨by omega⟩
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    (2+k) J q hc (J.fixed_card_prime_power hq hc hj)
  rw [Nat.card_congr (HermitianForm.IdentityGram.projectiveEquiv J C hC).toEquiv]
  let I := OddFundamental.form J.conj J.conj_involutive 2
  have hI : 3 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup I) :=
    unitaryTwo_three_dvd I hq hc hj
  have hSU : 3 ∣ Nat.card I.specialSubgroup := hI.trans
    (Subgroup.card_dvd_of_surjective (ProjectiveKernel.project I)
      (ProjectiveKernel.project_surjective I))
  exact hSU.trans (Subgroup.card_dvd_of_injective
    (OddFundamental.projectLeft J.conj J.conj_involutive (m := 2) (n := k))
    (OddFundamental.projectLeft_injective _ _))

end Theory.SpecificGroups.PrimeToFifteen.Classical
