module

public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus.Diagonal

/-!
# Three-primary norm-one parameters

Restrict the norm-one units to their Sylow three-subgroup before forming the
two-parameter diagonal torus. The resulting parameter group is cyclic, has
odd order, and retains the full three-part of q+1. Its projective image
still has the scalar cubic kernel: its order is m²/3 when 3 divides q+1.

Source: Aschbacher–Smith I.1.3(2), I.1.4(2), PDF pp.418–419;
GLS III, Theorem 6.1.4 and Tables 6.1.2–3.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus
@[expose] public noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.OddThreeMatrix
variable {F : Type*} [Field F] (J : HermitianForm 3 F)
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
/-- A Sylow three-subgroup of the cyclic norm-one group. -/
def primarySylow : Sylow 3 (HermitianForm.EvenInner.normOne J) := default
/-- Its injective image in the coefficient-field units. -/
def primary : Subgroup Fˣ :=
  (primarySylow J : Subgroup (HermitianForm.EvenInner.normOne J)).map
    (HermitianForm.EvenInner.normOne J).subtype

theorem primary_norm (u : primary J) : J.conj (u.val : F) * (u.val : F) = 1 := by
  obtain ⟨v, _, hv⟩ := u.property
  have he : v.val = u.val := hv
  rw [← he]
  exact normOne_norm J v

theorem primary_card [Finite F] {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hc : ∀ x, J.conj x = x ^ q) :
    Nat.card (primary J) = 3 ^ (q + 1).factorization 3 := by
  rw [primary, Subgroup.card_map_of_injective (HermitianForm.EvenInner.normOne J).subtype_injective]
  rw [(primarySylow J).card_eq_multiplicity, HermitianForm.EvenInner.normOne_card J hcard hc]

theorem primary_coprime_two [Finite F] : (Nat.card (primary J)).Coprime 2 := by
  rw [primary, Subgroup.card_map_of_injective (HermitianForm.EvenInner.normOne J).subtype_injective,
    (primarySylow J).card_eq_multiplicity]
  exact (by decide : Nat.Coprime 3 2).pow_left _

theorem primary_three_dvd [Finite F] {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hc : ∀ x, J.conj x = x ^ q)
    (hq : 3 ∣ q + 1) : 3 ∣ Nat.card (primary J) := by
  rw [primary, Subgroup.card_map_of_injective (HermitianForm.EvenInner.normOne J).subtype_injective]
  apply (primarySylow J).dvd_card_of_dvd_card
  rwa [HermitianForm.EvenInner.normOne_card J hcard hc]

/-- The chosen parameters really are norm-one field units. -/
theorem primary_le_normOne : primary J ≤ HermitianForm.EvenInner.normOne J := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-- The complementary factor of the norm-one order is prime to three. -/
theorem primary_complement [Finite F] {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hc : ∀ x, J.conj x = x ^ q) :
    ∃ d : ℕ, Nat.card (primary J) * d = q + 1 ∧ ¬ 3 ∣ d := by
  refine ⟨(primarySylow J).index, ?_, (primarySylow J).not_dvd_index⟩
  rw [primary, Subgroup.card_map_of_injective (HermitianForm.EvenInner.normOne J).subtype_injective,
    (primarySylow J).card_mul_index, HermitianForm.EvenInner.normOne_card J hcard hc]

/-- The actual projective three-primary diagonal torus. -/
def primaryTorus (hJ : J.form = 1) := torus J hJ (primary J) (primary_norm J)

/-- Restriction of parameters gives an actual subgroup of the full norm-one torus. -/
theorem primaryTorus_le_normOneTorus (hJ : J.form = 1) :
    primaryTorus J hJ ≤ normOneTorus J hJ := by
  rintro x ⟨⟨a, b⟩, rfl⟩
  refine ⟨(⟨a.val, primary_le_normOne J a.property⟩,
    ⟨b.val, primary_le_normOne J b.property⟩), ?_⟩
  apply Subtype.ext
  rw [diagonalProjective_val, diagonalProjective_val]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [entries]

/-- The order includes the scalar cube-root quotient, at every three-valuation. -/
theorem primaryTorus_card [Finite F] (hJ : J.form = 1) {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hc : ∀ x, J.conj x = x ^ q)
    (hq : 3 ∣ q + 1) :
    Nat.card (primaryTorus J hJ) = Nat.card (primary J) ^ 2 / 3 := by
  rw [primaryTorus, torus_card,
    Nat.gcd_eq_right (primary_three_dvd J hcard hc hq)]

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.OddThreeMatrix
