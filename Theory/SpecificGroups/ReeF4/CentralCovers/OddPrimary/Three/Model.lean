module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Unitary
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Configurations
public import Mathlib.FieldTheory.Finite.GaloisField

/-!+# A concrete unitary monomial group for Ree descent

Over GF(q²), with q = 2^(2m+1), take the identity Hermitian form and its
determinant-one norm-one diagonal matrices together with coordinate
permutations. This retains the scalar subgroup of order three. The geometric
input is an injective map of this particular matrix group into the literal
Ree carrier, together with an ambient element that inverts its diagonal
torus and fixes its coordinate cycle. It requests neither a full centralizer
calculation nor conjugacy of arbitrary order-three elements.

`MonomialRealization` is an unproved geometric obligation, not a theorem.
The associated counting and Sylow construction are proved separately.

Sources: GLS3 Example 2.6.3 (the A₂×A₂ subsystem and exceptional descent)
and Table 4.7.3A (full SU₃ and its graph normalizer). GLS3's half-integer
parameter has square q in our convention.
-/

@[expose] public noncomputable section

namespace ReeF4.CentralCovers.OddPrimary.Three
open Matrix Subgroup BenderSuzuki.MatrixGroups

abbrev QuadraticField (m : ℕ) : Type := GaloisField 2 ((2 * m + 1) * 2)

instance (m : ℕ) : Fintype (QuadraticField m) := Fintype.ofFinite _

theorem quadraticField_card (m : ℕ) :
    Nat.card (QuadraticField m) = (2 ^ (2 * m + 1)) ^ 2 := by
  rw [GaloisField.card 2 ((2 * m + 1) * 2) (by omega), pow_mul]

def form (m : ℕ) : HermitianForm 3 (QuadraticField m) where
  conj := iterateFrobeniusEquiv (QuadraticField m) 2 (2 * m + 1)
  conj_involutive := by
    intro x
    change (x ^ (2 ^ (2 * m + 1))) ^ (2 ^ (2 * m + 1)) = x
    rw [← pow_mul, ← pow_two, ← quadraticField_card m, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

theorem form_conj (m : ℕ) (x : QuadraticField m) :
    (form m).conj x = x ^ (2 ^ (2 * m + 1)) := rfl

theorem form_matrix (m : ℕ) : (form m).form = 1 := rfl

abbrev MonomialGroup (m : ℕ) := Unitary.monomial (form m) (form_matrix m)

/-- The remaining exceptional-descent construction. All equations are on
the full matrix torus, before taking any projective quotient. -/
structure MonomialRealization (m : ℕ) where
  embedding : MonomialGroup m →* ReeF4.Model m
  injective : Function.Injective embedding
  inverter : ReeF4.Model m
  inverts : ∀ a, inverter * embedding (Unitary.normDiagonal (form m) (form_matrix m) a) * inverter⁻¹ =
    embedding (Unitary.normDiagonal (form m) (form_matrix m) a⁻¹)
  fixes_cycle : Commute inverter (embedding (Unitary.cycle (form m) (form_matrix m)))

end ReeF4.CentralCovers.OddPrimary.Three
