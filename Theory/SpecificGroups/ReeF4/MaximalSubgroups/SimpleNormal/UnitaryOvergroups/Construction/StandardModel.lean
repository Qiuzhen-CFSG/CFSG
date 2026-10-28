module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.ProjectiveExtension
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# A fixed unitary model for the Ree projective-extension problem

For q = 2^(2m+1), use the identity Hermitian form over GF(q²), with
q-Frobenius as conjugation. `StandardPGU` is the actual image of its full
unitary group in PGL. The special subgroup is the image of the determinant-one
matrices, connected by `projectiveSpecialInclusion`.

The two final definitions are independent geometric proof obligations:
construct an embedding of this one concrete PGU into the Ree root-matrix
group, and conjugate its special image to a supplied unitary simple normal
subgroup of a radical-free maximal subgroup. Neither definition asserts a
solution, a normalizer calculation, or maximal-subgroup exhaustion.

Source: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; case 7 of the unconditional list inside the
proof of Theorem 5 of Himstedt–Nguyen–Tiep, arXiv:0910.4758, p.3.
-/

public noncomputable section

namespace ReeF4.MaximalSubgroups.SimpleNormal.Construction

open Subgroup Matrix BenderSuzuki.MatrixGroups

/-- The quadratic coefficient field, of order q² rather than q. -/
abbrev StandardField (m : ℕ) : Type := GaloisField 2 ((2 * m + 1) * 2)

instance (m : ℕ) : Fintype (StandardField m) := Fintype.ofFinite _

/-- The coefficient-field order in the source convention. -/
theorem standardField_card (m : ℕ) :
    Nat.card (StandardField m) = (2 ^ (2 * m + 1)) ^ 2 := by
  rw [GaloisField.card 2 ((2 * m + 1) * 2) (by omega), pow_mul]

/-- The identity Hermitian form with q-Frobenius conjugation. -/
@[expose] def standardForm (m : ℕ) : HermitianForm 3 (StandardField m) where
  conj := iterateFrobeniusEquiv (StandardField m) 2 (2 * m + 1)
  conj_involutive := by
    intro x
    change (x ^ (2 ^ (2 * m + 1))) ^ (2 ^ (2 * m + 1)) = x
    rw [← pow_mul, ← pow_two, ← standardField_card m, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

/-- The stored conjugation is exactly the required q-power map. -/
theorem standardForm_conj (m : ℕ) (x : StandardField m) :
    (standardForm m).conj x = x ^ (2 ^ (2 * m + 1)) := rfl

/-- The fixed field has order q. -/
theorem standardForm_fixed_card (m : ℕ) :
    Nat.card {x : StandardField m // (standardForm m).conj x = x} = 2 ^ (2 * m + 1) :=
  FiniteField.card_fixed_of_quadratic_frobenius (standardForm m).conj 2
    (2 * m + 1) (by omega) (standardField_card m) (standardForm_conj m)

/-- The full projective unitary group, defined by its actual image in PGL. -/
abbrev StandardPGU (m : ℕ) := (standardForm m).unitarySubgroup.map ProjGenLinGroup.mk

/-- The remaining root-matrix embedding construction for one fixed model.
It makes no assertion about the position of any supplied subgroup. -/
@[expose] def StandardProjectiveEmbeddings : Prop :=
  ∀ m, 1 ≤ m → ∃ j : StandardPGU m →* Model m, Function.Injective j

/-- The remaining conjugacy calculation, conditional on an actual PGU
embedding. This task can be proved independently of constructing the embedding.
The conjugation direction is from the special image of `j` to the supplied
ambient subgroup `S.map M.subtype`; the marking of `S` is not prescribed. -/
@[expose] def StandardSocleConjugacy : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
        Nat.card F = (2 ^ (2 * m + 1)) ^ 2 →
        (∀ x, J.conj x = x ^ (2 ^ (2 * m + 1))) →
        (S ≃* ProjectiveSpecialUnitaryMatrixGroup J) →
        ∀ j : StandardPGU m →* Model m, Function.Injective j →
          ∃ g : Model m,
            ((j.comp (projectiveSpecialInclusion (standardForm m))).range).map
              (MulAut.conj g).toMonoidHom = S.map M.subtype

end ReeF4.MaximalSubgroups.SimpleNormal.Construction
