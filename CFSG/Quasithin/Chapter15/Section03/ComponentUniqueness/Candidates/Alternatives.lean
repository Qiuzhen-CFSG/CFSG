module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Basic
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.FermatMersenne
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.SU3.OuterSolvable
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# The model and action alternatives to be established

These output propositions retain every clause in 15.3.37 and the alternatives
(i)--(iii) at the start of 15.3.43. Classical models are actual projective
matrix groups with multiplicative equivalences. In a unitary parameter q the
coefficient field has order q² and conjugation is q-Frobenius.

A diagonal outer actor is specified by its literal conjugation on L and a
compatible GL₃ or unitary matrix action on L/O₂(L). The transported action
is required to lie outside the inner automorphisms. Thus the field parameter,
quotient and outer action are connected to the same concrete model.
The residual factors and their set products are kept literally, including
|Y_C| = 3 in 15.3.37(2).

No theorem in this module asserts these alternatives. Their construction from
the earlier local results, 1.1.5, 1.2, and A.3 remains a proof obligation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.37 and the proof of 15.3.43, printed pp.1135 and 1139.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.Candidates
variable {G : Type*} [Group G]

/-- A literal conjugation action on `L`, rather than an unrelated automorphism. -/
def ConjugationOn (L : Subgroup G) (y : G) (α : MulAut L) : Prop :=
  ∀ x : L, (α x : G) = y * (x : G) * y⁻¹

/-- A diagonal outer action on the actual linear quotient `L/O₂(L)`.
The matrix action is transported through the displayed equivalence. -/
def LinearDiagonalOnTwoQuotient (L : Subgroup G) (y : G) (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    ∃ (e : (L ⧸ pCore 2 L) ≃* PSL(3,F)) (α : MulAut L)
      (d : Matrix.GeneralLinearGroup (Fin 3) F),
      ConjugationOn L y α ∧
      Matrix.PSL3.OuterSolvable.linearConj F d ∉ MulAut.innerSubgroup PSL(3,F) ∧
      ∀ x : L, e (QuotientGroup.mk' (pCore 2 L) (α x)) =
        Matrix.PSL3.OuterSolvable.linearConj F d (e (QuotientGroup.mk' (pCore 2 L) x))

/-- The unitary diagonal alternative uses a field of order `q²`, its
`q`-Frobenius Hermitian involution, and actual unitary conjugation. -/
def UnitaryDiagonalOnTwoQuotient (L : Subgroup G) (y : G) (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F)
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F),
    Nat.card F = q ^ 2 ∧ (∀ x, J.conj x = x ^ q) ∧
    ∃ (e : (L ⧸ pCore 2 L) ≃*
        BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
      (α : MulAut L) (d : J.unitarySubgroup),
      ConjugationOn L y α ∧
      J.unitaryConjHom d ∉
        MulAut.innerSubgroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) ∧
      ∀ x : L, e (QuotientGroup.mk' (pCore 2 L) (α x)) =
        J.unitaryConjHom d (e (QuotientGroup.mk' (pCore 2 L) x))

/-- The precise rank-one models retained in 15.3.37(2). -/
def RankOneModel (L : Type*) [Group L] : Prop :=
  (∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 2 (2 ^ n)) ∨
  (∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSU L 3 (2 ^ n)) ∨
  ClassicalGroup.IsPSL L 3 2

/-- All clauses of 15.3.37(2), including the ordinary centralizer and |Y_C|=3. -/
structure RankOneSplit (Yplus L L₀ : Subgroup G) : Prop where
  orbit_eq : L = L₀
  model : RankOneModel L
  product : (Yplus : Set G) =
    (componentPart Yplus L : Set G) * (centralizingPart Yplus L : Set G)
  component_three_part : 3 ^ (Nat.card (componentPart Yplus L)).factorization 3 = 3
  centralizer_card : Nat.card (centralizingPart Yplus L) = 3
  quotient : Nonempty ((Yplus ⧸ pCore 2 Yplus) ≃*
    Multiplicative (Fin 2 → ZMod 3))

/-- All clauses of 15.3.37(3). The outer action uses the same field
parameter as the model, including the central-two-cover alternative. -/
def RankTwoDiagonal (Yplus L L₀ : Subgroup G) : Prop :=
  L = L₀ ∧ componentPart Yplus L ≠ ⊥ ∧
    ∃ y ∈ Yplus, orderOf y = 3 ∧
      (Yplus : Set G) = (componentPart Yplus L : Set G) * (zpowers y : Set G) ∧
      ((∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
          LinearDiagonalOnTwoQuotient L y (2 ^ n)) ∨
        LinearDiagonalOnTwoQuotient L y 4)

/-- The actual three alternatives in 15.3.37, as an output to be proved. -/
def Alternatives15337 (Yplus L L₀ : Subgroup G) : Prop :=
  Yplus ≤ L₀ ∨ RankOneSplit Yplus L L₀ ∨ RankTwoDiagonal Yplus L L₀

/-- The quotient models in case (ii) at the start of 15.3.43.
For the signed rank-three families the congruence is q ≡ -δ (mod 3). -/
def RankOneQuotientModel (L : Type*) [Group L] : Prop :=
  (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) ∨
  (∃ n : ℕ, 0 < n ∧ 2 ^ n % 3 = 2 ∧
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 (2 ^ n)) ∨
  (∃ n : ℕ, 0 < n ∧ 2 ^ n % 3 = 1 ∧
    ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 (2 ^ n)) ∨
  (∃ p : ℕ, IsFermatOrMersennePrime p ∧
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p)

/-- Case (iii) in 15.3.43: the signed congruence is q ≡ ε (mod 3).
Only the assertion about an order-three outer actor is made here; the
stronger product conclusion of 15.3.37 is not inserted into this case. -/
def DiagonalAlternative15343 (Yplus L L₀ : Subgroup G) : Prop :=
  L = L₀ ∧ ∃ y ∈ Yplus, orderOf y = 3 ∧
    ((∃ n : ℕ, 0 < n ∧ 2 ^ n % 3 = 1 ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
        LinearDiagonalOnTwoQuotient L y (2 ^ n)) ∨
      (∃ n : ℕ, 0 < n ∧ 2 ^ n % 3 = 2 ∧ ClassicalGroup.IsPSU L 3 (2 ^ n) ∧
        UnitaryDiagonalOnTwoQuotient L y (2 ^ n)) ∨
      LinearDiagonalOnTwoQuotient L y 4)

/-- Cases (i)--(iii) at the start of 15.3.43. This is a conclusion
interface and makes no assertion that these alternatives hold. -/
def Alternatives15343 (Yplus I L L₀ : Subgroup G) : Prop :=
  (Yplus ≤ theta I ∧ theta I = L₀) ∨
    (L = L₀ ∧ primeRank 3 L = 1 ∧ RankOneQuotientModel L) ∨
    DiagonalAlternative15343 Yplus L L₀

end CFSG.Quasithin.Chapter15.Section03.Candidates
