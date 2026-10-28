module

public import Theory.SpecificGroups.HigherLinear.ParabolicGeometry
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular

/-!
# Coordinates for higher-linear Sylow-overgroup placement

The monomial condition records the actual action on the coordinate basis:
column `i` has its unique nonzero entry in row `σ i`. The Bruhat condition
asks for two full upper-unitriangular factors and a determinant-one monomial
factor. The diagonal coefficients of the middle factor are retained over
field extensions of F₂.

These are shared statements for independent proofs of matrix elimination
and the root/cut argument. No factorization or overgroup theorem is assumed
as an instance. Final assembly must supply the factorization proof.
Source: GLS III, §2.6, especially Tits's Theorem 2.6.7; Aschbacher–Smith,
`refs/quasithin.pdf`, printed pp.47–48 and p.74 (PDF pp.58–59 and p.85).
-/

@[expose] public section

open scoped MatrixGroups
namespace Matrix.HigherLinear.ParabolicPlacement

/-- A determinant-one matrix permuting the coordinate lines. Its permutation
sends the column index to the row containing the nonzero entry. -/
def IsMonomial {n : ℕ} {F : Type*} [Field F] (g : SL(n,F)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∃ d : Fin n → F,
    (∀ i, d i ≠ 0) ∧ ∀ i,
      SpecialLinearGroup.toLin' g (Pi.single i 1) = d i • Pi.single (σ i) 1

/-- Literal unitriangular–monomial–unitriangular factorization. Both outer
factors lie in the full unitriangular subgroup over F, not just over F₂. -/
def HasUnitriangularBruhat (n : ℕ) (F : Type*) [Field F] [Finite F] : Prop :=
  ∀ g : SL(n,F),
    ∃ u ∈ Theory.SpecificGroups.LinearSylowNormalizers.unipotent n F,
    ∃ m : SL(n,F), IsMonomial m ∧
    ∃ v ∈ Theory.SpecificGroups.LinearSylowNormalizers.unipotent n F,
      g = u * m * v

end Matrix.HigherLinear.ParabolicPlacement
