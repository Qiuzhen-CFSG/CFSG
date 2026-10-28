module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.Reduction
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.GraphComparison

/-!
# Remaining rank inputs for the odd-prime unitary inspection

The inner branch needs the derived centralizer rank in the actual projective
unitary model. The outer calculation identifies the full fixed group with
the ternary special orthogonal group over the fixed field; its three-rank
bound is the second independent input. These definitions state obligations,
and do not assert that either bound has been proved.

Source: Aschbacher–Smith E.6.18, printed p.252, and Theorem C, printed p.33.
-/

public section
open Theory.GroupTheory BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie.UnitaryThreeFixed

/-- Inner involution rank calculation, retaining the genuine projective model. -/
@[expose] def InnerDerivedThreeRank (p : ℕ) : Prop :=
  ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E),
    IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) →
    Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) →
    ∀ k : ProjectiveSpecialUnitaryMatrixGroup J, orderOf (MulAut.conj k) = 2 →
      primeRank 3 (commutator (MulAut.conj k).fixedSubgroup) ≤ 1

/-- Three-rank of the actual ternary orthogonal matrix group over a prime field. -/
@[expose] def OrthogonalThreeRank (p : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = p →
    primeRank 3 (splitOrthogonalForm K).specialSubgroup ≤ 1

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie.UnitaryThreeFixed
