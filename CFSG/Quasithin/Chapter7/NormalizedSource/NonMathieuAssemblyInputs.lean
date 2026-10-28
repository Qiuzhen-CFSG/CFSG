module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Actors
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteModels
public import BenderSuzuki.MatrixGroups.Suzuki

/-!
# Contracts for the non-Mathieu source family assembly

The rank-one rows mark the literal component central quotient. The fourth
row retains the covering projection and the absolute half-field tensor of
the original inflated action. Its exponent is the actual Schur degree,
including degree one; the source inequality q>2 concerns the quadratic ratio,
not the exponent or the matrix-field order.

These predicates specify inputs, not a family-selection theorem. The
chosen-module consumer retains the ambient hypotheses of the independent
family sieve and exclusions.

Source: Aschbacher--Smith,3.2.9 and7.0.1, printed pp.582--583,695.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuAssembly
open ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open BenderSuzuki.MatrixGroups

variable {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] {ρ : Representation (ZMod 2) A E} {Q : Subgroup A}

/-- The actual half-field tensor, with its central cover, quotient marking,
Schur degree, dimension and absolute intertwiner. Degree one is retained. -/
def HermitianRow (h : ChapterK.RankOne.SourceHypotheses ρ Q) : Prop :=
  ∃ (B : BinaryField) (C : LinearCover B 3 Q),
    Nonempty ((Q ⧸ center Q) ≃* PSL(3,B.Carrier)) ∧
      letI := inflated_irreducible ρ C h.irreducible
      let n := schurDegree (inflated ρ C)
      0 < n ∧ B.degree = 2 * n ∧ Module.finrank (ZMod 2) E = 9 * n ∧
        HasAbsoluteTwistedModel (inflated ρ C) n

/-- The four non-Mathieu families, marked on the original component
central quotient or its literal inflated action. -/
def SourceFamilies (h : ChapterK.RankOne.SourceHypotheses ρ Q) : Prop :=
  (∃ r : ℕ, 2 ≤ r ∧ ClassicalGroup.IsPSL (Q ⧸ center Q) 2 (2 ^ r)) ∨
  (∃ s : ℕ, 2 ≤ s ∧ ClassicalGroup.IsPSU (Q ⧸ center Q) 3 (2 ^ s)) ∨
  (∃ m : ℕ, 1 ≤ m ∧ Nonempty ((Q ⧸ center Q) ≃* SuzukiMatrixGroup m)) ∨
  HermitianRow h

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuAssembly
