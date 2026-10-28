module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.Contracts
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.Janko1.Model

/-!
# Source inputs for the two-component model reduction

A.1.34(3a) concerns the central quotient, and its odd linear alternative
allows both exponents one and two. The predicate below preserves that list.
The binary projective group is written as SL₂ using the canonical
characteristic-two isomorphism `Theory.PSL2.sl2QuotientEquiv`.

`SourceA134Three` is the specialization of (3) to an ambient group that is
itself the K-subgroup and has an SQTK cover. This excludes (3b) by its
explicit non-quotient clause. It does not assert that arbitrary quotients
are quasithin. `SemisimpleSectionRankTheorem` is the separate A.2.1(2)
source obligation used to establish that premise.

These definitions assert no source theorem. Centerlessness is subsequently
derived from the section-rank theorem and the proved I.1.2 transfer result,
without a model-specific multiplier input.

Source: Aschbacher--Smith, A.1.34, printed pp.29--30; A.2.1, p.33;
I.1.2 (perfect central covers), p.407; G.9.3, p.356.
-/

@[expose] public section

open scoped MatrixGroups
open Theory.GroupTheory

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions

universe u

/-- The unreduced list in A.1.34(3a), applied to a simple quotient. -/
def QuotientModel (S : Type u) [Group S] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ Nonempty (S ≃* SL(2, GaloisField 2 n))) ∨
  (∃ s : ℕ, 0 < s ∧ Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup s)) ∨
  Nonempty (S ≃* Janko1.Model) ∨
  (∃ (p : ℕ) (_ : Fact p.Prime) (a : ℕ),
    3 < p ∧ 1 ≤ a ∧ a ≤ 2 ∧ Nonempty (S ≃* PSL(2, GaloisField p a)))

/-- Only the nonexceptional clause is consumed, under the source's genuine
SQTK-quotient hypothesis. Quasithinness remains a premise to prove. -/
def SourceA134Three (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X], IsQuasithin X → IsKGroup K X →
    Nonempty (SQTKCover K X) → ∀ (L M : Subgroup X),
      IsComponent X L → IsComponent X M → L ≠ M → Nonempty (L ≃* M) →
        QuotientModel (L ⧸ Subgroup.center L)

/-- A.2.1(2), retaining the actual semisimple section and the SQTK cover.
This is an additional source obligation, not a proved quotient-closure rule. -/
def SemisimpleSectionRankTheorem (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X], IsSQTK K X →
    ∀ (S : Type u) [Group S] [Finite S],
      ChapterA.Section02.IsSectionOf S X → ChapterA.Section02.IsSemisimple S →
        IsStronglyQuasithin S

/-- Independent binary automorphism estimate, supplied by the existing
rank-one owner. -/
def BinaryAutomorphismRankTheorem : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), 2 ≤ n →
    Nat.card F = 2 ^ n → primeRank 2 (MulAut SL(2,F)) ≤ n

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions
