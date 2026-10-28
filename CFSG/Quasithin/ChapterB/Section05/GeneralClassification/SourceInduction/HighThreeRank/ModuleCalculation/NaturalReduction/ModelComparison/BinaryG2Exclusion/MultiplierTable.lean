module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ClassificationModels.Families
public import Theory.GroupTheory.PerfectCentralCoverRank

/-!
# The complete earlier multiplier table used in the binary G₂ exclusion

This module states the universal I.1.3 input, including its exhaustive list
and the actual multiplier isomorphism in each of its six rows. It does not
assert the table. Every named simple-group condition uses a genuine carrier
equivalence; the multiplier is the kernel of the constructed universal
perfect central cover of I.1.1. The two noncyclic rows are retained explicitly.

The permitted earlier-source producer is `qt-i-01`; its degree-three branch
includes `qt-i01-lie-a2`. No B.5.6, B.5.7, recognition, natural-action or
binary-G₂ kernel assertion occurs in this input. Its consumer proves the
binary-G₂ component exclusion by eliminating the relevant rows and mapping
the universal kernel onto the actual component-cover kernel.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.1.1–3, printed p.407. This definition retains all six clauses of I.1.3,
including the exclusion of L₃(4) in row (2), q ≠ 9 in row (1), and
unitary fixed-field conventions.
-/

@[expose] public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion
universe u

/-- The six multiplier types in all six rows of I.1.3. -/
inductive MultiplierShape
  | two | three | six | twelve | elementaryFour | exceptionalFortyEight

/-- The actual finite abelian group in the corresponding source row. -/
def MultiplierShape.Carrier : MultiplierShape → Type
  | .two => Multiplicative (ZMod 2)
  | .three => Multiplicative (ZMod 3)
  | .six => Multiplicative (ZMod 6)
  | .twelve => Multiplicative (ZMod 12)
  | .elementaryFour => Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
  | .exceptionalFortyEight =>
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) × Multiplicative (ZMod 3)

instance MultiplierShape.carrierGroup (r : MultiplierShape) : Group r.Carrier := by
  cases r <;> unfold MultiplierShape.Carrier <;> infer_instance

/-- All source model conditions, through actual carrier equivalences.
Finite field witnesses in `IsPSL` enforce the prime-power restriction.
The unitary parameter is the fixed-field order, with coefficient field of
its square order and the specified Frobenius conjugation. -/
def MultiplierRow (S : Type u) [Group S] : MultiplierShape → Prop
  | .two => ClassicalGroup.IsPSL S 4 2 ∨ ClassificationModels.IsG2At S 4 ∨
      Nonempty (S ≃* Sporadic.Mathieu.M12) ∨
      Nonempty (S ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (S ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (S ≃* Rudvalis.Model) ∨
      ∃ q : ℕ, Odd q ∧ q ≠ 9 ∧ ClassicalGroup.IsPSL S 2 q
  | .three => (¬ ClassicalGroup.IsPSL S 3 4) ∧
      ((∃ q : ℕ, q % 3 = 1 ∧ ClassicalGroup.IsPSL S 3 q) ∨
       ∃ p f : ℕ, p.Prime ∧ 0 < f ∧ (p ^ f) % 3 = 2 ∧
         ClassicalGroup.IsPSU S 3 (p ^ f))
  | .six => Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (S ≃* alternatingGroup (Fin 7))
  | .twelve => Nonempty (S ≃* Sporadic.Mathieu.M22)
  | .elementaryFour => Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)
  | .exceptionalFortyEight => ClassicalGroup.IsPSL S 3 4

/-- Both exhaustiveness and every multiplier identification in I.1.3.
In particular the exceptional order-48 multiplier is not declared cyclic. -/
structure MultiplierTable (S : Type u) [Group S] [Group.IsPerfect S] : Prop where
  exhaustive : Nontrivial (schurMultiplier S) ↔ ∃ r, MultiplierRow S r
  values : ∀ r, MultiplierRow S r → Nonempty (schurMultiplier S ≃* r.Carrier)

/-- The complete universal I.1.3 implication, retained as an earlier-source
parameter, not asserted here. Perfectness selects the source's nonabelian
simple domain. Its producer is `qt-i-01`, including `qt-i01-lie-a2`. -/
def EarlierMultiplierInput (K : GroupClass.{u}) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S] [Group.IsPerfect S] [IsSimpleGroup S],
    IsSQTK K S → MultiplierTable S



end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion
