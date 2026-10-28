module

public import Theory.SpecificGroups.SU3.MarkedHyperbolicCoordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.ModelInputs
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The marked hyperbolic model input

This names the concrete model theorem still needed for exceptional fusion.
It strengthens the unmarked cyclic-coordinate witness by retaining the
unitary-plane map and its scalar, rotation, swap and field-action markings.
The map lands in the literal inner-automorphism subgroup of the actual
projective matrix group. The field and inherited simplicity are those of
the source model; no independent simplicity or catalogue theorem is requested.

The conditional ambient transport can use this proposition while its model
producer constructs it. Neither this definition nor its conditional consumers
assert the unconditional model theorem.

Source: Aschbacher--Smith E.1.14(7), p.214, A.3.21(a,b), p.55;
Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open Matrix.UnitaryQuaternionRotation
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection

/-- Full marked Sylow coordinates in each genuine normalized projective model.
This is a proposition awaiting its concrete-model proof, not an axiom. -/
@[expose] def MarkedHyperbolicModelInput (p : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
    IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) →
    Nat.card F = p ^ 2 → (∀ x, J.conj x = x ^ p) →
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
    ∃ (S : Sylow 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
      (w : ProjectiveSpecialUnitaryMatrixGroup J) (J₂ : HermitianForm 2 F),
      orderOf w = 2 ∧ Nonempty (MarkedCyclicByFour
        (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        (S : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (MulAut.conj w) J₂)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection
