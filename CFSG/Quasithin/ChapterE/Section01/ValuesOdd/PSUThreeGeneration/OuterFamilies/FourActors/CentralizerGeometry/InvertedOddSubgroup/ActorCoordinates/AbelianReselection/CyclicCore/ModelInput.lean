module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.ModelInputs
public import Theory.GroupTheory.CyclicByFourOuterInvolutions
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The concrete unitary Sylow input for cyclic-core assembly

The concrete-model producer must exhibit an actual Sylow subgroup of the
full automorphism group of the actual projective matrix group. Its rotation
and reflections must satisfy the published generator coordinates relative
to the literal inner-automorphism subgroup. The marked involution belongs
to the projective matrix group itself.

This proposition names an outstanding mathematical input, not a theorem.
The ambient transport can be proved independently with this input explicit;
the cyclic-core assembly must discharge it before claiming the source result.

Source: Aschbacher--Smith E.1.14(7), printed p.214, A.3.21(b), p.55;
Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection

/-- A genuine unitary Sylow realization, including its marked inner subgroup.
No simplicity proof is requested: simplicity is inherited from the source. -/
@[expose] def CyclicCoreModelInput (p : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
    IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) →
    Nat.card F = p ^ 2 → (∀ x, J.conj x = x ^ p) →
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
    ∃ (S : Sylow 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
      (w : ProjectiveSpecialUnitaryMatrixGroup J),
      orderOf w = 2 ∧ Nonempty (CyclicByFourCoordinates
        (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        (S : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (MulAut.conj w))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection
