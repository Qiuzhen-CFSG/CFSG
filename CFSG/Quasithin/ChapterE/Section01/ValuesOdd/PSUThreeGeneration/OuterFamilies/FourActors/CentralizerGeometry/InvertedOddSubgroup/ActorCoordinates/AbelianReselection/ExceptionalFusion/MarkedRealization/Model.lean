module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.ExceptionalFusion.MarkedRealization.ModelInput
public import Theory.SpecificGroups.SU3.MarkedHyperbolicModel

/-!
# Discharging the marked hyperbolic model premise

The actual determinant-corrected unitary plane supplies the marked rotation,
swap, scalar involution and full field action in a full automorphism Sylow.
This proves the published model-input proposition with only the prime,
oddness and congruence assumptions. Ambient transport and identification of
the original supplied cyclic core are handled by MarkedRealization.

Source: Aschbacher–Smith E.1.14(7), p.214, citing Aschbacher (1982),
Lemma 4.11, and A.3.21(a,b), p.55.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection

/-- The full marked unitary model has no remaining geometric or Sylow premises. -/
theorem markedHyperbolicModelInput {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1) :
    MarkedHyperbolicModelInput p := by
  intro F _ _ J hsimple hcard hc hJ
  let := hsimple
  exact BenderSuzuki.MatrixGroups.HermitianForm.MarkedHyperbolicModel.exists_markedCyclicByFour_sylow
    J hp ho hmod hcard hc hJ

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection
