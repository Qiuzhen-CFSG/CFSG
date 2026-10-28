module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.CyclicCore.ModelInput
public import Theory.SpecificGroups.SU3.CyclicCoreSylow

/-!
# Discharging the concrete unitary cyclic-core Sylow input

The hyperbolic matrix construction supplies the full automorphism Sylow,
its literal inner subgroup, and its marked projective involution for every
prime p congruent to one modulo four. This discharges CyclicCoreModelInput;
transport into the source's ambient group belongs to the separate assembly.

Source: Aschbacher–Smith E.1.14(7), printed p.214, citing Aschbacher (1982),
Lemma 4.11, and A.3.21(b), printed p.55.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection

/-- The concrete model premise has no remaining geometric or Sylow inputs. -/
theorem cyclicCoreModelInput {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1) :
    CyclicCoreModelInput p := by
  intro F _ _ J hsimple hcard hc hJ
  let := hsimple
  exact BenderSuzuki.MatrixGroups.HermitianForm.CyclicCoreSylow.exists_cyclicByFour_sylow
    J hp ho hmod hcard hc hJ

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection
