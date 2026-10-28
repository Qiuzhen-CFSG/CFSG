module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Assembly
public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.CommutatorInput

/-!
# The proved L₃ centralizer bound in the Chapter 14 consumer

The three cases of original 12.4.8 now discharge the centralizer input of
Chapter 14's commutator-plane adapter. The earlier 12.2 and 12.4.1 source
premises retain their existing owner, qt-d-1242-l3-commutator-source.
Source: Aschbacher–Smith 12.4.8–9 and the proof of 12.4.2, pp.815–816.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Section02 SmallFusion
universe u

/-- The literal classification consumer with the full 12.4.8 input discharged. -/
theorem slThreeCommutator1242_of_proved_centralizers
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (conjugate : NoncommutingConjugate1241.{u}) :
    Chapter14.Section03.CaseOneSource.SLThreeCommutator1242.{u} :=
  Chapter14.Section03.CaseOneSource.slThreeCommutator1242_of_sources
    structural marked normalizerAction
    (hyperplaneCentralizers structural marked normalizerAction) conjugate

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
