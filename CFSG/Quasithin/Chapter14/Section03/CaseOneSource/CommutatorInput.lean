module

public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.FixedSpace
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Assembly

/-!
# The original L₃ commutator input to the D-source consumer

The Chapter12 assembly uses the actual chosen module and the original
L/O₂(L) marking. This adapter supplies its literal conjugation map and
commutator to the unchanged Chapter14 consumer. All earlier implications
remain explicit; the final source theorem must discharge them.

Source: Aschbacher–Smith, the final proof of 12.4.2, printed p.816.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04.SmallFusion
open Chapter12.Section04.SLThreeCommutatorSource
universe u

/-- Feed the checked symmetric-plane construction to its exact consumer.
This is a conditional assembly, independent of SLThreeFusion1247. -/
theorem slThreeCommutator1242_of_sources
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (centralizers : HyperplaneCentralizers1248.{u})
    (conjugate : NoncommutingConjugate1241.{u}) : SLThreeCommutator1242.{u} := by
  intro X _ _ T L V h D hmodel hne
  exact source_commutator_plane structural marked normalizerAction centralizers conjugate
    T L V h D hmodel hne

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
