module

public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.CommutatorInput
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.NormalizerAction.SourceAssembly

/-!
# The original L₃ commutator input after full-normalizer recognition

The original chosen module's full normalizer has the same action as L.
Supply this proved input to the unchanged Chapter14 commutator interface.
The structural and marked-module implications of 12.2.2, hyperplane centralizers,
and noncommuting-conjugate existence remain with the source assembly owner.

Source: Aschbacher–Smith, the final proof of 12.4.2, printed p.816.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04.SmallFusion
open Chapter12.Section04.SLThreeCommutatorSource
universe u

/-- Supply the full-normalizer action without an additional callback or
any fusion premise, retaining the independent earlier source inputs. -/
theorem slThreeCommutator1242_of_normalizer_source
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (centralizers : HyperplaneCentralizers1248.{u})
    (conjugate : NoncommutingConjugate1241.{u}) : SLThreeCommutator1242.{u} := by
  intro X _ _ T L V h D hmodel hne
  exact source_commutator_plane_of_remaining_sources structural marked centralizers conjugate
    T L V h D hmodel hne

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
