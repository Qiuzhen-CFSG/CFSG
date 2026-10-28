module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.Assembly
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlock
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockImages

/-!
# Conditional assembly of the fixed-residual calculation

The two actual block products imply Frattini vanishing and C_T(V)=V.
The independent B.4.8 action calculation then gives a common image for
every maximum elementary subgroup outside V; B.2.21 finishes the family.

Both source calculations remain explicit. This theorem does not assert
the unconditional fixed-residual branch until their producers have been
applied. It feeds the unchanged original fusion assembly.

Source: Aschbacher–Smith, 12.4.6, first escaping-normalizer case, p.814.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u

/-- Discharge the fixed-residual family from its independent block and
action calculations, deriving the intermediate self-centralizer equality. -/
theorem fixedResidualCalculation_of_block_and_action
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (block : FixedBlockCalculation.{u}) (action : FixedBlockActionCalculation.{u}) :
    FixedResidualCalculation.{u} := by
  intro G _ _ T L V h D hmodel hne d hescape hline
  have b := block G T L V h D hmodel hne d hescape
  have hself := (fixedBlock_selfCentralizing h structural marked hmodel hne d
    hescape hline b.product b.residual_centralizer).1
  have a := action G T L V h D hmodel hne d hescape hself
  exact fixedBlock_pair_of_plane h structural marked hmodel hne d hescape hself
    a.module_card a.actor_index a.fixed_plane

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
