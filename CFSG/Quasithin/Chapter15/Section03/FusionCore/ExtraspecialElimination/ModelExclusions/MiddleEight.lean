module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.NaturalDual
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointTransport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.SectionTransport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Inputs
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.PointCore

/-!
# Excluding the exceptional S₈ middle node

The perfect conjugate span places Vα* in L* and gives the genuine
offender-generated component action for B.5.1. After coordinates have been
selected, the proof transports best offending and point-core containment to
the same concrete PSL₄(2) natural-plus-dual action. The ranks four and at most
three are then incompatible.

`exclude_source_of_classification` selects coordinates from the full B.5.1
conclusion and uses the proved point-core bound. `exclude_source` applies
the full B.5.1 implication after constructing its hypotheses for L*, not
for all of H* = S₈. The genuine earlier local clauses, full B.5.1
classification and exact B.4.9(2iii) rank output remain explicit inputs;
neither coordinates nor a geometric exclusion is assumed. Final assembly
of the other models and the earlier source inputs belongs to the parent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49, printed p.1145, B.5.1, pp.99–103, and B.4.9(2iii), p.92.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open ComponentReduction.ModelReduction
open Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {H M Y V Y₀ L ZS Z A Vγ : Subgroup G} {T : Sylow 2 G}
  [IsElementaryAbelian 2 (localSpan ZS H)]

/-- Conditional assembly on the literal source section. In particular the
offender's component containment is proved from (i) and the reduced group. -/
theorem exclude_source_of_coordinates
    (d : BorelInner.SourceSetup κ H M Y V Y₀ L ZS Z A T)
    (r : ReducedLocalData H M L Y₀ T) (p : PointData d Vγ)
    (e : starImage H L ≃* PSL 4)
    (c : NaturalDualCoordinates d.action.representation (starImage H L) e p.space)
    (hB49 : NaturalDualBestRank) (hgeometry : NaturalDualPointCoreBound) : False :=
  exclude_of_coordinates d.action.representation (starImage H L)
    (starImage H Y₀ ⊔ starImage H (T : Subgroup G)) (starImage H A)
    e p.space c p.point p.stabilizer (star_offender_le_component d r)
    d.actor_core d.best hB49 hgeometry

/-- The full B.5.1 output on the actual component selects coordinates;
the independent intrinsic point-core calculation then contradicts
B.4.9(2iii). No selected module alternative or geometric bound is an input. -/
theorem exclude_source_of_classification
    (d : BorelInner.SourceSetup κ H M Y V Y₀ L ZS Z A T)
    (r : ReducedLocalData H M L Y₀ T)
    (m : BinaryGeometry.MiddleNodeEight (starImage H L) (componentParabolic H L Y₀ T))
    (p : PointData d Vγ)
    (hB51 : QuasisimpleSourceConclusion
      (d.action.representation.comp (starImage H L).subtype) ⊤)
    (hB49 : NaturalDualBestRank) : False := by
  obtain ⟨e, ⟨c⟩⟩ := Selection.coordinates_of_sourceConclusion d r m p hB51
  exact exclude_source_of_coordinates d r p e c hB49 naturalDualPointCoreBound

/-- The middle-node S₈ case is impossible from the genuine earlier source
clauses and the full enumerated classification inputs. The application of
B.5.1 constructs all its hypotheses on the offender-generated component. -/
theorem exclude_source
    (d : BorelInner.SourceSetup κ H M Y V Y₀ L ZS Z A T)
    (r : ReducedLocalData H M L Y₀ T)
    (m : BinaryGeometry.MiddleNodeEight (starImage H L) (componentParabolic H L Y₀ T))
    (p : PointData d Vγ)
    (hB51 : QuasisimpleClassificationInput.{u,u} κ)
    (hB49 : NaturalDualBestRank) : False := by
  obtain ⟨c⟩ := component_sourceConclusion d r m hB51
  exact exclude_source_of_classification d r m p c hB49

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight
