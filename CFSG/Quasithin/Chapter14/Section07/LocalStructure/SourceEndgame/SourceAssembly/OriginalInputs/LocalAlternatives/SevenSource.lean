module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.LocalAlternatives.SevenShort
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.SevenSelection

/-!
# Original fixed-component discharge in the Rudvalis branch

The actual fixed components are now proved short. Their natural moved
subgroup has order 64, so the intrinsic module bound contradicts the two
noncentral K-chief factors supplied by the original point commutator.
Thus the fixed-component C.2.7 alternatives require no local hypothesis.
Apply the existing natural-point Baumann and marked-amalgam consumers to
obtain the actual Rudvalis isomorphism and the full D-model conclusion.

The original Data constructor and the earlier structural, faithful and
module theorems remain explicit. These statements close the fixed-component
branch, not the unconditional14.7.75 assembly. The pre-Data14.5.21(2) and
F.9.18 inputs remain with qt-d-14775-source and its final source assembly.
Source: Aschbacher–Smith14.7.68–75, pp.1071–1078.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})

include d structural modules

theorem fixedComponentAlternatives_from_source : FixedComponentAlternatives d :=
  fixedComponentAlternatives_of_shortness d structural modules
    (fun u _ h => d.fixedComponent_short_from_source u h)

include faithful

theorem source_rudvalis_of_original_fixed_components : Nonempty (G ≃* Rudvalis.Model) :=
  source_rudvalis_of_naturalPointMS_local_alternatives d structural faithful modules
    (fixedComponentAlternatives_from_source d structural modules)

theorem source_theoremDModel_of_original_fixed_components : ClassificationModels.IsTheoremDModel G :=
  source_theoremDModel_of_naturalPointMS_local_alternatives d structural faithful modules
    (fixedComponentAlternatives_from_source d structural modules)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
