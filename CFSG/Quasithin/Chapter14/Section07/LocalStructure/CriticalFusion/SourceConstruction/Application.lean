module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.Assembly
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.LocalAlternatives

/-!
# Applying the constructed section to the Rudvalis endpoint

The same original G, T, L, V and flag are retained in the constructed Data
and in `source_rudvalis_of_local_alternatives`. The remaining C.2.7
alternative is requested only for this constructed datum, not universally
over unrelated actions or groups.

The component reduction and G₂ exclusion remain source obligations of
qt-d-14763-source-data. The structural, faithful classification, alternating
module, 14.7.10, 14.7.31 and local C.2.7 premises are discharged by the
final owner qt-d-14775-source and its existing producers. Thus this is a
conditional application, not an unconditional 14.7.63 or 14.7.75 theorem.

Source: Aschbacher–Smith, 14.7.63 and 14.7.75, printed pp.1069,1077–1078.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction
open Subgroup Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open SourceEndgame.SourceAssembly.FullSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The constructed Data feeds the existing endpoint on the very same group.
Only its own fixed-component alternatives remain at this final application. -/
theorem exists_data_with_rudvalis_application
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (h52 : AlternatingResidual F ∨ G2Residual F)
    (h53 : ¬ G2Residual F)
    (h40 : AlternatingResidual F → NaturalRecognition F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (baumann : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (weakClosure : Theorem14731.{u}) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (datum : Data T L V F W),
      FixedComponentAlternatives datum → Nonempty (G ≃* Rudvalis.Model) := by
  obtain ⟨W, add, mod, ⟨datum⟩⟩ :=
    exists_data_of_source_branches d h hab hunique hcomponent h52 h53 h40
  exact ⟨W, add, mod, datum, fun alternatives =>
    source_rudvalis_of_local_alternatives datum structural faithful modules baumann weakClosure
      alternatives⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction
