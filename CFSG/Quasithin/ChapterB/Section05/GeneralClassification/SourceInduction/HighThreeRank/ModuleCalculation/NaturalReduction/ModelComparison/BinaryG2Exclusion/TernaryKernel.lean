module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.KernelObstruction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.PreciseMultiplierInputs
public import Theory.SpecificGroups.SU3.TernaryPerfectKernels

/-!
# The intrinsic ternary-kernel exclusion of the binary G₂ component

The actual unitary root Sylow calculation proves the exact three-free
perfect-kernel premise of the lifted-component consumer. Thus a component
whose actual lifted center has a three-part cannot be the derived binary
octonion group. No universal multiplier table or unitary-cover construction
is needed for this particular B.5.7 application.

Source: Aschbacher–Smith B.5.7, printed p.106, and I.1.3, printed p.407.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
universe u

/-- The local simultaneous-inversion proof supplies the exact model-kernel
premise used in the adequate B.5 induction, in every covering universe. -/
theorem binaryG2_threeFreePerfectKernels :
    ThreeFreePerfectKernels.{u} (commutator (Atlas.G2.Model (ZMod 2))) := by
  intro E _ _ f
  exact Atlas.G2.not_three_dvd_binaryDerived_kernel f

/-- The actual component-cover obstruction, with its three-kernel input now
discharged by the concrete unitary Sylow pair. -/
theorem not_binaryG2_component_of_local_inversion
    {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
    {L : Subgroup G} (hL : IsComponent G L) (d : NoncentralContext K G L) :
    ¬ Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  rintro ⟨e⟩
  let := hL.2
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
    Atlas.G2.isSimple_commutator_binary
  have hz : center (commutator (Atlas.G2.Model (ZMod 2))) = ⊥ := by
    rcases (inferInstance : (center (commutator (Atlas.G2.Model (ZMod 2)))).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  exact not_model_of_threeFreePerfectKernels hL d
    hz binaryG2_threeFreePerfectKernels e

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison

namespace CFSG.Quasithin.ChapterB.SourceInduction.PreciseMultiplierInputs
open HighThreeRank.CoverCentralizer HighThreeRank.CoverCentralizer.SourceConstruction
open HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison ComponentReduction
universe u v

/-- The complete adequate induction with its binary-G₂ kernel premise
discharged. The ten genuine earlier-source inputs, including A.3.6, retain
their original universal statements. Their full KnownSimple instantiation
remains with `qt-b05-general-classification`; no multiplier-table premise
or unitary-cover construction is needed for this consumer. -/
theorem adequateClassification_of_source_local_kernel
    {K : GroupClass.{u}}
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h52 : CoverInput K)
    (hA : SemisimpleInput K)
    (h5 : PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (h36 : Chapter1.Section02.A36Input K)
    (h48two : PreliminaryActions.ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    (h19 : FittingReduction.EarlierB19.{u,v})
    (h131 : FactorExtraction.EarlierA131One.{u})
    (h48three : FactorExtraction.EarlierB48Three.{u,v})
    (h48four : ExceptionalExtension.Nonsplit.EarlierB48Four.{u,v}) :
    AdequateClassificationInput.{u,v} K :=
  adequateClassification_of_source h1 h52 hA h5 h36 binaryG2_threeFreePerfectKernels
    h48two h19 h131 h48three h48four

end CFSG.Quasithin.ChapterB.SourceInduction.PreciseMultiplierInputs
