module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SourceEarlier
public import CFSG.Quasithin.ChapterI.Section03.RankTwoSource.EarlierSources
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SourceBlockSelection
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.SourceInspection
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.HyperplaneFields
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.CommutationSource
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.BinaryCoverAnalysis
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.TwoCentralSubspace
/-!
# Original E.6.23 with its earlier source inputs discharged

After E.6.22, the adequate component sieve supplies the unchanged full model
interface: its two corank-one rows are impossible in a characteristic-two
hyperplane centralizer. The original E.6.7 family supplies block selection;
complete Chapter 1 containment/orbit models, C.1.9 and A.3.8 supply corank-two
lifting. The proved block and ordinary-component inspections leave only the
actual further A₆ enlargement. Complete A.3.6/A.3.8 and I.3 construct its normal
component, while the binary cover and two-central actor calculations are proved.

Only recognition of that original further component remains with its model
owner. The final theorem gives E.6.23 from E.6.8, E.6.18, the genuine common-normal
input and that precise recognition statement; it assumes no block persistence,
conjugate containment, normal lift, fixed-space equality or global odd-core result.
Source: Aschbacher–Smith, E.6.22–23, printed pp.254–255.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
open Components ComponentBalance BlockInspection
open InvariantSubspaces.BlockSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

theorem source_full_componentAlternatives
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hchar : ∀ U : Subgroup G, IsHyperplane V U →
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)))
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X) :
    OddObstruction.EarlierComponentAlternatives M V (sylowCentralizer (T : Subgroup G) V) := by
  intro A hA X hX
  exact ⟨component_not_le h (source_earlierLocalFacts h) hA hX,
    (h68 A hA X hX).full_of_hyperplane_characteristicTwo hchar hA.1 hX⟩

theorem source_furtherLift
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) : SixAutomorphisms.FurtherLift M V :=
  SourceBalance.further_lift_of_earlier_sources
    ChapterI.RankTwoSource.earlierA36_knownSimple ChapterI.RankTwoSource.earlierA38_knownSimple
    (ChapterI.RankTwoSource.earlierOrbitProjection KnownSimple.IsKnownSimple) h

theorem source_corankTwoLifting [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (hchar : ∀ U : Subgroup G, IsHyperplane V U →
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)))
    (h8 : OddObstruction.EarlierComponentAlternatives M V (sylowCentralizer (T : Subgroup G) V))
    (h18 : SevenExcluded M V) (ho : OddCoreFree V) : CorankTwoLifting M V := by
  apply Lifting.corankTwoLifting h h15 hchar (source_localContainmentInput h)
    (e67Input_knownSimple h) h8 h18 ho (source_blockCommutationInput G) (source_componentOrbits h)
  intro H _ _ hH hcore S A hA hgen B hB
  exact ChapterA.Section03.SourceComponents.sylow_orbit_of_generated hH hcore S hA hgen hB

theorem source_blockEnlargement_of_six [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (h311 : InvariantSubspaces.CommonNormalInput KnownSimple.IsKnownSimple T)
    (hchar : ∀ U : Subgroup G, IsHyperplane V U →
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)))
    (h8 : OddObstruction.EarlierComponentAlternatives M V (sylowCentralizer (T : Subgroup G) V))
    (h18 : SevenExcluded M V) (ho : OddCoreFree V) (hsix : SixOrbitContainment M V) :
    BlockEnlargement M V := by
  exact blockEnlargement_of_inspections h h15 (source_obstruction_not_sylow_normalized h h311)
    ho hsix (source_blockCommutationInput G) (source_corankTwoLifting h h15 hchar h8 h18 ho)
    (BlockCase.properBlockExclusion_of_e67 h (e67Input_knownSimple h) (source_blockCommutationInput G) ho)
    (ComponentCase.properComponentInspection h h15 hchar (fun A hA X hX => (h8 A hA X hX).2)
      h18 ho (source_blockCommutationInput G))

theorem source_sixOrbitContainment_of_quotientRecognition [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (h311 : InvariantSubspaces.CommonNormalInput KnownSimple.IsKnownSimple T)
    (h8 : OddObstruction.EarlierComponentAlternatives M V (sylowCentralizer (T : Subgroup G) V))
    (h18 : SevenExcluded M V) (ho : OddCoreFree V)
    (hquot : SixAutomorphisms.ModelIdentification.QuotientRecognition T M V) :
    SixOrbitContainment M V := by
  have hmodel : SixAutomorphisms.ModelIdentification M V :=
    SixAutomorphisms.ModelIdentification.modelIdentification_of_quotient_and_cover
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) h h15 ⟨h8,h18,ho⟩ hquot
      SixAutomorphisms.ModelIdentification.binaryCoverAnalysis
  exact SixAutomorphisms.sixOrbitContainment_of_enlargement_analysis h h15
    (source_obstruction_not_sylow_normalized h h311) (source_furtherLift h) hmodel
    (SixAutomorphisms.linearActionAnalysis h)

theorem source_rank_gt_one_of_quotientRecognition [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V)
    (h311 : InvariantSubspaces.CommonNormalInput KnownSimple.IsKnownSimple T)
    (h18 : SevenExcluded M V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X)
    (hquot : SixAutomorphisms.ModelIdentification.QuotientRecognition T M V) :
    1 < globalR V := by
  have ho := source_oddCoreFree h (Or.inr hm) h311 h18 h68
  have hchar := source_hyperplane_characteristicTwo_of_model_sources h (Or.inr hm) h311 h18 h68
  have h8 := source_full_componentAlternatives h hchar h68
  have hsix := source_sixOrbitContainment_of_quotientRecognition h (Or.inr hm) h311 h8 h18 ho hquot
  exact rank_gt_one_of_block_enlargement h (source_obstruction_not_sylow_normalized h h311)
    (source_earlierBlockSelection h) hchar
    (source_blockEnlargement_of_six h (Or.inr hm) h311 hchar h8 h18 ho hsix)
    (twoConjugates h (Or.inr hm) (source_obstruction_not_sylow_normalized h h311) ho) hm
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
