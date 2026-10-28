module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceLocal
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.OddCoreGeneration
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.Adequate
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ConjugateBound
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SourceBalance
public import CFSG.Quasithin.ChapterI.Section03.RankTwoSource.OrbitProjection
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.Reduction
/-!
# Source inheritance in E.6.20–22

The genuine common-normal theorem gives E.6.13 nonnormality for every original
obstruction. Chapter 1.1 is discharged by SourceLocal. Balance then feeds the
proved signalizer elimination and odd-core generation to give E.6.21.

For E.6.22, the complete original I.3 orbit/projection theorem supplies component
balance. The actual model inspections need only AdequateComponentAlternatives,
and the original conjugate-count argument supplies the orbit bound. Only
E.6.18, E.6.19 balance, and the component sieve remain their source producers.
Source: Aschbacher–Smith, E.6.13, E.6.20–22, printed pp.250,252–254.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes
open Components ComponentBalance Enlargement SignalizerElimination
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}

/-- E.6.13 excludes normalization of every actual obstruction by T. -/
theorem source_obstruction_not_sylow_normalized
    (h : HypothesisE61 K T M V) (h311 : InvariantSubspaces.CommonNormalInput K T) :
    ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G) := by
  intro A hA hn
  exact hA.2.2.1 (InvariantSubspaces.centralizer_le_of_normal_in_sylow h h311
    hA.2.1 hA.1 hA.2.2.2
    ((normal_subgroupOf_iff_le_normalizer (hA.1.trans h.le_sylow)).mpr hn))

/-- Original E.6.19 balance supplies E.6.20 and the full E.6.21 conclusion. -/
theorem source_oddCoreFree_of_balance [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (h311 : InvariantSubspaces.CommonNormalInput K T) (hbal : HyperplaneBalance V) :
    OddCoreFree V := by
  have he := source_earlierLocalFacts h
  have h13 := source_obstruction_not_sylow_normalized h h311
  intro A hAV hne
  exact lemma_E_6_21 h
    (fun _ _ hAM hp => h.localCentralizer_characteristicTwo he hAM hp)
    (fun W hWV hc => lemma_E_6_20 h h15 he h13 hbal ⟨hWV,hc⟩) hne hAV

/-- Supply original I.3 balance and every local inspection in the E.6.22 consumer. -/
theorem source_hyperplane_characteristicTwo [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (h311 : InvariantSubspaces.CommonNormalInput K T)
    (h18 : SevenExcluded M V) (ho : OddCoreFree V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X) :
    ∀ U : Subgroup G, IsHyperplane V U →
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)) := by
  have h13 := source_obstruction_not_sylow_normalized h h311
  exact characteristicTwo_of_component_enlargement h h15 (source_earlierLocalFacts h) h13 h18 ho
    (ComponentInspection.component_lift_of_adequate_models h h15
      (SourceBalance.earlierBalance_of_orbit_projection (ChapterI.RankTwoSource.earlierOrbitProjection K))
      ho h68) (twoConjugates h h15 h13 ho)
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes
