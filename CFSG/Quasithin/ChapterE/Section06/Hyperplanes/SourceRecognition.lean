module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SourceEnlargement
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Complete
/-!
# The original E.6.23 further enlargement with quotient recognition proved

The complete source model inspection supplies the last model premise to the
original enlargement construction. The theorem retains precisely the earlier
E.6.8, E.6.18 and common-normal source inputs; it assumes no model exclusion,
normal lift, block persistence or quotient-action identification.

Source: Aschbacher–Smith E.6.23, printed pp.254–255.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
open Components ComponentBalance
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

theorem source_modelIdentification [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (earlier : SixAutomorphisms.ModelIdentification.EarlierResults T M V) :
    SixAutomorphisms.ModelIdentification M V :=
  SixAutomorphisms.ModelIdentification.modelIdentification_of_quotient_and_cover
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) h h15 earlier
    (SixAutomorphisms.ModelIdentification.quotientRecognition T M V)
    SixAutomorphisms.ModelIdentification.binaryCoverAnalysis

theorem source_sixOrbitContainment [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (h311 : InvariantSubspaces.CommonNormalInput KnownSimple.IsKnownSimple T)
    (h8 : OddObstruction.EarlierComponentAlternatives M V (sylowCentralizer (T : Subgroup G) V))
    (h18 : SevenExcluded M V) (ho : OddCoreFree V) : SixOrbitContainment M V :=
  source_sixOrbitContainment_of_quotientRecognition h h15 h311 h8 h18 ho
    (SixAutomorphisms.ModelIdentification.quotientRecognition T M V)

theorem source_rank_gt_one [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V)
    (h311 : InvariantSubspaces.CommonNormalInput KnownSimple.IsKnownSimple T)
    (h18 : SevenExcluded M V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X) :
    1 < globalR V :=
  source_rank_gt_one_of_quotientRecognition h hm h311 h18 h68
    (SixAutomorphisms.ModelIdentification.quotientRecognition T M V)
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
