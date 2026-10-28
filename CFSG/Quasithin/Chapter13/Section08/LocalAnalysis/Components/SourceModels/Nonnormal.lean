module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.Original
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOrdinary.Source

/-!
# The genuine earlier catalogue in the nonnormal F.9.18 branch

A.3.8 applies to the literal component K* in H/O₂(H): SQTK comes from
the original point normalizer, and the quotient has trivial two-core.
Normality is reflected through this solvable quotient, so the assumed
relative nonnormality selects the index-two alternative. Transport through
`componentStarEquiv` gives actual model isomorphisms for K/O₂(K) and the
normalizer index inside H.

This earlier catalogue allows even PSL₂, Suzuki, odd-prime PSL₂ and J₁.
It does not yet give F.9.18(5): the module argument must exclude J₁ and
restrict the odd-prime cases to the PSL₂(5) and PSL₂(7) coincidences.
That remaining argument stays with qt-d-138-f918-models-source.

Source: Aschbacher–Smith, A.3.8(3), printed pp.45--46;
F.9.18(5), pp.325--326; original 13.8.16, p.952.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

variable {G : Type*} [Group G] [Finite G]

/-- Normality is preserved and reflected by the actual component quotient. -/
theorem star_normal_iff (H K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent) :
    (Source.starImage H K).Normal ↔ (K.subgroupOf H).Normal := by
  constructor
  · intro hn
    let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
    exact cComponent_normal_of_quotient_normal hK (pCore 2 H) hn
  · intro hn
    exact hn.map _ (QuotientGroup.mk'_surjective (pCore 2 H))

variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hn : ¬ (K.subgroupOf H).Normal)

include d hH hK hn in
/-- A.3.8 on the literal star image, before the F.9.18 small-ratio sieve. -/
theorem source_nonnormal_star_models :
    (normalizer (Source.starImage H K : Set (Source.Hstar H))).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel (Source.starImage H K) := by
  rcases ChapterA.Section03.NonnormalOrdinary.index_and_model_knownSimple
    (CoverModels.original_star_sqtk d hH) (pCore_quotient_pCore_eq_bot 2)
    (Source.starImage H K) (starImage_isCComponent H K hK) with hnormal | hm
  · exact (hn ((star_normal_iff H K hK).mp hnormal)).elim
  · exact hm

include d hH hKH hK hn in
/-- The same nonnormal model list on K/O₂(K), with its source normalizer index. -/
theorem source_nonnormal_quotient_models :
    (normalizer (K.subgroupOf H : Set H)).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel (K ⧸ pCore 2 K) := by
  have hm := source_nonnormal_star_models d hH hK hn
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  refine ⟨?_, hm.2.of_mulEquiv (componentStarEquiv H K hKH hK)⟩
  exact (cComponent_normalizer_index_quotient hK (pCore 2 H)).symm.trans hm.1

end CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
