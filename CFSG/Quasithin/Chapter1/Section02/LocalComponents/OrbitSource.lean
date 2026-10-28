module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceNormality

/-!
# The original component orbit bound with its source discharged

Pass the literal C-component through the two-core quotient. The proved
noncentral SQTK structure bounds the quotient's conjugacy orbit by two;
normality and normalizer index lift through the same quotient map. No
component model is selected or assumed.

Source: Aschbacher--Smith A.3.8(3) and1.2.1(3).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

theorem component_normal_or_index_two_source
    (hG : IsSQTK KnownSimple.IsKnownSimple G) {B : Subgroup G} (hB : B.IsCComponent) :
    B.Normal ∨ (normalizer (B : Set G)).index = 2 := by
  let := pCore_isNilpotent (p := 2) (G := G)
  apply cComponent_normal_or_index_two_of_quotient hB (pCore 2 G)
  have hq : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 G) pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  exact ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
    (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
    hq (pCore_quotient_pCore_eq_bot 2) (hB.map_quotient _)
end CFSG.Quasithin.Chapter1.Section02
