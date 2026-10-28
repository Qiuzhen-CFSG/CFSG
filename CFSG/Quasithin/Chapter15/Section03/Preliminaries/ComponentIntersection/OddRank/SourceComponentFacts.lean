module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.CoreNormalization
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation

/-!
# The actual earlier component inputs in 15.3.12(1)

Apply the complete source theorems 1.2.1(2)--(3) inside the original outside
overgroup I. They supply both commutation modulo O₂(I) and the full model
alternative for the intrinsic quotient of L∩I. The existing component-
permutation argument consequently makes O₂(Y₊S) normalize the original L.

The original nontrivial intersection residual and the SQTK hypothesis on
I/O₂(I) remain with the 15.3.11--12 source assembly owner. No component
quasisimplicity, model list or orbit assertion is an extra premise.

Source: Aschbacher--Smith 15.3.12(1), pp.1124--1125, using 1.2.1(2)--(3), p.504.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
variable {G : Type*} [Group G] [Finite G]

/-- Discharge the exact earlier Chapter 1 assumptions on the original I and L. -/
theorem localCore_le_normalizer_of_sqtk_quotient
    {Y S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Y S M) (hLI : L ≤ I)
    (hL : (L.subgroupOf I).IsCComponent)
    (hQ : IsSQTK KnownSimple.IsKnownSimple (I ⧸ pCore 2 I))
    (hne : intersectionResidual Y L ≠ ⊥) :
    localCore Y S ≤ normalizer (L : Set G) := by
  apply localCore_le_normalizer_of_component_facts hI hLI hL
  · intro K hK hne
    exact ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two hQ hL hK hne.symm
  · exact Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ hL
  · exact hne

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
