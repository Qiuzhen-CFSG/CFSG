module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen.Reduction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen.LocalGeometry
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen.FrobeniusModule

/-!
# The small PSL₂(17) branch of K.2

For the original source action with explicit binary degree at most eight,
the order-seventeen lower bound makes the degree exactly eight. The compatible
cover and diagonal-actor calculations construct a literal 17:8 pair in G,
together with involution fusion and the four-group centralizer products.
The Frobenius relation gives fixed dimensions one, two and four for the
complement and its powers. A small elementary actor would then share an
involution's four-dimensional fixed space, whereas its centralizer product
has only two fixed dimensions. Thus the cubic ratio is strictly greater than two.

All local geometry and fixed-space premises are discharged here. The degree
upper bound remains explicit: the six-parameter assembly derives it under
the contrary ratio bound using the independent prime-degree calculation.

Source: Aschbacher--Smith K.2, printed p.453; Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 4.1, manuscript p.9.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- The degree-eight PSL₂(17) branch of K.2, retaining the actual source
central quotient and explicit degree bound, with all local calculations proved. -/
theorem two_lt_cubicRatio_of_degree_le_eight
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (hd : Module.finrank (ZMod 2) V ≤ 8) :
    2 < cubicRatio ρ := by
  obtain ⟨x, r, hx, hr, hrel, hfusion, hproducts⟩ := source_local_geometry ρ h hm hd
  exact source_exclusion_of_frobenius_pair ρ h hm hd x r hx hr hrel hfusion hproducts

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
