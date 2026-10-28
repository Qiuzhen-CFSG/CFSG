module

public import CFSG.Quasithin.ChapterA.Section02.OddAutomorphisms
public import Theory.SpecificGroups.Triality.OddGraphFixedPoints

/-!
# Applying the concrete triality fixed subgroup in A.2.6

The genuine model construction supplies a pointwise fixed elementary subgroup
of order nine for the chosen coefficient graph action. Its compatible image in
the original normal subgroup is centralized by the given ambient element.
Outerness proves that this element lies outside the normal subgroup, so the
existing fixed-join theorem gives the three-rank contradiction.

These theorems discharge the concrete fixed-subgroup and outside-element
premises of the final paragraph of Aschbacher–Smith A.2.6, printed p.34,
`refs/quasithin.pdf`. The finite automorphism reduction still owns selection of
the ambient representative and the earlier source quotient steps.
-/

public section

namespace CFSG.Quasithin.ChapterA.Section02
open Triality.Standard Triality.Standard.OuterOdd

variable {G : Type*} [Group G] [Finite G]

/-- The actual coefficient fixed subgroup discharges the fixed-nine premise of A.2.6. -/
theorem triality_coefficient_fixed_join_contradicts_three_rank
    (hrank : primeRank 3 G ≤ 2) (L : Subgroup G) [L.Normal]
    (n : ℕ) (hn : 0 < n) (c : CoefficientAut (binaryParameters n hn)) (hc : c ≠ 1)
    (e : BinaryCarrier n hn ≃* L) (x : G) (hx : orderOf x = 3)
    (he : ∀ z, e (coefficientAction (binaryParameters n hn) c z) =
      MulAut.conjNormal x (e z)) : False := by
  obtain ⟨E, hE, hcard, hEL, hfix⟩ :=
    OddGraph.exists_fixed_nine_in_ambient L (binaryParameters n hn) rfl c e x he
  let := hE
  exact fixed_join_contradicts_three_rank hrank L E hEL hcard x hx
    (OddGraph.not_mem_of_compatible_coefficient L n hn c hc e x he) hfix

/-- The constructed cubic graph representative gives the source rank contradiction. -/
theorem triality_graph_fixed_join_contradicts_three_rank
    (hrank : primeRank 3 G ≤ 2) (L : Subgroup G) [L.Normal]
    (n : ℕ) (hn : 0 < n) (e : BinaryCarrier n hn ≃* L) (x : G)
    (hx : orderOf x = 3)
    (he : ∀ z, e (OddGraph.automorphism (binaryParameters n hn) z) =
      MulAut.conjNormal x (e z)) : False := by
  obtain ⟨E, hE, hcard, hEL, hfix⟩ :=
    OddGraph.exists_fixed_nine_in_ambient L (binaryParameters n hn) rfl
      (fieldFrobenius (binaryParameters n hn)) e x he
  let := hE
  exact fixed_join_contradicts_three_rank hrank L E hEL hcard x hx
    (OddGraph.not_mem_of_compatible_graph L n hn e x he) hfix

end CFSG.Quasithin.ChapterA.Section02
