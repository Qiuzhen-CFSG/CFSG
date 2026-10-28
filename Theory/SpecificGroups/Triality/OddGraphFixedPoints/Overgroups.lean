module

public import Theory.SpecificGroups.Triality.OddGraphFixedPoints
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage

/-!
# Selecting a concrete graph representative in a triality automorphism overgroup

Apply the proved inner–coefficient coverage to the given automorphism, then
cancel its inner part inside the original overgroup. Cauchy's theorem in the
coefficient cyclic subgroup supplies an outer element of order three fixing the
explicit elementary nine. No conjugacy classification of arbitrary graph fixed
groups is required. Simplicity and perfectness are inherited from the source
component, as in the coverage theorem.

This is the representative needed by Aschbacher–Smith A.2.6, printed pp.33–34,
with the graph convention of GLS98 Definition 2.5.13(c)(2)
(`refs/quasithin.pdf`, `refs/KGroup/GLS3/chapter2.tex`).
-/

public section

noncomputable section
namespace Triality.Standard.OddGraph
open OuterOdd

/-- An automorphism overgroup with an outer three-divisor contains a genuine
order-three coefficient graph representative and its fixed elementary nine. -/
theorem exists_graph_representative_in_overgroup
    (n : ℕ) (hn : 0 < n)
    [IsSimpleGroup (BinaryCarrier n hn)] [Group.IsPerfect (BinaryCarrier n hn)]
    (U : Subgroup (MulAut (BinaryCarrier n hn)))
    (hU : MulAut.innerSubgroup (BinaryCarrier n hn) ≤ U)
    (a : MulAut (BinaryCarrier n hn)) (ha : a ∈ U)
    (hthree : 3 ∣ orderOf
      (QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier n hn)) a)) :
    ∃ d : CoefficientAut (binaryParameters n hn),
      coefficientAction (binaryParameters n hn) d ∈ U ∧
      orderOf (coefficientAction (binaryParameters n hn) d) = 3 ∧
      coefficientAction (binaryParameters n hn) d ∉ MulAut.innerSubgroup (BinaryCarrier n hn) ∧
      ∃ E : Subgroup (BinaryCarrier n hn), IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
        E ≤ (coefficientAction (binaryParameters n hn) d).fixedSubgroup := by
  obtain ⟨g, c, hform⟩ := Coverage.binary_inner_coefficient n hn a
  obtain ⟨d, hdU, hdorder, hdouter, hdfix⟩ :=
    exists_order_three_coefficient_in_overgroup n hn U hU a ha g c hform hthree
  exact ⟨d, hdU, hdorder, hdouter, ElementaryNine.subgroup (binaryParameters n hn) rfl,
    ElementaryNine.subgroup_elementary _ _, ElementaryNine.card_subgroup _ _, hdfix⟩

end Triality.Standard.OddGraph
