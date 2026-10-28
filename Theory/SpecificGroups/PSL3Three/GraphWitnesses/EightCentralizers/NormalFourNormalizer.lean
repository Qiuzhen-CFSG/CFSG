module

public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.EightCentralizers.FixedMonomial
public import Theory.SpecificGroups.PSL3Three.MonomialMaximality
public import Theory.SpecificGroups.PSL3Three.Simplicity
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# The full normalizer of the graph-centralizer four

The graph-fixed subgroup is the actual monomial subgroup. Its maximality,
proved by matrix word certificates in `MonomialMaximality`, transfers along
the canonical SL₃(3)-to-PSL₃(3) equivalence. Relative normality of D therefore
puts this maximal subgroup inside the full normalizer of D. A larger
normalizer would make D normal in PSL₃(3); simplicity excludes this, since
D is nontrivial and lies in a proper subgroup.

This proves precisely the `hnorm` input of
`eight_witness_of_graph_centralizer_calculations`, used by `reselect_outer`.
It needs no identification of the fixed group with S₄ and no classification
of all maximal subgroups. The elementary-abelian premise is retained to
match that consumer, although nontriviality alone suffices for the argument.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript p.10: C₁ is the full normalizer of C₁ ∩ A in S.
-/

public section

namespace Matrix.PSL3Three.GraphWitnesses.EightCentralizers

open Subgroup Matrix.PSL3.OuterSolvable

/-- A four-subgroup normal inside the literal graph-fixed subgroup has that
fixed subgroup as its full normalizer in PSL₃(3). -/
theorem normalizer_eq_graph_fixed_of_normal_four
    (D : Subgroup PSL) (_hD : IsElementaryAbelian 2 D) (hc : Nat.card D = 4)
    (hle : D ≤ (graph (ZMod 3)).fixedSubgroup)
    (hn : (D.subgroupOf (graph (ZMod 3)).fixedSubgroup).Normal) :
    normalizer (D : Set PSL) = (graph (ZMod 3)).fixedSubgroup := by
  let : IsSimpleGroup PSL := isSimpleGroup_psl3_three
  have hm : IsCoatom (graph (ZMod 3)).fixedSubgroup := by
    rw [graph_fixed_eq_monomial]
    have he : equiv.toMonoidHom = project := by
      ext x
      exact equiv_apply x
    change IsCoatom (monomialSL.map project)
    rw [← he]
    exact (equiv.mapSubgroup.isCoatom_iff monomialSL).mpr isCoatom_monomialSL
  have hMN := (normal_subgroupOf_iff_le_normalizer hle).mp hn
  rcases hm.le_iff.mp hMN with htop | heq
  · rcases (normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with hbot | htop
    · have h1 : Nat.card D = 1 := Subgroup.card_eq_one.mpr hbot
      omega
    · exact (hm.ne_top (top_unique (htop ▸ hle))).elim
  · exact heq

end Matrix.PSL3Three.GraphWitnesses.EightCentralizers
