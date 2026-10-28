module

public import Theory.Mathieu.M11.Properties.Sylow3
public import Theory.GroupTheory.PrimeRankElementary

/-!
# The three-rank lower bound for M11

The checked nine-element Sylow model embeds its two elementary coordinates
in the original permutation group. This gives the lower rank used for
component normality in Aschbacher--Smith 2.5.3(4), printed p.553.
-/

namespace Sporadic.Mathieu

/-- The actual Mathieu model has three-rank at least two. -/
public theorem m11_primeRank_three_ge_two : 2 ≤ primeRank 3 M11 := by
  let f := (m11Sylow3 : Subgroup M11).subtype.comp m11Sylow3_mulEquiv_e9.symm.toMonoidHom
  apply primeRank_ge_of_elementary_embedding (p := 3) (e := 2) (f := f)
  · decide +kernel
  · norm_num [Nat.card_eq_fintype_card]
  · exact Subtype.val_injective.comp m11Sylow3_mulEquiv_e9.symm.injective

end Sporadic.Mathieu
