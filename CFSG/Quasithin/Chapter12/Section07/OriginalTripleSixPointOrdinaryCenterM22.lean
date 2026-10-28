module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryCenterRank
public import CFSG.Quasithin.Chapter12.Section07.Preliminaries.M22CenterSource
public import Theory.Mathieu.M22.Properties.TwoRank

/-!
# Excluding the M₂₂ quotient before centrality of the field point

The two-primary center of a perfect M₂₂ cover is cyclic. An elementary
subgroup of order 64 would therefore give an elementary subgroup of order
at least 32 in M₂₂, contrary to its proved two-rank bound.

Source: Aschbacher--Smith, 12.7.5, printed p.840.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section07

/-- The M₂₂ alternative is impossible from the original elementary U of
order 64 alone; no centrality assumption on its marked four-group is used. -/
theorem original_point_ordinary_not_m22
    {B : Type*} [Group B] [Finite B] [IsQuasisimple B]
    (U : Subgroup B) [IsElementaryAbelian 2 U] (hU : Nat.card U = 64)
    (hp : IsPGroup 2 (center B))
    (e : B ⧸ center B ≃* Sporadic.Mathieu.M22) : False := by
  exact original_point_center_not_isCyclic U hU e
    Sporadic.Mathieu.m22_twoRank_le_four
    (Preliminaries.M22CenterSource.center_isCyclic e hp)

end CFSG.Quasithin.Chapter12.Section07
