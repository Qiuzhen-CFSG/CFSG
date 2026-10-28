module

public import Theory.GroupTheory.WeaklyClosedSquareFusion
public import Theory.GroupTheory.PGroup.UniqueNormalFourRoots

/-!
# Weak closure of a central involution in a unique normal four

In a finite group of elementary two-rank at most two, let a Sylow
two-subgroup have a unique normal four. A central involution weakly closed
in that four is weakly closed in the whole Sylow subgroup.

Every involution square in the Sylow lies in the normal four: squares
centralize the four, and the elementary rank bound forces membership.
An involution outside the four centralizes a square root of the central
involution, by `UniqueNormalFourRoots`. Transporting this root through an
ambient conjugation into the original Sylow makes its square a conjugate
in the four, where weak closure applies.

This gives a shortcut to the outside-centralizer step of Janko–Thompson,
Math. Z. 113 (1970), §4, Case 2, p.393, under the stronger bound on all
elementary subgroup orders used here. It needs no core-index bound.
-/

open Subgroup

namespace Sylow

/-- Weak closure of a central involution in the unique normal four extends
to the entire Sylow subgroup under the elementary rank bound. -/
public theorem eq_of_isConj_of_weakly_closed_in_unique_normal_four
    {G : Type*} [Group G] [Finite G]
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hweak : ∀ t : S, t ∈ E → IsConj (z : G) (t : G) → t = z)
    (t : S) (hconj : IsConj (z : G) (t : G)) : t = z := by
  by_cases htE : t ∈ E
  · exact hweak t htE hconj
  have hlocal := elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have ht : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    calc
      orderOf t = orderOf (t : G) := (orderOf_coe t).symm
      _ = orderOf ((MulAut.conj g) (z : G)) := congrArg orderOf hg.symm
      _ = orderOf (z : G) := (MulAut.conj g).orderOf_eq _
      _ = 2 := (orderOf_coe z).trans hz
  obtain ⟨x, hx, hxt⟩ := S.isPGroup'.exists_commuting_square_root_of_unique_normal_four
    hlocal E hE hunique z t hzC hz ht htE
  apply S.eq_of_isConj_of_commuting_square_root_of_weakly_closed_squares
    z t x hzC hz2 ?_ hconj hx hxt
  intro v hv
  apply hweak (v ^ 2) ?_ hv
  have hv2 : (v ^ 2) ^ 2 = 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hv
    apply Subtype.ext
    change ((v ^ 2 : S) : G) ^ 2 = 1
    rw [← hg]
    change ((MulAut.conj g) (z : G)) ^ 2 = 1
    rw [← map_pow, ← Subgroup.coe_pow, hz2]
    exact (MulAut.conj g).map_one
  apply mem_four_of_square_eq_one_of_elementary_card_lt_eight hlocal E hE hv2
  have hb := centralizer_index_le_two_of_normal_four S.isPGroup' E hE
  have hn := (centralizer (E : Set S)).index_ne_zero_of_finite
  have hi : (centralizer (E : Set S)).index = 1 ∨
      (centralizer (E : Set S)).index = 2 := by omega
  rcases hi with hi | hi
  · rw [index_eq_one.mp hi]
    trivial
  · exact sq_mem_of_index_two hi v

end Sylow
