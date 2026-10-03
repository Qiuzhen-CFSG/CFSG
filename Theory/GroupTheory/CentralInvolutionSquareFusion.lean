module

public import Theory.GroupTheory.WeaklyClosedSquareFusion
public import Theory.GroupTheory.SylowCentralizerNonfusion

/-!
# Fusion obstruction from central involution squares

Suppose the normalizer of a Sylow two-subgroup fixes a central involution z,
and every square that is an involution is central in the Sylow subgroup.
Burnside fusion then makes z weakly closed among squares. Consequently any
conjugate of z that commutes with a square root of z equals z, by transporting
that root through an involution centralizer.

This isolates the fusion argument in MacWilliams, *On 2-groups with no normal
abelian subgroups of rank 3, and their occurrence as Sylow 2-subgroups of
finite simple groups*, Trans. AMS 150 (1970), §3(iv), pp.367–369,
DOI 10.1090/S0002-9947-1970-0276324-3. The structural construction of the
involution and its commuting roots is a separate hypothesis.
-/

open Subgroup

namespace Sylow

/-- Centrality of involution squares and a fixed normalizer action turn a
commuting square root into a nonfusion certificate. -/
public theorem eq_of_isConj_of_central_involution_squares
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (z : S) (hz : z ^ 2 = 1) (hzc : z ∈ center S)
    (hN : normalizer (S : Set G) ≤ centralizer ({(z : G)} : Set G))
    (hsquares : ∀ v : S, v ^ 4 = 1 → v ^ 2 ∈ center S)
    (t x : S) (hx : x ^ 2 = z) (hxt : Commute x t)
    (hconj : IsConj (z : G) (t : G)) : t = z := by
  have hcentral (u : S) (hu : u ∈ center S) :
      (u : G) ∈ centralizer (S : Set G) := by
    intro s hs
    exact congrArg Subtype.val (mem_center_iff.mp hu (⟨s, hs⟩ : S))
  have hweak (v : S) (hv : IsConj (z : G) ((v ^ 2 : S) : G)) : v ^ 2 = z := by
    have hv4 : v ^ 4 = 1 := by
      have hh := hv.pow 2
      have hzG : (z : G) ^ 2 = 1 := congrArg Subtype.val hz
      rw [hzG, isConj_one_right] at hh
      have hvsq : (v ^ 2) ^ 2 = 1 := Subtype.ext hh
      simpa only [← pow_mul] using hvsq
    exact Subtype.ext (S.eq_of_isConj_of_normalizer_le_centralizer
      z (v ^ 2) (hcentral z hzc) (hcentral (v ^ 2) (hsquares v hv4)) hN hv)
  exact S.eq_of_isConj_of_commuting_square_root_of_weakly_closed_squares
    z t x hzc hz hweak hconj hx hxt

end Sylow
