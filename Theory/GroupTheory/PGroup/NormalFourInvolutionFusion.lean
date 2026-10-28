module

public import Theory.GroupTheory.PGroup.UniqueNormalFourRoots
public import Mathlib.GroupTheory.Sylow

/-!
# Weak closure from a unique normal four

In a rank-two Sylow two-subgroup with a unique normal four `E`, a central
involution weakly closed in `E` is weakly closed in the whole Sylow subgroup.
An outside conjugate centralizes a square root of the central involution.
Transport that root into the Sylow subgroup inside the involution centralizer.
Its square is an involution and centralizes the normal four, so the rank
bound puts it in `E`. Weak closure now makes the transporting conjugation
fix both involutions, proving that they coincide.

A general transport lemma and an index-two version are also provided.
This replaces the elementary-centralizer endpoint in Janko–Thompson,
Math. Z. 113 (1970), §4, Case 1, p.392, under the stronger rank bound.
The commuting-square-root input is proved in `UniqueNormalFourRoots`.
-/

open Subgroup
open scoped Pointwise

/-- Under the elementary rank bound, a square which is an involution belongs
to every normal four-group. -/
public theorem Subgroup.involution_square_mem_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hrank : ∀ U : Subgroup P, IsElementaryAbelian 2 U → Nat.card U < 8)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (x : P) (hx : orderOf (x ^ 2) = 2) : x ^ 2 ∈ E := by
  apply mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank E hE
  · have hh := pow_orderOf_eq_one (x ^ 2)
    rw [hx] at hh
    exact hh
  · have hb := centralizer_index_le_two_of_normal_four hP E hE
    have hn := (centralizer (E : Set P)).index_ne_zero_of_finite
    have hi : (centralizer (E : Set P)).index = 1 ∨
        (centralizer (E : Set P)).index = 2 := by omega
    rcases hi with hi | hi
    · rw [index_eq_one.mp hi]
      trivial
    · exact sq_mem_of_index_two hi x

namespace Sylow

/-- Weak closure in a subgroup containing involution squares extends across involutions
that centralize a square root of the given central involution. -/
public theorem eq_of_isConj_of_weakly_closed_of_square_mem
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (H : Subgroup S) (z : S)
    (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hsquare : ∀ x : S, orderOf (x ^ 2) = 2 → x ^ 2 ∈ H)
    (hweak : ∀ t : S, t ∈ H → IsConj (z : G) (t : G) → t = z)
    (hroot : ∀ t : S, orderOf t = 2 → t ∉ H →
      ∃ x : S, x ^ 2 = z ∧ Commute x t)
    (t : S) (hconj : IsConj (z : G) (t : G)) : t = z := by
  by_cases htH : t ∈ H
  · exact hweak t htH hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj.symm
  let f : G ≃* G := MulAut.conj g
  have hft : f (t : G) = z := hg
  have ht : orderOf t = 2 := by
    rw [← orderOf_coe t, ← f.orderOf_eq, hft, orderOf_coe z, hz]
  obtain ⟨x, hx, hxt⟩ := hroot t ht htH
  let C : Subgroup G := centralizer ({(z : G)} : Set G)
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hzC ⟨s, hs⟩))
  let y : C := ⟨f (x : G), mem_centralizer_singleton_iff.mpr (by
    have hh := (hxt.map ((f : G →* G).comp (S : Subgroup G).subtype)).eq
    change f (x : G) * f (t : G) = f (t : G) * f (x : G) at hh
    rwa [hft] at hh)⟩
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hx4 : x ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hx, hz2]
  have hy4 : y ^ 4 = 1 := by
    apply Subtype.ext
    change f (x : G) ^ 4 = 1
    simp only [← map_pow, ← Subgroup.coe_pow, hx4, Subgroup.coe_one, map_one]
  have hp : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hy4)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq C T (S.subtype hSC)
  have hyS : (MulAut.conj k) y ∈ S.subtype hSC := by
    rw [← hk]
    change (MulAut.conj k) • y ∈ (MulAut.conj k) • (T : Set C)
    exact Set.smul_mem_smul_set (hT (mem_zpowers y))
  let v : S := ⟨((MulAut.conj k) y : C), hyS⟩
  let u : G ≃* G := f.trans (MulAut.conj (k : G))
  have hfix : (MulAut.conj (k : G)) (z : G) = z :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp k.property)
  have hut : u (t : G) = z := by
    change (MulAut.conj (k : G)) (f (t : G)) = z
    rw [hft, hfix]
  have huz : u (z : G) = ((v ^ 2 : S) : G) := by
    rw [← hx, Subgroup.coe_pow, map_pow]
    rfl
  have hvconj : IsConj (z : G) ((v ^ 2 : S) : G) := by
    apply isConj_iff.mpr
    refine ⟨(k : G) * g, ?_⟩
    rw [← huz]
    simp [u, f, mul_assoc]
  have hvorder : orderOf (v ^ 2) = 2 := by
    rw [← orderOf_coe, ← huz, u.orderOf_eq, orderOf_coe, hz]
  have hvz : v ^ 2 = z := hweak (v ^ 2) (hsquare v hvorder) hvconj
  exact Subtype.ext (u.injective (hut.trans (huz.trans (congrArg Subtype.val hvz)).symm))

/-- A central involution weakly closed in an index-at-most-two subgroup
containing the unique normal four is weakly closed in the Sylow subgroup. -/
public theorem eq_of_isConj_of_weakly_closed_of_index_le_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrank : ∀ U : Subgroup S, IsElementaryAbelian 2 U → Nat.card U < 8)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (H : Subgroup S) (hEH : E ≤ H) (hi : H.index ≤ 2)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hweak : ∀ t : S, t ∈ H → IsConj (z : G) (t : G) → t = z)
    (t : S) (hconj : IsConj (z : G) (t : G)) : t = z := by
  apply S.eq_of_isConj_of_weakly_closed_of_square_mem H z hzC hz ?_ hweak ?_ t hconj
  · intro x _
    have hn := H.index_ne_zero_of_finite
    have hcases : H.index = 1 ∨ H.index = 2 := by omega
    rcases hcases with h | h
    · rw [index_eq_one.mp h]
      trivial
    · exact sq_mem_of_index_two h x
  · intro t ht htH
    exact S.isPGroup'.exists_commuting_square_root_of_unique_normal_four hrank E hE
      hunique z t hzC hz ht (fun htE => htH (hEH htE))

/-- A central involution weakly closed in the unique normal four is weakly
closed in the whole Sylow subgroup, under the elementary rank bound on that
Sylow subgroup. The suffix distinguishes this local-rank interface from
the ambient-rank theorem in `NormalFourWeaklyClosedInvolution`. -/
public theorem eq_of_isConj_of_weakly_closed_in_unique_normal_four_of_sylow_rank
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrank : ∀ U : Subgroup S, IsElementaryAbelian 2 U → Nat.card U < 8)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hweak : ∀ t : S, t ∈ E → IsConj (z : G) (t : G) → t = z)
    (t : S) (hconj : IsConj (z : G) (t : G)) : t = z := by
  apply S.eq_of_isConj_of_weakly_closed_of_square_mem E z hzC hz
    (involution_square_mem_normal_four S.isPGroup' hrank E hE) hweak ?_ t hconj
  intro t ht htE
  exact S.isPGroup'.exists_commuting_square_root_of_unique_normal_four
    hrank E hE hunique z t hzC hz ht htE

end Sylow
