module

public import Theory.GroupTheory.InvolutionSquareSubgroupFusion
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Elementary centralizers from cyclic core squares

Let a Sylow two-subgroup have an index-two subgroup whose squares lie in a
cyclic subgroup containing the central involution. If this involution is weakly
closed in the index-two subgroup, any conjugate outside it has elementary
centralizer. A nontrivial square in the core centralizer supplies a commuting
square root of the central involution, contradicting weak closure. Multiplying
an outside centralizer element by the outside involution reduces to the core.

This is the elementary-centralizer step in Janko–Thompson, Math. Z. 113 (1970),
§4, Case 1, printed p.392. No bound on elementary subgroup orders is used.
-/

open Subgroup

namespace Sylow

/-- An outside conjugate of the central involution has elementary centralizer
when core squares are cyclic and fusion inside the core fixes that involution. -/
public theorem elementary_centralizer_of_index_two_of_cyclic_squares
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (H : Subgroup S) (hi : H.index = 2)
    (R : Subgroup H) [IsCyclic R] (hsq : ∀ x : H, x ^ 2 ∈ R)
    (z : H) (hzR : z ∈ R) (hz : orderOf z = 2) (hzc : (z : S) ∈ center S)
    (hweak : ∀ u : S, u ∈ H → IsConj ((z : S) : G) (u : G) → u = z)
    (t : S) (ht : t ^ 2 = 1) (hout : t ∉ H)
    (hconj : IsConj ((z : S) : G) (t : G)) :
    IsElementaryAbelian 2 (centralizer ({t} : Set S)) := by
  have hcore (u : H) (hu : Commute (u : S) t) : u ^ 2 = 1 := by
    by_contra hn
    have hd : 2 ∣ orderOf (u ^ 2) := (S.isPGroup'.to_subgroup H).dvd_orderOf hn
    let n := orderOf (u ^ 2) / 2
    have ho : orderOf ((u ^ 2) ^ n) = 2 :=
      orderOf_pow_orderOf_div (orderOf_pos (u ^ 2)).ne' hd
    have he : (u ^ 2) ^ n = z := congrArg Subtype.val
      (IsCyclic.eq_of_orderOf_eq_two
        (x := (⟨(u ^ 2) ^ n, R.pow_mem (hsq u) n⟩ : R))
        (y := ⟨z, hzR⟩) (by rwa [← orderOf_coe]) (by rwa [← orderOf_coe]))
    have hroot : ((u : S) ^ n) ^ 2 = z := by
      have he' := congrArg Subtype.val he
      simpa only [Subgroup.coe_pow, ← pow_mul, Nat.mul_comm] using he'
    have heq := S.eq_of_isConj_of_squares_mem_of_inside_fusion H
      (sq_mem_of_index_two hi) z hzc hweak t ((u : S) ^ n) hroot
      (hu.pow_left n) hconj
    exact hout (heq ▸ z.property)
  have hpow (x : centralizer ({t} : Set S)) : x ^ 2 = 1 := by
    have hxt : Commute (x : S) t := mem_centralizer_singleton_iff.mp x.property
    apply Subtype.ext
    by_cases hx : (x : S) ∈ H
    · exact congrArg H.subtype (hcore ⟨x, hx⟩ hxt)
    · have htx : t * (x : S) ∈ H :=
        (mul_mem_iff_of_index_two hi).mpr (iff_of_false hout hx)
      have hh := congrArg H.subtype (hcore ⟨t * (x : S), htx⟩
        ((Commute.refl t).mul_left hxt))
      change (t * (x : S)) ^ 2 = 1 at hh
      rwa [hxt.symm.mul_pow, ht, one_mul] at hh
  exact {
    toIsMulCommutative := ⟨⟨fun a b =>
      (Commute.of_orderOf_dvd_two (fun c => orderOf_dvd_of_pow_eq_one (hpow c)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }
end Sylow
