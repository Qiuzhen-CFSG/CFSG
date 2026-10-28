module

public import Theory.GroupTheory.InvolutionSquareFusion
public import Theory.GroupTheory.PGroup.ExtraspecialInvolution

/-!
# Squares and fusion through an index-two extraspecial subgroup

Suppose a central Sylow involution has no distinct conjugate inside a subgroup
containing all Sylow squares. Then no distinct conjugate can centralize a square
root of that involution. Transport the root into the original Sylow inside the
centralizer of the central involution; its square lies in the specified subgroup,
where the fusion hypothesis identifies it.

For an index-two extraspecial subgroup, an outside involution splits its own
centralizer over the core centralizer. Every square in that centralizer is thus
a core square. The preceding transport argument makes the entire centralizer
elementary abelian. This isolates the sentence “Clearly C_T(z₁) is elementary”
in Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389.
-/

open Subgroup
open scoped Pointwise

namespace Sylow

/-- Fusion inside a subgroup containing all squares obstructs a commuting
square root at every distinct conjugate of the central involution. -/
public theorem eq_of_isConj_of_squares_mem_of_inside_fusion
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (H : Subgroup S) (hsquares : ∀ x : S, x ^ 2 ∈ H)
    (z : S) (hz : z ∈ center S)
    (hinside : ∀ u : S, u ∈ H → IsConj (z : G) (u : G) → u = z)
    (t x : S) (hx : x ^ 2 = z) (hxt : Commute x t)
    (hconj : IsConj (z : G) (t : G)) : t = z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj.symm
  let f : G ≃* G := MulAut.conj g
  have hft : f (t : G) = z := hg
  let C : Subgroup G := centralizer ({(z : G)} : Set G)
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hz ⟨s, hs⟩))
  let y : C := ⟨f (x : G), mem_centralizer_singleton_iff.mpr (by
    have hh := (hxt.map ((f : G →* G).comp (S : Subgroup G).subtype)).eq
    change f (x : G) * f (t : G) = f (t : G) * f (x : G) at hh
    rwa [hft] at hh)⟩
  have hy : orderOf y = orderOf x := by
    rw [← Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
  obtain ⟨m, hm⟩ := S.isPGroup'.exists_orderOf_dvd_pow x
  have hp : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card_dvd_pow (n := m) (by rw [Nat.card_zpowers, hy]; exact hm)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq C T (S.subtype hSC)
  have hyS : (MulAut.conj k) y ∈ S.subtype hSC := by
    rw [← hk]
    change (MulAut.conj k) • y ∈ (MulAut.conj k) • (T : Set C)
    exact Set.smul_mem_smul_set (hT (mem_zpowers y))
  let v : S := ⟨((MulAut.conj k) y : C), hyS⟩
  let a : G := (k : G) * g
  have hav : (MulAut.conj a) (z : G) = (v : G) ^ 2 := by
    rw [← hx, Subgroup.coe_pow, map_pow]
    congr 1
    simp [a, v, y, f, mul_assoc]
  have hvz : v ^ 2 = z := hinside (v ^ 2) (hsquares v)
    (isConj_iff.mpr ⟨a, hav⟩)
  have hat : (MulAut.conj a) (t : G) = z := by
    have hfix : (MulAut.conj (k : G)) (z : G) = z :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp k.property)
    calc
      _ = (MulAut.conj (k : G)) (f (t : G)) := by simp [a, f, mul_assoc]
      _ = z := by rw [hft]; exact hfix
  apply Subtype.ext
  exact (MulAut.conj a).injective
    (hat.trans (hav.trans (congrArg Subtype.val hvz)).symm)

/-- In an index-two extraspecial extension, an outside conjugate of the
central involution has elementary centralizer once inside-core fusion is
excluded. The assertion does not require the extraspecial group to have
order thirty-two. -/
public theorem elementary_centralizer_of_extraspecial_index_two_of_inside_fusion
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (H : Subgroup S) [IsExtraspecial 2 H]
    (hi : H.index = 2) (z : H) (hz : orderOf z = 2)
    (hzc : (z : S) ∈ center S)
    (hinside : ∀ u : S, u ∈ H → IsConj ((z : S) : G) (u : G) → u = z)
    (t : S) (ht : t ^ 2 = 1) (hout : t ∉ H)
    (hconj : IsConj ((z : S) : G) (t : G)) :
    IsElementaryAbelian 2 (centralizer ({t} : Set S)) := by
  have hzH : z ∈ center H := mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_center_iff.mp hzc x))
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hsquare (x : H) : x ^ 2 = 1 ∨ x ^ 2 = z := by
    obtain ⟨w, hw, hall⟩ := (Nat.card_eq_two_iff' (1 : center H)).mp
      (IsExtraspecial.center_order_p 2 H)
    by_cases hx : x ^ 2 = 1
    · exact Or.inl hx
    · right
      exact congrArg Subtype.val
        ((hall ⟨x ^ 2, IsExtraspecial.square_mem_center x⟩
          (fun h => hx (congrArg Subtype.val h))).trans
        (hall ⟨z, hzH⟩ (fun h => hz1 (congrArg Subtype.val h))).symm)
  have hpow (x : centralizer ({t} : Set S)) : x ^ 2 = 1 := by
    have hxt : Commute (x : S) t := mem_centralizer_singleton_iff.mp x.property
    have hcases : (x : S) ^ 2 = 1 ∨ (x : S) ^ 2 = z := by
      by_cases hxH : (x : S) ∈ H
      · exact (hsquare ⟨x, hxH⟩).imp (congrArg Subtype.val) (congrArg Subtype.val)
      · have htx : t * (x : S) ∈ H :=
          (mul_mem_iff_of_index_two hi).mpr (iff_of_false hout hxH)
        have he : (t * (x : S)) ^ 2 = (x : S) ^ 2 := by
          rw [hxt.symm.mul_pow, ht, one_mul]
        simpa only [Subgroup.coe_pow, OneMemClass.coe_one, he] using
          (hsquare ⟨t * (x : S), htx⟩).imp
            (congrArg Subtype.val) (congrArg Subtype.val)
    rcases hcases with hx | hx
    · exact Subtype.ext hx
    · have he := S.eq_of_isConj_of_squares_mem_of_inside_fusion H
        (sq_mem_of_index_two hi) z hzc hinside t x hx hxt hconj
      exact (hout (he ▸ z.property)).elim
  exact {
    toIsMulCommutative := ⟨⟨fun a b =>
      (Commute.of_orderOf_dvd_two (fun c => orderOf_dvd_of_pow_eq_one (hpow c)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }

/-- The index-two argument stops at an elementary subgroup of order at least
 eight: a core centralizer of order at least four and an outside involution
 generate such a subgroup. -/
public theorem not_isConj_of_extraspecial_index_two_of_inside_fusion_of_fixed_card
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (H : Subgroup S) [IsExtraspecial 2 H]
    (hi : H.index = 2) (z : H) (hz : orderOf z = 2)
    (hzc : (z : S) ∈ center S)
    (hinside : ∀ u : S, u ∈ H → IsConj ((z : S) : G) (u : G) → u = z)
    (t : S) (ht : t ^ 2 = 1) (hout : t ∉ H)
    (hfixed : 4 ≤ Nat.card (H ⊓ centralizer ({t} : Set S) : Subgroup S)) :
    ¬ IsConj ((z : S) : G) (t : G) := by
  intro hconj
  let C := centralizer ({t} : Set S)
  let F : Subgroup S := H ⊓ C
  let : IsElementaryAbelian 2 C :=
    S.elementary_centralizer_of_extraspecial_index_two_of_inside_fusion
      H hi z hz hzc hinside t ht hout hconj
  have hsmall := hrank C inferInstance
  have htc : t ∈ C := mem_centralizer_singleton_iff.mpr (Commute.refl t)
  have htF : t ∈ centralizer (F : Set S) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx.2
  have hle : F ⊔ zpowers t ≤ C := sup_le inf_le_right (zpowers_le.mpr htc)
  have hcard := card_sup_zpowers_of_normalizing_involution F t ht
    (fun h => hout h.1) (centralizer_le_normalizer _ htF)
  have hbound := card_le_of_le hle
  rw [hcard] at hbound
  change 4 ≤ Nat.card F at hfixed
  omega

end Sylow
