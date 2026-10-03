module

public import Theory.GroupTheory.WeaklyClosedSquareFusion
public import Theory.GroupTheory.PGroup.IsolatedFour
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Elementary involution centralizers over a cyclic-center core

Let a Sylow two-subgroup have an index-two subgroup R with cyclic center
and central squares. A central involution weakly closed in R has elementary
centralizer at every outside conjugate: splitting that centralizer over R
puts its squares in the cyclic center, and any nontrivial square supplies
a commuting square root of the central involution. Square fusion excludes it.

If the center of R has index four, every elementary subgroup of R has order
at most four, by counting its product with the cyclic center. The outside
centralizer consequently has order at most eight. When the Sylow contains
an elementary eight, the involution-centralizer theorem excludes order four,
so this centralizer has order exactly eight.

Source: Janko–Thompson (1970), §4, Case 2, printed p.393. The square-fusion
argument replaces the source's normalizer-moving argument and does not use
a bound on arbitrary elementary subgroups of the Sylow subgroup.
-/

open Subgroup

private theorem square_root {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (C : Subgroup P) [IsCyclic C] (z : C) (hz : orderOf z = 2)
    (x : P) (hx : x ^ 2 ∈ C) (hne : x ^ 2 ≠ 1) :
    ∃ n : ℕ, (x ^ n) ^ 2 = z := by
  let a : C := ⟨x ^ 2, hx⟩
  have ha : a ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have ho : orderOf (a ^ (orderOf a / 2)) = 2 :=
    orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos a))
      ((hP.to_subgroup C).dvd_orderOf ha)
  have he := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two ho hz)
  refine ⟨orderOf a / 2, ?_⟩
  simpa only [coe_pow, a, ← pow_mul, Nat.mul_comm] using he

/-- A cyclic center of index four bounds elementary binary subgroup orders by four. -/
public theorem Subgroup.elementary_card_le_four_of_cyclic_center_index_four {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hcard : Nat.card P = 4 * Nat.card (center P))
    (E : Subgroup P) [IsElementaryAbelian 2 E] : Nat.card E ≤ 4 := by
  let Z := center P
  let I := E ⊓ Z
  let : IsCyclic I := isCyclic_of_le (show I ≤ Z from inf_le_right)
  have hI : Nat.card I ≤ 2 := by
    apply Nat.le_of_dvd (by decide : 0 < 2)
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x x.property.1)
  have hproper : E ⊔ Z ≠ ⊤ := by
    intro ht
    have hEZ : E ≤ Z := by
      have hall : (⊤ : Subgroup P) ≤ centralizer (E : Set P) := by
        rw [← ht]
        exact sup_le (le_centralizer E) (center_le_centralizer _)
      simpa only [coe_top, centralizer_univ] using le_centralizer_iff.mp hall
    have hz : Z = ⊤ := by simpa only [sup_eq_right.mpr hEZ] using ht
    have he : Nat.card Z = Nat.card P := by rw [hz, card_top]
    have hp : 0 < Nat.card P := Nat.card_pos
    change Nat.card P = 4 * Nat.card Z at hcard
    omega
  have hi : 2 ≤ (E ⊔ Z).index := by
    have := (E ⊔ Z).index_ne_zero_of_finite
    have hn := mt index_eq_one.mp hproper
    omega
  have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes E Z
    ((center_le_centralizer (E : Set P)).trans (Subgroup.centralizer_le_normalizer _))
  have ht := (E ⊔ Z).card_mul_index
  have hp : 0 < Nat.card Z := Nat.card_pos
  change Nat.card P = 4 * Nat.card Z at hcard
  change Nat.card E * Nat.card Z = Nat.card I * Nat.card (E ⊔ Z : Subgroup P) at hm
  nlinarith


namespace Sylow

/-- An outside conjugate of a weakly closed central involution has elementary
centralizer over an index-two core with cyclic center and central squares. -/
public theorem elementary_centralizer_of_cyclic_core {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (R : Subgroup S) (hi : R.index = 2)
    [IsCyclic (center R)] (hsq : ∀ r : R, r ^ 2 ∈ center R)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2) (hzR : z ∈ R)
    (hweak : ∀ u : S, u ∈ R → IsConj (z : G) (u : G) → u = z)
    (t : S) (hout : t ∉ R) (hconj : IsConj (z : G) (t : G)) :
    IsElementaryAbelian 2 (centralizer ({t} : Set S)) := by
  have ht : t ^ 2 = 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    apply Subtype.ext
    have hz2 : z ^ 2 = 1 := (by simpa only [hz] using pow_orderOf_eq_one z)
    have he := congrArg (fun y : G => y ^ 2) hg
    change (MulAut.conj g) (z : G) ^ 2 = (t : G) ^ 2 at he
    rw [← map_pow] at he
    simpa only [← coe_pow, hz2, coe_one, map_one] using he.symm
  let zR : R := ⟨z, hzR⟩
  have hzRC : zR ∈ center R := mem_center_iff.mpr
    (fun r => Subtype.ext (mem_center_iff.mp hzC r))
  let Z := (center R).map R.subtype
  let : IsCyclic Z := isCyclic_of_surjective
    (R.subtype.subgroupMap (center R)) (R.subtype.subgroupMap_surjective (center R))
  let zZ : Z := ⟨z, mem_map_of_mem R.subtype hzRC⟩
  have hzZ : orderOf zZ = 2 := (orderOf_coe zZ).symm.trans hz
  have hp (x : centralizer ({t} : Set S)) : x ^ 2 = 1 := by
    have hxt : Commute (x : S) t := mem_centralizer_singleton_iff.mp x.property
    have hxZ : (x : S) ^ 2 ∈ Z := by
      by_cases hxR : (x : S) ∈ R
      · exact mem_map_of_mem R.subtype (hsq ⟨x, hxR⟩)
      · have hr : t * (x : S) ∈ R :=
          (mul_mem_iff_of_index_two hi).mpr (iff_of_false hout hxR)
        have hh := mem_map_of_mem R.subtype (hsq ⟨t * (x : S), hr⟩)
        change (t * (x : S)) ^ 2 ∈ Z at hh
        simpa only [hxt.symm.mul_pow, ht, one_mul] using hh
    apply Subtype.ext
    by_contra hx
    obtain ⟨n, hn⟩ := square_root S.isPGroup' Z zZ hzZ x hxZ hx
    have he := S.eq_of_isConj_of_commuting_square_root_of_weakly_closed_squares z t
      ((x : S) ^ n) hzC ((by simpa only [hz] using pow_orderOf_eq_one z))
      (fun v hv => hweak _ (sq_mem_of_index_two hi v) hv) hconj hn (hxt.pow_left n)
    exact hout (he ▸ hzR)
  exact {
    toIsMulCommutative := ⟨⟨fun a b =>
      (Commute.of_orderOf_dvd_two (fun c => orderOf_dvd_of_pow_eq_one (hp c)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hp }

end Sylow

namespace Sylow

/-- An elementary outside centralizer has order eight if the core has elementary
rank at most two and the Sylow subgroup has elementary rank at least three. -/
public theorem card_centralizer_eq_eight_of_elementary_of_index_two_core {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (R : Subgroup S) (hi : R.index = 2)
    (hrank : ∀ F : Subgroup R, IsElementaryAbelian 2 F → Nat.card F ≤ 4)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2) (hzR : z ∈ R)
    (t : S) (hout : t ∉ R)
    [IsElementaryAbelian 2 (centralizer ({t} : Set S))] :
    Nat.card (centralizer ({t} : Set S)) = 8 := by
  let E := centralizer ({t} : Set S)
  let I := E ⊓ R
  have htE : t ∈ E := mem_centralizer_singleton_iff.mpr rfl
  have hzE : z ∈ E := mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzC t).symm
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) t htE
  have hI : Nat.card I ≤ 4 := by
    let f := (inclusion (show I ≤ E from inf_le_left)).comp
      (subgroupOfEquivOfLe (show I ≤ R from inf_le_right)).toMonoidHom
    have hf : Function.Injective f :=
      (inclusion_injective (show I ≤ E from inf_le_left)).comp
        (subgroupOfEquivOfLe (show I ≤ R from inf_le_right)).injective
    have he : IsElementaryAbelian 2 (I.subgroupOf R) := {
      toIsMulCommutative := isMulCommutative_iff.mpr (fun a b => hf (by
        rw [map_mul, map_mul]
        exact mul_comm' _ _))
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun a => hf (by
        rw [map_pow, map_one]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 E) (f a))) }
    have hh := hrank (I.subgroupOf R) he
    rwa [Nat.card_congr (subgroupOfEquivOfLe (show I ≤ R from inf_le_right)).toEquiv] at hh
  have hindex : I.relIndex E ≤ 2 := by
    change (E ⊓ R).relIndex E ≤ 2
    rw [inf_relIndex_left]
    apply Nat.le_of_dvd (by decide : 0 < 2)
    let : R.Normal := R.normal_of_index_eq_two hi
    simpa only [hi] using R.relIndex_dvd_index_of_normal E
  have hmul := (I.subgroupOf E).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show I ≤ E from inf_le_left)).toEquiv] at hmul
  change Nat.card I * I.relIndex E = Nat.card E at hmul
  have hle : Nat.card E ≤ 8 := by nlinarith
  have hge : 4 ≤ Nat.card E := by
    have hzc : zpowers z ≤ E := zpowers_le.mpr hzE
    have hzt : t ∈ centralizer (zpowers z : Set S) := by
      intro v hv
      obtain ⟨n, rfl⟩ := hv
      exact (show Commute z t from (mem_center_iff.mp hzC t).symm).zpow_left n |>.eq
    have hh := card_sup_zpowers_of_normalizing_involution (zpowers z) t ht2
      (fun h => hout (zpowers_le.mpr hzR h)) (Subgroup.centralizer_le_normalizer _ hzt)
    rw [Nat.card_zpowers, hz] at hh
    have hb := card_le_of_le (sup_le hzc (zpowers_le.mpr htE))
    change Nat.card (zpowers z ⊔ zpowers t : Subgroup S) ≤ Nat.card E at hb
    exact le_trans (show 4 ≤ Nat.card (zpowers z ⊔ zpowers t : Subgroup S) by
      exact hh.ge) hb
  have hne : Nat.card E ≠ 4 := by
    intro h4
    have hself : centralizer (E : Set S) = E := by
      apply le_antisymm
      · intro x hx
        exact mem_centralizer_singleton_iff.mpr (hx t htE).symm
      · exact le_centralizer E
    exact centralizer_ne_self_of_four_of_central_involution S.isPGroup' A E hA h4
      z hzE (by intro he; simp [he] at hz) hzC hself
  obtain ⟨n, hn⟩ := (S.isPGroup'.to_subgroup E).exists_card_eq
  have hn3 : n ≤ 3 := by
    by_contra h
    have hh := Nat.pow_le_pow_right (n := 2) (by decide) (show 4 ≤ n by omega)
    rw [← hn] at hh
    norm_num at hh
    omega
  change Nat.card E = 8
  change Nat.card E = 2 ^ n at hn
  rw [hn] at hle hge hne ⊢
  interval_cases n <;> norm_num at *

end Sylow
