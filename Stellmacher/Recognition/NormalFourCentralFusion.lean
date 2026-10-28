module

public import Theory.GroupTheory.PGroup.RankTwoFour
public import Stellmacher.Recognition.SimpleInvolutionFusion

/-!
# Fusion in the nonabelian central-four case

When first omega of the Sylow center has order four and all elementary binary
subgroups have order less than eight, every Sylow involution is central.
Z-star gives each involution a distinct conjugate in the Sylow subgroup.
Burnside fusion realizes this conjugacy inside the Sylow normalizer. In
particular the normalizer is strictly larger than the product of the Sylow
subgroup and its centralizer.

This proves the fusion reduction in Janko–Thompson, Math. Z. 113 (1970),
Lemma 5.1, pp.393–394, under the stronger elementary rank bound used here.
The remaining structural input is the nontrivial-normalizer case of their
Theorem 1.3 (MacWilliams): the order-64 conclusion and the center, derived,
and Frattini equalities. No ambient classification is used in this module.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaFour

open Subgroup

/-- Every Sylow involution belongs to the Sylow center. -/
public theorem involution_mem_center
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4)
    {z : S} (hz : orderOf z = 2) : z ∈ center S :=
  mem_center_of_square_eq_one_of_omega_center_card_four
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) hfour
    (by simpa only [hz] using pow_orderOf_eq_one z)

private theorem coe_mem_centralizer_of_mem_center
    {G : Type*} [Group G] (S : Sylow 2 G) {z : S} (hz : z ∈ center S) :
    (z : G) ∈ centralizer (S : Set G) := by
  intro x hx
  exact congrArg Subtype.val (mem_center_iff.mp hz (⟨x, hx⟩ : S))

/-- Each involution has a distinct conjugate under the Sylow normalizer. -/
public theorem exists_distinct_normalizer_conjugate
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (z : S) (hz : orderOf z = 2) :
    ∃ (t : S) (n : G), t ≠ z ∧ n ∈ normalizer (S : Set G) ∧
      n⁻¹ * (z : G) * n = t := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htz, hconj⟩ := exists_distinct_isConj_in_sylow hns S z hz
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have ht : orderOf t = 2 := by
    rw [← orderOf_coe t, ← hg, ← MulAut.conj_apply]
    simpa using ((MulAut.conj g).orderOf_eq (z : G)).trans
      ((orderOf_coe z).trans hz)
  have hzc := coe_mem_centralizer_of_mem_center S (involution_mem_center S hrank hfour hz)
  have htc := coe_mem_centralizer_of_mem_center S (involution_mem_center S hrank hfour ht)
  obtain ⟨n, hn, he⟩ := S.conj_eq_normalizer_conj_of_mem_centralizer (z : G) g⁻¹
    hzc (by simpa only [inv_inv, hg] using htc)
  exact ⟨t, n, htz, hn, he.symm.trans (by simpa only [inv_inv] using hg)⟩

/-- The three Sylow involutions form a single ambient conjugacy class.
Each class has at least two elements by Z-star, so two distinct classes
would give at least four involutions in a four-group. -/
public theorem involutions_isConj
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (z t : S) (hz : orderOf z = 2) (ht : orderOf t = 2) :
    IsConj (z : G) (t : G) := by
  classical
  let E := omega₁ S (p := 2)
  have hE : Nat.card E = 4 := by
    rw [show E = (omega₁ (center S) (p := 2)).map (center S).subtype from
      omega_one_eq_map_center_of_card_four
        (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) hfour]
    rwa [card_map_of_injective (center S).subtype_injective]
  have hmem (a b : S) (ha : orderOf a = 2) (hc : IsConj (a : G) (b : G)) : b ∈ E := by
    have ha2 : (a : G) ^ 2 = 1 := by
      exact congrArg Subtype.val (show a ^ 2 = 1 by simpa only [ha] using pow_orderOf_eq_one a)
    have hb2 : (b : G) ^ 2 = 1 := by
      have hh := IsConj.pow 2 hc
      rwa [ha2, isConj_one_right] at hh
    exact subset_closure (by simpa using (show b ^ 2 = 1 from Subtype.ext hb2))
  have hne (a b : S) (ha : orderOf a = 2) (hc : IsConj (a : G) (b : G)) : b ≠ 1 := by
    intro hb
    have ha1 : a = 1 := Subtype.ext (isConj_one_left.mp (by simpa [hb] using hc))
    simp [ha1] at ha
  by_contra hn
  obtain ⟨u, huz, hzu⟩ := exists_distinct_isConj_in_sylow hns S z hz
  obtain ⟨v, hvt, htv⟩ := exists_distinct_isConj_in_sylow hns S t ht
  have hz1 := hne z z hz (IsConj.refl _)
  have ht1 := hne t t ht (IsConj.refl _)
  have hu1 := hne z u hz hzu
  have hv1 := hne t v ht htv
  have hzt : z ≠ t := fun he => hn (he ▸ IsConj.refl (z : G))
  have hzv : z ≠ v := fun he => hn ((he ▸ htv).symm)
  have htu : t ≠ u := fun he => hn (he ▸ hzu)
  have huv : u ≠ v := fun he => hn (hzu.trans (he ▸ htv.symm))
  let : Fintype E := Fintype.ofFinite E
  let a : E := ⟨z, hmem z z hz (IsConj.refl _)⟩
  let b : E := ⟨t, hmem t t ht (IsConj.refl _)⟩
  let c : E := ⟨u, hmem z u hz hzu⟩
  let d : E := ⟨v, hmem t v ht htv⟩
  have hcard := Finset.card_le_univ ({1, a, b, c, d} : Finset E)
  have hnat : Fintype.card E = 4 := by rwa [← Nat.card_eq_fintype_card]
  have hfive : ({1, a, b, c, d} : Finset E).card = 5 := by
    simp [a, b, c, d, Subtype.ext_iff, hzt, Ne.symm huz, hzv, htu,
      Ne.symm hvt, huv, Ne.symm hz1, Ne.symm ht1, Ne.symm hu1, Ne.symm hv1]
  omega

/-- Burnside fusion makes the Sylow normalizer transitive on the three
involutions, without assuming the Lyons structural conclusion. -/
public theorem involutions_normalizer_conjugate
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (z t : S) (hz : orderOf z = 2) (ht : orderOf t = 2) :
    ∃ n ∈ normalizer (S : Set G), n⁻¹ * (z : G) * n = t := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_isConj hns S hrank hfour z t hz ht)
  have hzc := coe_mem_centralizer_of_mem_center S (involution_mem_center S hrank hfour hz)
  have htc := coe_mem_centralizer_of_mem_center S (involution_mem_center S hrank hfour ht)
  obtain ⟨n, hn, he⟩ := S.conj_eq_normalizer_conj_of_mem_centralizer (z : G) g⁻¹
    hzc (by simpa only [inv_inv, hg] using htc)
  exact ⟨n, hn, he.symm.trans (by simpa only [inv_inv] using hg)⟩

/-- The self-normalizer-product branch is impossible under the rank bound.
This uses neither the N2 hypothesis nor noncommutativity of the Sylow. -/
public theorem normalizer_ne_sup_centralizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4) :
    normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hfour]; decide)
  let z : S := (w : center S)
  have hz : orderOf z = 2 := (orderOf_coe (w : center S)).trans
    ((orderOf_coe w).trans hw)
  obtain ⟨t, n, htz, hn, he⟩ := exists_distinct_normalizer_conjugate hns S hrank hfour z hz
  intro hN
  have hfix : (S : Subgroup G) ⊔ centralizer (S : Set G) ≤
      centralizer ({(z : G)} : Set G) := by
    apply sup_le
    · intro s hs
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val
        (mem_center_iff.mp (involution_mem_center S hrank hfour hz) (⟨s, hs⟩ : S))
    · intro c hc
      exact mem_centralizer_singleton_iff.mpr (hc z z.property).symm
  have hcomm := mem_centralizer_singleton_iff.mp (hfix (hN ▸ hn))
  have heq : (t : G) = z := by
    rw [← he, mul_assoc, ← hcomm, inv_mul_cancel_left]
  exact htz (Subtype.ext heq)

end Stellmacher.Recognition.NormalFourCentralOmegaFour
