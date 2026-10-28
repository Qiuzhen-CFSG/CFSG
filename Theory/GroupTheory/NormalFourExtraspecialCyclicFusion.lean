module

public import Theory.GroupTheory.NormalFourCentralizerAutomorphisms
public import Theory.GroupTheory.PGroup.ExtraspecialAbelianIndexTwo
public import Theory.GroupTheory.NormalFourFusion
public import Theory.GroupTheory.NormalFourWeaklyClosedInvolution

/-!
# Fusion exclusion over an extraspecial core with cyclic quotient of order four

Let a rank-two Sylow two-subgroup have a unique normal four and one central
involution. Suppose the four lies in an extraspecial normal subgroup of order
greater than eight, with cyclic quotient of order four. Then the central
involution is weakly closed in the Sylow subgroup.

Fusion in the four would make all squares of its nonabelian centralizer lie
in the four. But the extraspecial subgroup does not centralize the four, so
the index-two centralizer surjects onto the cyclic quotient of order four.
This is incompatible with its square bound. The unique-normal-four weak
closure theorem then extends exclusion from the four to the whole Sylow.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, p.389, the minus-type core
fusion step. The argument here uses the stronger elementary rank bound to
replace the cited Sylow classifications by intrinsic three-involution theory.
-/

open Subgroup

namespace Sylow

/-- A cyclic-four quotient over a large extraspecial normal subgroup prevents
fusion of the unique central involution anywhere in the Sylow subgroup. -/
public theorem eq_of_isConj_of_extraspecial_cyclic_four_quotient
    {G : Type*} [Group G] [Finite G]
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (K : Subgroup S) [K.Normal] [IsExtraspecial 2 K]
    (hK : 8 < Nat.card K) (hEK : E ≤ K)
    (hiK : K.index = 4) [IsCyclic (S ⧸ K)]
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (t : S) (hconj : IsConj (z : G) (t : G)) : t = z := by
  have hr := elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)
  let C := centralizer (E : Set S)
  have hiC : C.index = 2 :=
    centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
      S.isPGroup' hZ E hE
  let : C.Normal := C.normal_of_index_eq_two hiC
  have hnot : ¬ K ≤ C := by
    intro hKC
    have hcenter : E.subgroupOf K ≤ center K := by
      intro e he
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext ((hKC k.property) e he).symm
    have hc := card_le_of_le hcenter
    rw [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv, hE,
      IsExtraspecial.center_order_p 2 K] at hc
    omega
  have hnonab : ¬ IsMulCommutative C := by
    intro hab
    let : IsMulCommutative C := hab
    let A := C.subgroupOf K
    have hiA : A.index = 2 := by
      have hd : C.relIndex K ∣ 2 := by
        simpa only [hiC] using (relIndex_dvd_index_of_normal (H := C) (K := K))
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
      · exact (hnot (relIndex_eq_one.mp h)).elim
      · exact h
    have hZA : center K ≤ A := by
      intro k hk e he
      exact congrArg Subtype.val (mem_center_iff.mp hk (⟨e, hEK he⟩ : K))
    exact IsExtraspecial.not_isMulCommutative_of_index_two hK A hiA hZA
      (C.comap_injective_isMulCommutative K.subtype_injective)
  have hzE : z ∈ E := mem_four_of_square_eq_one_of_elementary_card_lt_eight
    hr E hE (by simpa only [hz] using pow_orderOf_eq_one z)
      (center_le_centralizer _ hzc)
  apply S.eq_of_isConj_of_weakly_closed_in_unique_normal_four hrank E hE hunique
    z hzc hz ?_ t hconj
  intro u hu hzu
  by_contra huz
  have hu1 : u ≠ 1 := by
    intro he
    have hz1 : (z : G) = 1 := isConj_one_left.mp (by simpa [he] using hzu)
    have : z = 1 := Subtype.ext hz1
    simp [this] at hz
  have hfusion := normal_four_fusion_of_central_isConj E hE
    (four_not_le_center_of_card_omega_one_center_eq_two hZ E hE)
    (⟨z, hzE⟩ : E) hzc
    (fun he => (orderOf_eq_prime_iff.mp hz).2 (congrArg Subtype.val he))
    (S : Subgroup G).subtype (⟨u, hu⟩ : E)
    (fun he => hu1 (congrArg Subtype.val he))
    (fun he => huz (congrArg Subtype.val he)) hzu
  have hsq := S.centralizer_squares_mem_four_of_fusion hr hZ E hE hunique
    z hz hzc hfusion hnonab
  let q := QuotientGroup.mk' K
  have hquot : Nat.card (S ⧸ K) = 4 := by rw [← index_eq_card, hiK]
  obtain ⟨v, hv⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S ⧸ K)
  rw [hquot] at hv
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K v
  have hlift : ∃ c : C, q c = q g := by
    by_cases hg : g ∈ C
    · exact ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨k, hk, hkC⟩ := SetLike.not_le_iff_exists.mp hnot
    have hkg : k * g ∈ C := (C.mul_mem_iff_of_index_two hiC).mpr
      (by simp only [hkC, hg])
    refine ⟨⟨k * g, hkg⟩, ?_⟩
    change q (k * g) = q g
    have hkq : q k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    rw [map_mul, hkq, one_mul]
  obtain ⟨c, hc⟩ := hlift
  have hc2 : (q g) ^ 2 = 1 := by
    rw [← hc, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hEK (hsq c))
  have hd := orderOf_dvd_iff_pow_eq_one.mpr hc2
  rw [hv] at hd
  norm_num at hd

end Sylow
