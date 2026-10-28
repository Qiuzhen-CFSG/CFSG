module

public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PGroup.UniqueCentralInvolutionNormal

/-!
# Disjoint conjugate factors in an index-two configuration

Let `S` have index two in a finite two-group `T`, and let `t ∈ T − S`.
Suppose `S ≤ N`, `U ≤ S`, `N` normalizes `U`, and `t` normalizes `N`.
Then `T` normalizes the intersection of `U` and its `t`-conjugate.
If `T` has a unique central involution and that involution is absent from
`U`, the intersection is trivial. Both factors are normal in `N`, so
they commute, and multiplication gives their internal direct product.

This is the group-theoretic argument in Aschbacher–Smith 15.3.32(5),
combined manuscript (1 March 2004), printed p.1133. Normality is relative
to `N`; no normality in the ambient group is required.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- An invariant actor normalizes the conjugate of every subgroup it normalizes. -/
theorem normalizes_conjugate_of_normalizes {N U : Subgroup G} {t : G}
    (htN : t ∈ normalizer (N : Set G)) (hNU : N ≤ normalizer (U : Set G)) :
    N ≤ normalizer (U.conjBy t : Set G) := by
  rw [show U.conjBy t = U.map (MulAut.conj t).toMonoidHom from rfl,
    ← map_equiv_normalizer_eq U (MulAut.conj t)]
  have hn := map_mono (f := (MulAut.conj t).toMonoidHom) hNU
  have he : N.map (MulAut.conj t).toMonoidHom = N :=
    mem_normalizer_iff_map_conj_eq.mp htN
  rwa [he] at hn

private theorem index_two_normalizes_of_square
    {S T U : Subgroup G} (hindex : (S.subgroupOf T).index = 2)
    {t : G} (ht : t ∈ T) (htS : t ∉ S)
    (hSU : S ≤ normalizer (U : Set G)) (htu : t ∈ normalizer (U : Set G)) :
    T ≤ normalizer (U : Set G) := by
  intro x hx
  by_cases hxS : x ∈ S
  · exact hSU hxS
  · have hxt : x * t⁻¹ ∈ S := by
      apply ((S.subgroupOf T).mul_mem_iff_of_index_two hindex
        (a := (⟨x, hx⟩ : T)) (b := (⟨t, ht⟩ : T)⁻¹)).mpr
      change x ∈ S ↔ t⁻¹ ∈ S
      simp only [S.inv_mem_iff, hxS, htS]
    simpa only [inv_mul_cancel_right] using
      (normalizer (U : Set G)).mul_mem (hSU hxt) htu

/-- Conjugation by the outside coset interchanges the two factors, so their
intersection is invariant under the entire two-group. -/
theorem index_two_normalizes_conjugate_inf
    {S T N U : Subgroup G} (hindex : (S.subgroupOf T).index = 2)
    {t : G} (ht : t ∈ T) (htS : t ∉ S)
    (hSN : S ≤ N) (htN : t ∈ normalizer (N : Set G))
    (hNU : N ≤ normalizer (U : Set G)) :
    T ≤ normalizer ((U ⊓ U.conjBy t : Subgroup G) : Set G) := by
  have hNUt := normalizes_conjugate_of_normalizes htN hNU
  have hSU : S ≤ normalizer (U : Set G) := hSN.trans hNU
  have hSinf : S ≤ normalizer ((U ⊓ U.conjBy t : Subgroup G) : Set G) := by
    intro s hs x
    exact and_congr (hSU hs x) ((hSN.trans hNUt) hs x)
  have ht2 : t ^ 2 ∈ S := (S.subgroupOf T).sq_mem_of_index_two hindex ⟨t, ht⟩
  have hswap : (U.conjBy t).conjBy t = U := by
    rw [conjBy_conjBy, ← pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp (hSU ht2)
  apply index_two_normalizes_of_square hindex ht htS hSinf
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_inf _ _ _ (MulAut.conj t).injective]
  change U.conjBy t ⊓ (U.conjBy t).conjBy t = U ⊓ U.conjBy t
  rw [hswap, inf_comm]

/-- The unique central involution forces the conjugate factors to be disjoint. -/
theorem disjoint_conjugate_of_avoiding_central_involution [Finite G]
    {S T N U : Subgroup G} (hT : IsPGroup 2 T)
    (hZ : Nat.card (omega₁ (center T) (p := 2)) = 2)
    (z : T) (hzC : z ∈ center T) (hz : orderOf z = 2)
    (hzU : (z : G) ∉ U) (hUS : U ≤ S) (hST : S ≤ T)
    (hindex : (S.subgroupOf T).index = 2)
    {t : G} (ht : t ∈ T) (htS : t ∉ S)
    (hSN : S ≤ N) (htN : t ∈ normalizer (N : Set G))
    (hNU : N ≤ normalizer (U : Set G)) : Disjoint U (U.conjBy t) := by
  let D := U ⊓ U.conjBy t
  have hDT : D ≤ T := inf_le_left.trans (hUS.trans hST)
  let _ : (D.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer
    (index_two_normalizes_conjugate_inf hindex ht htS hSN htN hNU)
  have he : D.subgroupOf T = ⊥ :=
    hT.normal_eq_bot_of_avoiding_unique_central_involution hZ z hzC hz
      (D.subgroupOf T) (fun h => hzU h.1)
  apply disjoint_iff.mpr
  change D = ⊥
  rw [← map_subgroupOf_eq_of_le hDT, he, map_bot]

/-- Disjoint factors normalized by the same overgroup commute inside it. -/
theorem commuting_of_disjoint_of_normalizes
    {N U V : Subgroup G} (hUN : U ≤ N) (hVN : V ≤ N)
    (hNU : N ≤ normalizer (U : Set G)) (hNV : N ≤ normalizer (V : Set G))
    (hd : Disjoint U V) : U ≤ centralizer (V : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply eq_bot_iff.mpr
  have hU : ⁅U, V⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp (hVN.trans hNU)
  have hV : ⁅U, V⁆ ≤ V := le_normalizer_iff_commutator_le_right.mp (hUN.trans hNV)
  exact (le_inf hU hV).trans (disjoint_iff.mp hd).le

/-- The internal direct-product conclusion retains the actual multiplication
map and normalization by the indicated local overgroup. -/
theorem conjugate_pair_direct_product
    {S N U : Subgroup G} {t : G} (hUS : U ≤ S) (hSN : S ≤ N)
    (htN : t ∈ normalizer (N : Set G)) (hNU : N ≤ normalizer (U : Set G))
    (hd : Disjoint U (U.conjBy t)) :
    N ≤ normalizer ((U ⊔ U.conjBy t : Subgroup G) : Set G) ∧
      U ≤ centralizer (U.conjBy t : Set G) ∧
      ∃ e : U × U.conjBy t ≃* ↥(U ⊔ U.conjBy t),
        ∀ u v, (e (u, v) : G) = (u : G) * (v : G) := by
  have hNUt := normalizes_conjugate_of_normalizes htN hNU
  have hUtN : U.conjBy t ≤ N := by
    rintro x ⟨u, hu, rfl⟩
    exact (htN u).mp ((hUS.trans hSN) hu)
  have hc := commuting_of_disjoint_of_normalizes (hUS.trans hSN) hUtN hNU hNUt hd
  exact ⟨(le_inf hNU hNUt).trans (normalizer_inf_normalizer_le_normalizer_sup _ _),
    hc, exists_mulEquiv_prod_sup_of_disjoint_of_commuting U (U.conjBy t) hd hc⟩

end Subgroup

end
