module
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.FourGroupChoice.Replacement

/-!
# Squares and the two inner Sylow factors

Source: Aschbacher–Smith, printed pp.569–570. The product `S_K S_Kˣ` is
normalized by the crossing element. Using the model orders eight and 64,
it is exactly `N_S(E)` for each four-group `E ≤ S_K`. Its index in `S` is two.
Thus square stability is equivalent to membership in this product and is
unchanged by replacing `x` by `xs`. This identifies, rather than assumes away,
the outstanding square-membership argument in the source construction.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction
open Subgroup
variable {G : Type*} [Group G]

/-- The crossing element normalizes the product of the two inner Sylow factors.
This uses `x² ∈ S` and relative normality of `K`; it does not say that `x²`
normalizes a four-group. -/
public theorem Setup.crossing_normalizes_factor_product (d : Setup G) :
    d.x ∈ normalizer ((d.sk ⊔ conjugate d.x d.sk : Subgroup G) : Set G) := by
  have hK := (normal_subgroupOf_iff_le_normalizer (CoreReduction.k_le_h d)).mp d.normalK
  have hD : d.S ≤ normalizer (d.sk : Set G) := by
    intro s hs
    exact inf_normalizer_le_normalizer_inf
      ⟨d.S.le_normalizer hs, hK (CoreReduction.s_le_h d hs)⟩
  exact normalizes_join_conjugate_of_square_normalizes d.sk (hD d.square_mem)

/-- For an `x`-stable subgroup of index two in `S`, membership of the square
in that subgroup depends only on the coset `xS`. Thus changing representatives
cannot by itself supply a missing square-stability argument. -/
public theorem Setup.square_replaceX_mem_iff (d : Setup G) (U : Subgroup G)
    (hindex : (U.subgroupOf d.S).index = 2)
    (hxU : d.x ∈ normalizer (U : Set G)) (s : d.S) :
    (d.replaceX s).x ^ 2 ∈ U ↔ d.x ^ 2 ∈ U := by
  let sx : d.S := ⟨d.x⁻¹ * (s : G) * d.x, by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (d.S : Set G)).inv_mem d.x_normalizes) s).mp
        s.property⟩
  have hsx : sx ∈ U.subgroupOf d.S ↔ s ∈ U.subgroupOf d.S := by
    change d.x⁻¹ * (s : G) * d.x ∈ U ↔ (s : G) ∈ U
    have h := mem_normalizer_iff.mp ((normalizer (U : Set G)).inv_mem hxU) (s : G)
    simpa only [inv_inv] using h.symm
  have hp : sx * s ∈ U.subgroupOf d.S :=
    (mul_mem_iff_of_index_two hindex).mpr hsx
  have hpG : (d.x⁻¹ * (s : G) * d.x) * s ∈ U := hp
  have heq : (d.replaceX s).x ^ 2 = d.x ^ 2 * ((d.x⁻¹ * (s : G) * d.x) * s) := by
    change (d.x * (s : G)) ^ 2 = _
    simp only [pow_two]
    group
  rw [heq, U.mul_mem_cancel_right hpG]

variable [Finite G]

/-- Once the finite normalizer orders are known, the four-group normalizer
inside `S` is exactly the product of the two commuting inner Sylow factors. -/
public theorem Setup.four_normalizer_eq_factor_product (d : Setup G)
    (hDcard : Nat.card d.sk = 8) (E : Subgroup G) [IsKleinFour E]
    (hE : E ≤ d.sk)
    (hUcard : Nat.card (d.S ⊓ normalizer (E : Set G) : Subgroup G) = 64) :
    d.S ⊓ normalizer (E : Set G) = d.sk ⊔ conjugate d.x d.sk := by
  have hEcard : Nat.card (E.subgroupOf d.sk) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hE).toEquiv]
    exact IsKleinFour.card_four
  have hindex : (E.subgroupOf d.sk).index = 2 := by
    have hi := (E.subgroupOf d.sk).card_mul_index
    rw [hEcard, hDcard] at hi
    omega
  have hDN : d.sk ≤ normalizer (E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hE).mp (normal_of_index_eq_two hindex)
  have hDXN : conjugate d.x d.sk ≤ normalizer (E : Set G) := by
    intro a ha
    apply centralizer_le_normalizer _
    intro e he
    exact (d.sk_centralizes_conjugate (hE he) a ha).symm
  have hBS : d.sk ⊔ conjugate d.x d.sk ≤ d.S :=
    sup_le inf_le_left (CoreReduction.conjugate_le d inf_le_left)
  have hBN : d.sk ⊔ conjugate d.x d.sk ≤ normalizer (E : Set G) := sup_le hDN hDXN
  have hDXcard : Nat.card (conjugate d.x d.sk) = 8 := by
    unfold conjugate
    rw [MulEquiv.toMonoidHom_eq_coe,
      ← Nat.card_congr ((MulAut.conj d.x⁻¹).subgroupMap d.sk).toEquiv]
    exact hDcard
  obtain ⟨f, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting d.sk
    (conjugate d.x d.sk) d.disjoint_sk_conjugate d.sk_centralizes_conjugate
  have hBcard : Nat.card (d.sk ⊔ conjugate d.x d.sk : Subgroup G) = 64 := by
    rw [← Nat.card_congr f.toEquiv, Nat.card_prod, hDcard, hDXcard]
  exact (eq_of_le_of_card_ge (le_inf hBS hBN) (by rw [hUcard, hBcard])).symm

/-- Under the actual orders of the two local normalizers, square stability
cannot be repaired by replacing `x` with another representative of `xS`. -/
public theorem Setup.four_square_replaceX_iff (d : Setup G) (r : CoreReduction d)
    (hDcard : Nat.card d.sk = 8) (E : Subgroup G) [IsKleinFour E]
    (hE : E ≤ d.sk)
    (hUcard : Nat.card (d.S ⊓ normalizer (E : Set G) : Subgroup G) = 64)
    (s : d.S) :
    (d.replaceX s).x ^ 2 ∈ normalizer (E : Set G) ↔
      d.x ^ 2 ∈ normalizer (E : Set G) := by
  let U := d.S ⊓ normalizer (E : Set G)
  have hindex : (U.subgroupOf d.S).index = 2 := by
    have hi := (U.subgroupOf d.S).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show U ≤ d.S from inf_le_left)).toEquiv,
      hUcard, r.card_s] at hi
    omega
  have hxU : d.x ∈ normalizer (U : Set G) := by
    dsimp only [U]
    rw [d.four_normalizer_eq_factor_product hDcard E hE hUcard]
    exact d.crossing_normalizes_factor_product
  have hh := d.square_replaceX_mem_iff U hindex hxU s
  have hsq : (d.replaceX s).x ^ 2 ∈ d.S := (d.replaceX s).square_mem
  simpa only [U, mem_inf, hsq, d.square_mem, true_and] using hh

end CFSG.Quasithin.Chapter2.A6ShadowConstruction
