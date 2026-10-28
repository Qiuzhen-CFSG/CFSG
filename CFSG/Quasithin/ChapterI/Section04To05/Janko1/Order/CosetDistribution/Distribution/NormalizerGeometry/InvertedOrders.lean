module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.NormalizerGeometry.FourGroups

/-!
# Orders of inverted subgroups in Bender's normalizer

An already constructed subgroup inverted elementwise by an outside involution
is abelian. Its order divides 168 and is indivisible by four, by the literal
normalizer-overlap calculation. If it contains a seven-subgroup, the involution
normalizes that seven-subgroup; the supplied assertion (4.3) makes its ambient
centralizer equal to itself. The whole inverted subgroup therefore has order
seven. The other possible orders are one, two, three and six.

The order restriction does not presuppose closure of the inversion set.
Given explicit pairwise commutation, the subsequent construction proves closure
and applies the resulting subgroup to the actual right-coset involution fibers.
Pairwise commutation remains a separate obligation in the source argument.
Source: Bender, *Finite groups with large subgroups* (1974), §4, printed p.226.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

omit [Finite G] in
private theorem inverted_subgroup_commute
    (u : G) (K : Subgroup G) (hinv : ∀ a ∈ K, u * a * u⁻¹ = a⁻¹)
    {a b : G} (ha : a ∈ K) (hb : b ∈ K) : Commute a b := by
  have hm := (MulAut.conj u).map_mul a b
  change u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) at hm
  rw [hinv _ (K.mul_mem ha hb), hinv a ha, hinv b hb] at hm
  change a * b = b * a
  simpa using congrArg Inv.inv hm

public theorem bender_inverted_subgroup_card [IsSimpleGroup G]
    (normalizerData : BenderNormalizerData h)
    (u : G) (hu : orderOf u = 2) (huH : u ∉ normalizer (h.sylow : Set G))
    (K : Subgroup G) (hKH : K ≤ normalizer (h.sylow : Set G))
    (hinv : ∀ a ∈ K, u * a * u⁻¹ = a⁻¹) :
    Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 6 ∨ Nat.card K = 7 := by
  let H := normalizer (h.sylow : Set G)
  have hd : Nat.card K ∣ 168 := normalizerData.normalizer_card ▸ card_dvd_of_le hKH
  have hn4 : ¬ 4 ∣ Nat.card K := by
    intro hfour
    apply h.bender_normalizer_overlap_not_four_dvd u huH
    apply hfour.trans (card_dvd_of_le (show K ≤ H ⊓ H.comap (MulAut.conj u).toMonoidHom from ?_))
    intro a ha
    exact ⟨hKH ha, by change u * a * u⁻¹ ∈ H; rw [hinv a ha]; exact H.inv_mem (hKH ha)⟩
  by_cases hseven : 7 ∣ Nat.card K
  · let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 7 hseven
    let S := zpowers (x : G)
    have hS : Nat.card S = 7 := by
      rw [Nat.card_zpowers]
      exact (orderOf_injective K.subtype K.subtype_injective x).trans hx
    have hSK : S ≤ K := zpowers_le.mpr x.property
    have huN : u ∈ normalizer (S : Set G) := by
      rw [mem_normalizer_iff_map_conj_eq]
      change (zpowers (x : G)).map (MulAut.conj u).toMonoidHom = zpowers (x : G)
      rw [MonoidHom.map_zpowers]
      change zpowers (u * (x : G) * u⁻¹) = _
      rw [hinv _ x.property, zpowers_inv]
    have hNeven : Even (Nat.card (normalizer (S : Set G))) := by
      rw [even_iff_two_dvd, ← hu, ← Nat.card_zpowers]
      exact card_dvd_of_le (zpowers_le.mpr huN)
    have hCS := normalizerData.seven_centralizer S (hSK.trans hKH) hS hNeven
    have hKS : K ≤ S := by
      rw [← hCS]
      intro a ha
      exact mem_centralizer_iff.mpr (fun b hb =>
        (inverted_subgroup_commute u K hinv (hSK hb) ha).eq)
    exact Or.inr (Or.inr (Or.inr (Or.inr ((le_antisymm hKS hSK) ▸ hS))))
  · have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have he : (168 : ℕ).divisors =
        {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by decide
    rw [he] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega

variable [IsSimpleGroup G]

public theorem bender_inverted_subgroup_of_pairwise_commute
    (normalizerData : BenderNormalizerData h)
    (u : G) (hu : orderOf u = 2) (huH : u ∉ normalizer (h.sylow : Set G))
    (hcomm : ∀ a b : G, a ∈ normalizer (h.sylow : Set G) →
      b ∈ normalizer (h.sylow : Set G) → u * a * u⁻¹ = a⁻¹ →
      u * b * u⁻¹ = b⁻¹ → Commute a b) :
    ∃ K : Subgroup G,
      (∀ a : G, a ∈ K ↔ a ∈ normalizer (h.sylow : Set G) ∧ u * a * u⁻¹ = a⁻¹) ∧
      (Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 6 ∨ Nat.card K = 7) := by
  let H := normalizer (h.sylow : Set G)
  let K : Subgroup G :=
    { carrier := {a | a ∈ H ∧ u * a * u⁻¹ = a⁻¹}
      one_mem' := ⟨H.one_mem, by simp⟩
      mul_mem' := by
        intro a b ha hb
        refine ⟨H.mul_mem ha.1 hb.1, ?_⟩
        calc
          u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) :=
            (MulAut.conj u).map_mul a b
          _ = a⁻¹ * b⁻¹ := by rw [ha.2, hb.2]
          _ = (a * b)⁻¹ := by
            rw [mul_inv_rev]
            exact (hcomm a b ha.1 hb.1 ha.2 hb.2).inv_inv.eq
      inv_mem' := by
        intro a ha
        refine ⟨H.inv_mem ha.1, ?_⟩
        have he := (MulAut.conj u).map_inv a
        change u * a⁻¹ * u⁻¹ = (u * a * u⁻¹)⁻¹ at he
        rwa [ha.2] at he }
  exact ⟨K, fun _ => Iff.rfl,
    h.bender_inverted_subgroup_card normalizerData u hu huH K (fun _ ha => ha.1)
      (fun _ ha => ha.2)⟩

public theorem bender_fiber_sizes_of_pairwise_commute
    (normalizerData : BenderNormalizerData h)
    (hcomm : ∀ u : G, orderOf u = 2 → u ∉ normalizer (h.sylow : Set G) →
      ∀ a b : G, a ∈ normalizer (h.sylow : Set G) →
        b ∈ normalizer (h.sylow : Set G) → u * a * u⁻¹ = a⁻¹ →
        u * b * u⁻¹ = b⁻¹ → Commute a b)
    (ω : G ⧸ normalizer (h.sylow : Set G))
    (hω : ω ≠ benderBaseCoset (normalizer (h.sylow : Set G))) :
    Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 0 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 1 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 2 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 3 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 6 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 7 := by
  let H := normalizer (h.sylow : Set G)
  by_cases hc : Nat.card (BenderFiber H ω) = 0
  · exact Or.inl hc
  obtain ⟨⟨u, hu, huω⟩⟩ := (Nat.card_ne_zero.mp hc).1
  have huH : u ∉ H := by
    intro huH
    exact hω (huω.symm.trans ((benderRightCoset_eq_base_iff H u).mpr huH))
  obtain ⟨K, hK, hcard⟩ := h.bender_inverted_subgroup_of_pairwise_commute
    normalizerData u hu huH (hcomm u hu huH)
  have he := bender_fiber_card_of_inverted_subgroup H u hu huH K hK
  rw [huω] at he
  exact Or.inr (he.symm ▸ hcard)

end CFSG.Quasithin.Janko1CentralizerData
