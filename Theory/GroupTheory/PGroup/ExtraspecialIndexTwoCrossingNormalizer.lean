module

public import Theory.GroupTheory.PGroup.ExtraspecialIndexTwoElementaryNormalizer
public import Theory.GroupAction.ElementaryEightInvolution
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.PGroup.CyclicCenterIndexFourElementary

/-!
# Normalizers of elementary eights crossing an extraspecial core

Let a group of order sixty-four have an extraspecial subgroup of order
thirty-two and index two, and no normal elementary abelian subgroup of order
at least eight. Every elementary eight crossing the core has normalizer of
order thirty-two.

Its intersection with the core is a normal four containing the core center.
The core modulo this intersection is therefore elementary abelian of order
eight. An outside involution in the eight fixes at least four quotient
elements. Their preimage has order at least sixteen and normalizes the eight:
it normalizes the intersection, and its commutator with the outside
involution belongs to that intersection. The normalizer crosses the core,
doubling this lower bound; the absence of normal eights gives the upper bound.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389,
the index-two paragraph, in
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open scoped IsMulCommutative
namespace Subgroup
universe u

private theorem elementary_quotient_of_center_le
    {H : Type*} [Group H] [IsExtraspecial 2 H]
    (K : Subgroup H) [K.Normal] (hZ : center H ≤ K) :
    IsElementaryAbelian 2 (H ⧸ K) := by
  have hs (x : H ⧸ K) : x ^ 2 = 1 := by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (hZ ((IsExtraspecial.quotient_elementary_abelian 2 H).sq_mem_center_of_central_quotient y))
  have hi (x : H ⧸ K) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using hs x
  exact {
    toIsMulCommutative := isMulCommutative_iff.mpr (fun x y => by
      calc x * y = (x * y)⁻¹ := (hi _).symm
           _ = y * x := by rw [mul_inv_rev, hi, hi])
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

private theorem fixed_card_ge_four
    {T V : Type u} [Group T] [Group V] [Finite T] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction T V]
    (t : T) (ht : t ≠ 1 ∧ t ^ 2 = 1) (hT : Nat.card T = 2)
    (hV : Nat.card V = 8) : 4 ≤ Nat.card (FixedPoints.subgroup T V) := by
  by_cases hm : ∃ v : V, t • v ≠ v
  · exact (fixed_subgroup_card_four_of_nontrivial_involution_on_eight t ht hT hV hm).ge
  · push Not at hm
    have htop : FixedPoints.subgroup T V = ⊤ := by
      apply top_unique
      intro v _ a
      by_cases ha : a = 1
      · simp [ha]
      · obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : T)).mp hT
        rw [(hz a ha).trans (hz t ht.1).symm]
        exact hm v
    rw [htop, card_top, hV]
    decide

/-- A crossing elementary eight has normalizer of order thirty-two in an
index-two extraspecial extension of order sixty-four with no normal eight. -/
public theorem card_normalizer_eq_thirty_two_of_elementary_eight_crossing_extraspecial
    {P : Type*} [Group P] [Finite P] (hP : Nat.card P = 64)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (H : Subgroup P) [IsExtraspecial 2 H] (hH : Nat.card H = 32) (hi : H.index = 2)
    (F : Subgroup P) [IsElementaryAbelian 2 F] (hF : Nat.card F = 8)
    (hout : ¬ F ≤ H) : Nat.card (normalizer (F : Set P)) = 32 := by
  classical
  let : H.Normal := H.normal_of_index_eq_two hi
  obtain ⟨hIn, _hIe, hIc, hZF⟩ :=
    elementary_eight_crossing_extraspecial_intersection hno H hi F hF hout
  let I := H ⊓ F
  change Nat.card I = 4 at hIc
  let : I.Normal := hIn
  let K := I.subgroupOf H
  let : K.Normal := inferInstance
  have hK : Nat.card K = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show I ≤ H from inf_le_left)).toEquiv).trans hIc
  have hZK : center H ≤ K := by
    intro z hz
    exact ⟨z.property, hZF (mem_map_of_mem H.subtype hz)⟩
  let V := H ⧸ K
  let q : H →* V := QuotientGroup.mk' K
  let : IsElementaryAbelian 2 V := elementary_quotient_of_center_le K hZK
  have hV : Nat.card V = 8 := by
    have hc := card_eq_card_quotient_mul_card_subgroup K
    rw [hK, hH] at hc
    change 32 = Nat.card V * 4 at hc
    omega
  obtain ⟨t, htF, htH⟩ : ∃ t : P, t ∈ F ∧ t ∉ H := by
    by_contra! h
    exact hout h
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htF
  have htne : t ≠ 1 := fun hh => htH (hh ▸ H.one_mem)
  let T := zpowers t
  let a : T := ⟨t, mem_zpowers t⟩
  have ha : a ≠ 1 ∧ a ^ 2 = 1 :=
    ⟨fun hh => htne (congrArg Subtype.val hh), Subtype.ext ht2⟩
  have hT : Nat.card T = 2 := (Nat.card_zpowers t).trans (orderOf_eq_prime ht2 htne)
  have hTH : T ≤ normalizer (H : Set P) := le_normalizer_of_normal
  have hTI : T ≤ normalizer (I : Set P) := le_normalizer_of_normal
  obtain ⟨ρ, hρ⟩ := exists_quotient_conjugation_action T H I hTH hTI
    (show (I.subgroupOf H).Normal from inferInstance)
  let : MulDistribMulAction T V := MulDistribMulAction.compHom V ρ
  let C := FixedPoints.subgroup T V
  have hC : 4 ≤ Nat.card C := fixed_card_ge_four a ha hT hV
  let B := C.comap q
  have hBi : B.index ≤ 2 := by
    rw [index_comap_of_surjective _ (QuotientGroup.mk'_surjective K)]
    have hc := C.card_mul_index
    rw [hV] at hc
    nlinarith
  have hB : 16 ≤ Nat.card B := by
    have hc := B.card_mul_index
    rw [hH] at hc
    nlinarith
  have hgen : I ⊔ T = F := by
    have hle : I ⊔ T ≤ F := sup_le inf_le_right (zpowers_le.mpr htF)
    have hgt : 4 < Nat.card (I ⊔ T : Subgroup P) := by
      have hge := card_le_of_le (show I ≤ I ⊔ T from le_sup_left)
      have hne : Nat.card (I ⊔ T : Subgroup P) ≠ 4 := by
        intro hh
        have heq : I = I ⊔ T := eq_of_le_of_card_ge le_sup_left (by omega)
        have htI : t ∈ I := heq ▸ ((le_sup_right : T ≤ I ⊔ T) (mem_zpowers t) : t ∈ I ⊔ T)
        exact htH htI.1
      omega
    apply eq_of_le_of_card_ge hle
    have hd := card_dvd_of_le hle
    rw [hF] at hd ⊢
    have hd' := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have hd8 : (8 : ℕ).divisors = {1, 2, 4, 8} := by decide
    rw [hd8] at hd'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd'
    omega
  have hBN : B.map H.subtype ≤ normalizer (F : Set P) := by
    apply subgroup_le_normalizer_of_conj_mem
    intro b f hf
    obtain ⟨x, hx, hxb⟩ := b.property
    have hfix : ρ a (q x) = q x := (show q x ∈ C from hx) a
    rw [hρ] at hfix
    have hc : t * (x : P) * t⁻¹ * (x : P)⁻¹ ∈ I := by
      have hh := QuotientGroup.eq_iff_div_mem.mp hfix
      change t * (x : P) * t⁻¹ / (x : P) ∈ I at hh
      simpa only [div_eq_mul_inv] using hh
    have hxt : (x : P) * t * (x : P)⁻¹ ∈ F := by
      have hh := F.mul_mem (show (t * (x : P) * t⁻¹ * (x : P)⁻¹)⁻¹ ∈ F from
        (I.inv_mem hc).2) htF
      convert hh using 1
      group
    have hmap : F.map (MulAut.conj (x : P)).toMonoidHom ≤ F := by
      nth_rw 1 [← hgen]
      rw [map_sup]
      apply sup_le
      · rintro _ ⟨i, hiI, rfl⟩
        exact ((show I.Normal from inferInstance).conj_mem i hiI (x : P)).2
      · change (zpowers t).map _ ≤ F
        rw [MonoidHom.map_zpowers]
        exact zpowers_le.mpr hxt
    have hf' := hmap (mem_map_of_mem (MulAut.conj (x : P)).toMonoidHom hf)
    change (x : P) * f * (x : P)⁻¹ ∈ F at hf'
    have hxb' : (x : P) = (b : P) := hxb
    rwa [hxb'] at hf'
  have hcore : 16 ≤ Nat.card (H.subgroupOf (normalizer (F : Set P))) := by
    have hle : B.map H.subtype ≤ H ⊓ normalizer (F : Set P) :=
      le_inf (map_subtype_le B) hBN
    have hc := card_le_of_le hle
    rw [card_map_of_injective H.subtype_injective] at hc
    have heq : Nat.card (H ⊓ normalizer (F : Set P) : Subgroup P) =
        Nat.card (H.subgroupOf (normalizer (F : Set P))) := by
      rw [← subgroupOf_map_subtype H (normalizer (F : Set P)),
        card_map_of_injective (normalizer (F : Set P)).subtype_injective]
    omega
  apply Nat.le_antisymm (card_normalizer_le_thirty_two_of_no_normal_eight hP hno F hF)
  rw [card_normalizer_eq_two_mul_core_intersection H F hi hout]
  omega
end Subgroup
