module

public import Theory.SpecificGroups.SymmetricEight.ComponentMarking.PermutationFacts
public import Theory.SpecificGroups.SymmetricEight.ComponentMarking.NormalizerAction
/-!
# Adjoining the component-centralizing involution to A₈

The actual normalizer action sends the involution to a transposition.
The A₆ component supplies the divisor 360 in its centralizer, while
properness and relative subnormality exclude the identity action. The
extension representation has image S₈, since it contains A₈ and a
transposition. The external involution doubles the order of K, so this
surjection is an equivalence.

Source: Aschbacher–Smith, 16.3.11(3) and the setup for 16.3.12,
combined 1 March 2004 manuscript, printed p.1181.
-/

open Subgroup Equiv Equiv.Perm Theory.GroupTheory
@[expose] public noncomputable section
namespace Theory.SpecificGroups.SymmetricEight.ComponentMarking
variable {G : Type*} [Group G] {K L : Subgroup G} {z : G}

theorem normalizerRepresentation_isSwap
    (e : K ≃* alternatingGroup (Fin 8)) (hz : z ∈ normalizer (K : Set G))
    (ho : orderOf z = 2) (hLK : L < K)
    (hL : IsComponentIn L (K ⊓ centralizer ({z} : Set G)))
    (hcardL : Nat.card L = 360) :
    (normalizerRepresentation K e ⟨z, hz⟩).IsSwap := by
  let q := normalizerRepresentation K e ⟨z, hz⟩
  have hq : orderOf q = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      have hs : (⟨z, hz⟩ : normalizer (K : Set G)) ^ 2 = 1 := by
        apply Subtype.ext
        exact ho ▸ pow_orderOf_eq_one z
      rw [hs, map_one]
    · exact normalizerRepresentation_ne_one e hz hLK hL
  let f : L →* Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp (e.toMonoidHom.comp (inclusion hLK.le))
  have hf : Function.Injective f :=
    (alternatingGroup (Fin 8)).subtype_injective.comp
      (e.injective.comp (inclusion_injective hLK.le))
  have hc : f.range ≤ centralizer ({q} : Set (Perm (Fin 8))) := by
    rintro _ ⟨x, rfl⟩
    have hfix : K.normalizerMonoidHom ⟨z, hz⟩ (inclusion hLK.le x) =
        inclusion hLK.le x := by
      apply Subtype.ext
      change z * x.val * z⁻¹ = x.val
      have hcomm := mem_centralizer_singleton_iff.mp (hL.1 x.property).2
      rw [← hcomm]
      simp [mul_assoc]
    have he := normalizerRepresentation_conj K e ⟨z, hz⟩ (inclusion hLK.le x)
    rw [hfix] at he
    exact mem_centralizer_singleton_iff.mpr (eq_mul_inv_iff_mul_eq.mp he)
  apply isSwap_of_centralizer_card q hq
  have hd := card_dvd_of_le hc
  rwa [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, hcardL] at hd

/-- Restriction of the normalizer representation to the actual extension. -/
def extensionRepresentation (e : K ≃* alternatingGroup (Fin 8))
    (hz : z ∈ normalizer (K : Set G)) :
    (K ⊔ zpowers z : Subgroup G) →* Perm (Fin 8) :=
  (normalizerRepresentation K e).comp
    (inclusion (sup_le K.le_normalizer (zpowers_le.mpr hz)))

theorem extensionRepresentation_on_subgroup (e : K ≃* alternatingGroup (Fin 8))
    (hz : z ∈ normalizer (K : Set G)) (x : K) :
    extensionRepresentation e hz ⟨x, mem_sup_left x.property⟩ = e x :=
  normalizerRepresentation_on_subgroup K e x

theorem extensionRepresentation_larger_image (e : K ≃* alternatingGroup (Fin 8))
    (hz : z ∈ normalizer (K : Set G)) :
    (K.subgroupOf (K ⊔ zpowers z)).map (extensionRepresentation e hz) =
      alternatingGroup (Fin 8) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have he := extensionRepresentation_on_subgroup e hz ⟨x.val, hx⟩
    rw [he]
    exact (e ⟨x.val, hx⟩).property
  · intro hy
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
    exact ⟨⟨x, mem_sup_left x.property⟩, x.property,
      (extensionRepresentation_on_subgroup e hz x).trans (congrArg Subtype.val hx)⟩


theorem extensionRepresentation_bijective (e : K ≃* alternatingGroup (Fin 8))
    (hz : z ∈ normalizer (K : Set G)) (ho : orderOf z = 2)
    (hq : (normalizerRepresentation K e ⟨z, hz⟩).IsSwap) :
    Function.Bijective (extensionRepresentation e hz) := by
  let J := K ⊔ zpowers z
  let f := extensionRepresentation e hz
  let zJ : J := ⟨z, mem_sup_right (mem_zpowers z)⟩
  let q := normalizerRepresentation K e ⟨z, hz⟩
  have hfz : f zJ = q := rfl
  have hqout : q ∉ alternatingGroup (Fin 8) := by
    rw [mem_alternatingGroup, hq.sign_eq]
    decide
  have hzout : z ∉ K := by
    intro hzK
    have he := extensionRepresentation_on_subgroup e hz ⟨z, hzK⟩
    have hmem := (e ⟨z, hzK⟩).property
    rw [← he] at hmem
    exact hqout hmem
  have hcardK : Nat.card K = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hcardJ : Nat.card J = 40320 := by
    rw [card_sup_zpowers_of_normalizing_involution K z (ho ▸ pow_orderOf_eq_one z)
      hzout hz, hcardK]
  let : Finite J := Nat.finite_of_card_ne_zero (by rw [hcardJ]; decide)
  apply (Nat.bijective_iff_surjective_and_card f).mpr
  refine ⟨?_, ?_⟩
  · have heven (a : Perm (Fin 8)) (ha : a ∈ alternatingGroup (Fin 8)) :
        ∃ x : J, f x = a := by
      obtain ⟨x, hx⟩ := e.surjective ⟨a, ha⟩
      exact ⟨⟨x, mem_sup_left x.property⟩,
        (extensionRepresentation_on_subgroup e hz x).trans (congrArg Subtype.val hx)⟩
    intro a
    by_cases ha : a ∈ alternatingGroup (Fin 8)
    · exact heven a ha
    · have hprod : a * q⁻¹ ∈ alternatingGroup (Fin 8) := by
        rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two, inv_mem_iff]
        exact iff_of_false ha hqout
      obtain ⟨x, hx⟩ := heven _ hprod
      refine ⟨x * zJ, ?_⟩
      rw [map_mul, hx, hfz]
      simp
  · rw [hcardJ, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]

end Theory.SpecificGroups.SymmetricEight.ComponentMarking
