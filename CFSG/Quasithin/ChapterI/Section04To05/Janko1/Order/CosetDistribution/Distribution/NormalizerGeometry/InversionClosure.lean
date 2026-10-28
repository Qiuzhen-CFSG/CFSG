module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.NormalizerGeometry.InvertedOrders
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.NormalizerGeometry.LocalStructure
public import Theory.SpecificGroups.Frobenius21.Recognition

/-!
# Closure of Bender's literal inversion sets

Let H be the normalizer of the elementary Sylow eight-group. The overlap
H ∩ Hᵘ has order indivisible by four. An even subgroup of this overlap has
its unique involution in the normal Sylow subgroup, so that involution is
central. Its centralizer has order 120, restricting the overlap order to
two or six. The remaining overlap orders are one, three, seven and 21.

All cases except the nonabelian group of order 21 are abelian. For that
case, the actual Frobenius-group recognition isomorphism transports the
restricted conjugation map to the concrete model. The defining relation
between its seven- and three-generators forces every injective endomorphism
to fix the quotient of order three. Inverted elements therefore lie in the
cyclic seven-kernel and commute. The finite model certificates below check
only generator images and normal forms, not an enumeration of automorphisms.

This proves closure of the literal inversion set and feeds the existing
subgroup-order and right-coset-fiber theorems. The prime-counting record is
retained as an explicit input of the chapter interface; the commutation
argument uses only the centralizer data and normalizer data.

Source: Bender, *Finite groups with large subgroups* (1974), §4, printed
p.226, the paragraph following the proof of (4.3).
-/

namespace CFSG.Quasithin.Janko1CentralizerData.InversionClosure
open Frobenius21
private def kernelGenerator : Model := SemidirectProduct.inl (Multiplicative.ofAdd 1)
private def complementGenerator : Model := SemidirectProduct.inr (Multiplicative.ofAdd 1)

private theorem generator_relations :
    kernelGenerator ≠ 1 ∧ kernelGenerator ^ 7 = 1 ∧
      complementGenerator * kernelGenerator * complementGenerator⁻¹ = kernelGenerator ^ 2 := by
  decide +kernel

private theorem generator_images : ∀ x y : Model,
    x ≠ 1 → x ^ 7 = 1 → y * x * y⁻¹ = x ^ 2 →
      x.right = 1 ∧ y.right = Multiplicative.ofAdd 1 := by
  decide +kernel

private theorem normal_form : ∀ x : Model,
    x = kernelGenerator ^ x.left.toAdd.val * complementGenerator ^ x.right.toAdd.val := by
  decide +kernel

private theorem preserves_right (f : Model →* Model) (hf : Function.Injective f) (x : Model) :
    (f x).right = x.right := by
  have hg := generator_relations
  have hi := generator_images (f kernelGenerator) (f complementGenerator)
    (fun he => hg.1 (hf (he.trans (map_one f).symm)))
    (by rw [← map_pow, hg.2.1, map_one])
    (by rw [← map_inv, ← map_mul, ← map_mul, hg.2.2, map_pow])
  let r : Model →* Complement := SemidirectProduct.rightHom
  change r (f x) = x.right
  conv_lhs => rw [normal_form x, map_mul, map_pow, map_pow, map_mul, map_pow, map_pow]
  change (f kernelGenerator).right ^ x.left.toAdd.val *
    (f complementGenerator).right ^ x.right.toAdd.val = x.right
  rw [hi.1, hi.2, one_pow, one_mul]
  change x.right.toAdd.val • (1 : ZMod 3) = x.right.toAdd
  simp

private theorem inverted_mem_kernel (f : Model →* Model) (hf : Function.Injective f)
    (x : Model) (hx : f x = x⁻¹) : x.right = 1 := by
  have hr := preserves_right f hf x
  rw [hx, SemidirectProduct.inv_right] at hr
  exact (by decide +kernel : ∀ a : Complement, a⁻¹ = a → a = 1) x.right hr

private theorem model_inverted_commute (f : Model →* Model) (hf : Function.Injective f)
    (x y : Model) (hx : f x = x⁻¹) (hy : f y = y⁻¹) : Commute x y := by
  have hxk := inverted_mem_kernel f hf x hx
  have hyk := inverted_mem_kernel f hf y hy
  change x * y = y * x
  apply SemidirectProduct.ext
  · simp [SemidirectProduct.mul_left, hxk, hyk, mul_comm]
  · simp [SemidirectProduct.mul_right, mul_comm]

private theorem inverted_commute_of_card_twenty_one
    {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 21)
    (f : K →* K) (hf : Function.Injective f)
    (a b : K) (ha : f a = a⁻¹) (hb : f b = b⁻¹) : Commute a b := by
  classical
  by_cases hc : ∀ x y : K, x * y = y * x
  · exact hc a b
  obtain ⟨e⟩ := Frobenius21.nonempty_mulEquiv_of_card_eq hK hc
  let f' : Model →* Model := e.toMonoidHom.comp (f.comp e.symm.toMonoidHom)
  have hf' : Function.Injective f' := e.injective.comp (hf.comp e.symm.injective)
  have hi (x : K) (hx : f x = x⁻¹) : f' (e x) = (e x)⁻¹ := by
    change e (f (e.symm (e x))) = (e x)⁻¹
    rw [e.symm_apply_apply, hx, map_inv]
  have hm := model_inverted_commute f' hf' (e a) (e b) (hi a ha) (hi b hb)
  apply e.injective
  simpa only [map_mul] using hm.eq
end CFSG.Quasithin.Janko1CentralizerData.InversionClosure

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G) [IsSimpleGroup G]

private theorem even_subgroup_card
    (normalizerData : BenderNormalizerData h)
    (S : Subgroup G) (hSH : S ≤ normalizer (h.sylow : Set G))
    (hn4 : ¬ 4 ∣ Nat.card S) (htwo : 2 ∣ Nat.card S) :
    Nat.card S = 2 ∨ Nat.card S = 6 := by
  classical
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 htwo
  have htG : orderOf (t : G) = 2 :=
    (orderOf_injective S.subtype S.subtype_injective t).trans ht
  have htQ := h.normalizer_involution_mem_sylow t htG (hSH t.property)
  let I := S ⊓ (h.sylow : Subgroup G)
  have hzle : zpowers (t : G) ≤ I := zpowers_le.mpr ⟨t.property, htQ⟩
  have hI : Nat.card I = 2 := by
    have hd : Nat.card I ∣ 8 := h.sylow_card ▸
      card_dvd_of_le (show I ≤ (h.sylow : Subgroup G) from inf_le_right)
    have hn : ¬ 4 ∣ Nat.card I := fun hh =>
      hn4 (hh.trans (card_dvd_of_le (show I ≤ S from inf_le_left)))
    have htwoI : 2 ∣ Nat.card I := by
      simpa [Nat.card_zpowers, htG] using card_dvd_of_le hzle
    have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have he : (8 : ℕ).divisors = {1, 2, 4, 8} := by decide
    rw [he] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  have hIz : I = zpowers (t : G) := (eq_of_le_of_card_ge hzle (by
    rw [hI, Nat.card_zpowers, htG])).symm
  have hSC : S ≤ centralizer ({(t : G)} : Set G) := by
    intro x hx
    have hconjI : x * t * x⁻¹ ∈ I :=
      ⟨S.mul_mem (S.mul_mem hx t.property) (S.inv_mem hx),
        (mem_normalizer_iff.mp (hSH hx) _).mp htQ⟩
    have hconjNe : x * t * x⁻¹ ≠ 1 := by
      intro he
      have ht1 : (t : G) = 1 := (MulAut.conj x).injective (he.trans (map_one _).symm)
      rw [ht1, orderOf_one] at htG
      omega
    rw [hIz, mem_zpowers_iff_mem_range_orderOf, htG] at hconjI
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hconjI
    have hnlt := Finset.mem_range.mp hn
    have hfix : x * t * x⁻¹ = t := by
      interval_cases n
      · exact (hconjNe (by simpa using he.symm)).elim
      · simpa using he.symm
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)
  have hd : Nat.card S ∣ 24 := by
    have hg := Nat.dvd_gcd (card_dvd_of_le hSH) (card_dvd_of_le hSC)
    simpa [normalizerData.normalizer_card, h.involution_centralizer_card t htG] using hg
  have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have he : (24 : ℕ).divisors = {1, 2, 3, 4, 6, 8, 12, 24} := by decide
  rw [he] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

private theorem overlap_card
    (normalizerData : BenderNormalizerData h)
    (u : G) (huH : u ∉ normalizer (h.sylow : Set G)) :
    let I := normalizer (h.sylow : Set G) ⊓
      (normalizer (h.sylow : Set G)).comap (MulAut.conj u).toMonoidHom
    Nat.card I = 1 ∨ Nat.card I = 2 ∨ Nat.card I = 3 ∨
      Nat.card I = 6 ∨ Nat.card I = 7 ∨ Nat.card I = 21 := by
  let I := normalizer (h.sylow : Set G) ⊓
    (normalizer (h.sylow : Set G)).comap (MulAut.conj u).toMonoidHom
  have hn := h.bender_normalizer_overlap_not_four_dvd u huH
  have hIH : I ≤ normalizer (h.sylow : Set G) := inf_le_left
  have hd : Nat.card I ∣ 168 := normalizerData.normalizer_card ▸ card_dvd_of_le hIH
  by_cases htwo : 2 ∣ Nat.card I
  · rcases even_subgroup_card h normalizerData I hIH hn htwo with he | he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
  · have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have he : (168 : ℕ).divisors =
        {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by decide
    rw [he] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    change Nat.card I = 1 ∨ Nat.card I = 2 ∨ Nat.card I = 3 ∨
      Nat.card I = 6 ∨ Nat.card I = 7 ∨ Nat.card I = 21
    omega

/-- Elements of the Sylow normalizer inverted by one outside involution commute. -/
public theorem bender_inverted_elements_commute {d : ℕ}
    (_localData : BenderPrimeData G d)
    (normalizerData : BenderNormalizerData h)
    (u : G) (hu : orderOf u = 2) (huH : u ∉ normalizer (h.sylow : Set G))
    (a b : G) (haH : a ∈ normalizer (h.sylow : Set G))
    (hbH : b ∈ normalizer (h.sylow : Set G))
    (ha : u * a * u⁻¹ = a⁻¹) (hb : u * b * u⁻¹ = b⁻¹) : Commute a b := by
  classical
  let H := normalizer (h.sylow : Set G)
  let I := H ⊓ H.comap (MulAut.conj u).toMonoidHom
  have haI : a ∈ I := ⟨haH, by change u * a * u⁻¹ ∈ H; rw [ha]; exact H.inv_mem haH⟩
  have hbI : b ∈ I := ⟨hbH, by change u * b * u⁻¹ ∈ H; rw [hb]; exact H.inv_mem hbH⟩
  let aI : I := ⟨a, haI⟩
  let bI : I := ⟨b, hbI⟩
  suffices hh : Commute aI bI from congrArg Subtype.val hh.eq
  have cyclic_case (hc : IsCyclic I) : Commute aI bI := by
    let _ := hc
    exact IsMulCommutative.is_comm.comm aI bI
  rcases overlap_card h normalizerData u huH with h1 | h2 | h3 | h6 | h7 | h21
  · have : Subsingleton I := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  · exact cyclic_case (isCyclic_of_prime_card h2)
  · let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact cyclic_case (isCyclic_of_prime_card h3)
  · exact cyclic_case (h.bender_six_cyclic I inf_le_left h6)
  · let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact cyclic_case (isCyclic_of_prime_card h7)
  · have hu2 : u * u = 1 := by simpa only [← pow_two, hu] using pow_orderOf_eq_one u
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
    have hconj2 (x : G) : (MulAut.conj u) ((MulAut.conj u) x) = x := by
      change u * (u * x * u⁻¹) * u⁻¹ = x
      rw [hui]
      calc
        u * (u * x * u) * u = (u * u) * x * (u * u) := by group
        _ = x := by rw [hu2]; simp
    let f : I →* I :=
      { toFun x := ⟨(MulAut.conj u) x, x.property.2, by
          change (MulAut.conj u) ((MulAut.conj u) x) ∈ H
          rw [hconj2]
          exact x.property.1⟩
        map_one' := Subtype.ext (map_one (MulAut.conj u))
        map_mul' x y := Subtype.ext (map_mul (MulAut.conj u) (x : G) (y : G)) }
    have hf : Function.Injective f := by
      intro x y he
      exact Subtype.ext ((MulAut.conj u).injective (congrArg Subtype.val he))
    exact InversionClosure.inverted_commute_of_card_twenty_one h21 f hf aI bI
      (Subtype.ext ha) (Subtype.ext hb)

/-- The literal inversion set is a subgroup with the source order alternatives. -/
public theorem bender_inverted_subgroup {d : ℕ}
    (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h)
    (u : G) (hu : orderOf u = 2) (huH : u ∉ normalizer (h.sylow : Set G)) :
    ∃ K : Subgroup G,
      (∀ a : G, a ∈ K ↔ a ∈ normalizer (h.sylow : Set G) ∧ u * a * u⁻¹ = a⁻¹) ∧
      (Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 6 ∨ Nat.card K = 7) :=
  h.bender_inverted_subgroup_of_pairwise_commute normalizerData u hu huH
    (h.bender_inverted_elements_commute localData normalizerData u hu huH)

/-- Applying closure to the actual non-base right-coset involution fibers. -/
public theorem bender_fiber_sizes_of_inversion_closure {d : ℕ}
    (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h)
    (ω : G ⧸ normalizer (h.sylow : Set G))
    (hω : ω ≠ benderBaseCoset (normalizer (h.sylow : Set G))) :
    Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 0 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 1 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 2 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 3 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 6 ∨
      Nat.card (BenderFiber (normalizer (h.sylow : Set G)) ω) = 7 :=
  h.bender_fiber_sizes_of_pairwise_commute normalizerData
    (h.bender_inverted_elements_commute localData normalizerData) ω hω

end CFSG.Quasithin.Janko1CentralizerData
