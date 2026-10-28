module

public import CFSG.Quasithin.ChapterH.Section10To12.Defs
public import Theory.GroupTheory.CentralCoprimePrimeLift
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Eleven-by-five subgroups through a central cubic kernel

The prime-subgroup lifting theorem gives an actual subgroup of order eleven
and identifies its normalizer with the inverse image of the native normalizer.
Injectivity on the eleven- and five-subgroups transfers the fixed-point-free
conjugation action. Their normalized product has order 55.

The triple-M₂₂ adapter uses the genuine central quotient from `IsTripleM22`.
Its native M₂₂ Frobenius calculation remains an explicit premise; this module
does not claim that model calculation or the unconditional H.12.1 witnesses.

Source: Aschbacher–Smith H.12.1, printed p.394 (combined 1 March 2004
manuscript), the Frobenius subgroup used for the order-five displacement bound.
-/

public section

open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.AmbientActors

/-- Lift an actual eleven-by-five Frobenius configuration through a central cubic kernel. -/
theorem lift_eleven_five {E B : Type*} [Group E] [Finite E] [Group B]
    (f : E →* B) (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (hk : Nat.card f.ker = 3) (y : E) (hy : orderOf y = 5)
    (K : Subgroup B) (hK : Nat.card K = 11)
    (hn : zpowers (f y) ≤ normalizer (K : Set B))
    (hfree : ∀ a ∈ zpowers (f y), a ≠ 1 →
      ∀ k ∈ K, a * k * a⁻¹ = k → k = 1) :
    ∃ A : Subgroup E, Nat.card A = 11 ∧
      zpowers y ≤ normalizer (A : Set E) ∧
      (∀ a ∈ zpowers y, a ≠ 1 → ∀ k ∈ A, a * k * a⁻¹ = k → k = 1) ∧
      Nat.card (A ⊔ zpowers y : Subgroup E) = 55 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  have hkp : IsPGroup 11 K := IsPGroup.of_card (n := 1) (by simpa using hK)
  obtain ⟨A, hA, hmap, hnorm, _, hi⟩ :=
    exists_prime_lift_of_central_coprime f hf hc (by rw [hk]; decide : Nat.Coprime 11 (Nat.card f.ker)) K hkp
  have hAc : Nat.card A = 11 := by
    have hfi : Function.Injective (f.subgroupMap A) := by
      intro x z h
      exact hi (congrArg Subtype.val h)
    have hcard := Nat.card_congr (Equiv.ofBijective (f.subgroupMap A)
      ⟨hfi, f.subgroupMap_surjective A⟩)
    rw [hmap, hK] at hcard
    exact hcard
  have hnA : zpowers y ≤ normalizer (A : Set E) := by
    rw [← hnorm]
    apply zpowers_le.mpr
    exact hn (mem_zpowers (f y))
  have hY : IsPGroup 5 (zpowers y) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, hy] using (show (5 : ℕ) = 5 ^ 1 by decide))
  have hiY : Function.Injective (f.comp (zpowers y).subtype) :=
    injective_comp_subtype_of_coprime_ker f (by rw [hk]; decide : Nat.Coprime 5 (Nat.card f.ker)) (zpowers y) hY
  have hfr : ∀ a ∈ zpowers y, a ≠ 1 → ∀ k ∈ A, a * k * a⁻¹ = k → k = 1 := by
    intro a ha ha1 k hka heq
    have hfa : f a ∈ zpowers (f y) := by
      rw [← MonoidHom.map_zpowers]
      exact mem_map_of_mem f ha
    have hfa1 : f a ≠ 1 := by
      intro h
      exact ha1 (congrArg Subtype.val (hiY (show (f.comp (zpowers y).subtype) ⟨a, ha⟩ = (f.comp (zpowers y).subtype) 1 by simpa using h)))
    have hfk : f k ∈ K := hmap ▸ mem_map_of_mem f hka
    have hk1 := hfree (f a) hfa hfa1 (f k) hfk (by
      simpa only [map_mul, map_inv] using congrArg f heq)
    exact congrArg Subtype.val (hi (show (f.comp A.subtype) ⟨k, hka⟩ = (f.comp A.subtype) 1 by simpa using hk1))
  have hdis : Disjoint A (zpowers y) := disjoint_of_coprime_natCard (by
    rw [hAc, Nat.card_zpowers, hy]
    decide)
  refine ⟨A, hAc, hnA, hfr, ?_⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint A (zpowers y) hnA hdis,
    hAc, Nat.card_zpowers, hy]


/-- The exact order-55 subgroup for each cubic-cover element of order five,
conditional only on the native M₂₂ normalizer calculation. -/
theorem exists_eleven_five_of_model
    (hmodel : ∀ v : M22, orderOf v = 5 → ∃ K : Subgroup M22,
      Nat.card K = 11 ∧ zpowers v ≤ normalizer (K : Set M22) ∧
      ∀ a ∈ zpowers v, a ≠ 1 → ∀ k ∈ K, a * k * a⁻¹ = k → k = 1)
    {L : Type*} [Group L] [Finite L] (hL : IsTripleM22 L)
    (y : L) (hy : orderOf y = 5) :
    ∃ K : Subgroup L, Nat.card K = 11 ∧
      zpowers y ≤ normalizer (K : Set L) ∧
      (∀ a ∈ zpowers y, a ≠ 1 → ∀ k ∈ K, a * k * a⁻¹ = k → k = 1) ∧
      Nat.card (K ⊔ zpowers y : Subgroup L) = 55 := by
  obtain ⟨e⟩ := hL.centralQuotient
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hker : f.ker = center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hcard : Nat.card f.ker = 3 := hker ▸ hL.center_card
  have hkp : IsPGroup 3 f.ker := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hfy : orderOf (f y) = 5 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hkp y (by rw [hy]; decide)).trans hy
  obtain ⟨K, hK, hn, hfree⟩ := hmodel (f y) hfy
  exact lift_eleven_five f (e.surjective.comp (QuotientGroup.mk'_surjective _))
    hker.le hcard y hy K hK hn hfree

end CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.AmbientActors
