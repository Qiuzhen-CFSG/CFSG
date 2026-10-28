module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Frattini

/-!
# Sylow normalizer actions through an outer quotient

If an odd subgroup B normalizes the Sylow intersection S ∩ L, then elements
of N_S(B) in L centralize B: their commutators lie in both disjoint groups.
Thus the actual normalizer action factors through the image in G/L. For a
self-centralizing normal L this quotient embeds in its actual outer group.

An action of order dividing two kills the Frattini subgroup of its actors.
Consequently B = [B, Φ(N_S(B))] with B nontrivial excludes that action order.
These are the kernel and parameter arguments used in Aschbacher--Smith,
`refs/quasithin.pdf`, proof of Proposition 1.3.4, printed pp.510--511.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

def normalizerQuotientMap (L S B : Subgroup G) [L.Normal] :
    (S ⊓ normalizer B : Subgroup G) →* G ⧸ L :=
  (QuotientGroup.mk' L).comp (S ⊓ normalizer B).subtype

theorem normalizerQuotientMap_kernel_centralizes
    (L S B : Subgroup G) [L.Normal]
    (hBn : B ≤ normalizer (S ⊓ L : Subgroup G))
    (hd : Disjoint (S ⊓ L) B)
    (s : (S ⊓ normalizer B : Subgroup G)) (hs : normalizerQuotientMap L S B s = 1) :
    (s : G) ∈ centralizer (B : Set G) := by
  have hsL : (s : G) ∈ L := (QuotientGroup.eq_one_iff _).mp hs
  have hc : (S ⊓ L) ⊓ normalizer B ≤ centralizer (B : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← hd.eq_bot]
    refine le_inf ?_ (le_normalizer_iff_commutator_le_right.mp inf_le_right)
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hBn)
  exact hc ⟨⟨s.property.1, hsL⟩, s.property.2⟩

noncomputable def normalizerAction (S B : Subgroup G) :
    (S ⊓ normalizer B : Subgroup G) →* MulAut B :=
  B.normalizerMonoidHom.comp (inclusion inf_le_right)

theorem normalizerAction_factors_quotient
    (L S B : Subgroup G) [L.Normal]
    (hBn : B ≤ normalizer (S ⊓ L : Subgroup G))
    (hd : Disjoint (S ⊓ L) B) :
    ∃ f : (normalizerQuotientMap L S B).range →* (normalizerAction S B).range,
      Function.Surjective f := by
  let q := normalizerQuotientMap L S B
  let a := normalizerAction S B
  have hk : q.ker ≤ a.rangeRestrict.ker := by
    intro s hs
    apply Subtype.ext
    change a s = 1
    have hc := normalizerQuotientMap_kernel_centralizes L S B hBn hd s hs
    exact show inclusion inf_le_right s ∈ B.normalizerMonoidHom.ker from
      (normalizerMonoidHom_ker B).symm ▸ hc
  let f := QuotientGroup.lift q.ker a.rangeRestrict hk
  let e := QuotientGroup.quotientKerEquivRange q
  refine ⟨f.comp e.symm.toMonoidHom, ?_⟩
  exact (QuotientGroup.lift_surjective_of_surjective q.ker a.rangeRestrict
    a.rangeRestrict_surjective hk).comp e.symm.surjective


theorem normalizerAction_isCyclic_of_quotient
    (L S B : Subgroup G) [L.Normal] [IsCyclic (G ⧸ L)]
    (hBn : B ≤ normalizer (S ⊓ L : Subgroup G))
    (hd : Disjoint (S ⊓ L) B) : IsCyclic (normalizerAction S B).range := by
  obtain ⟨f, hf⟩ := normalizerAction_factors_quotient L S B hBn hd
  exact isCyclic_of_surjective f hf

theorem normalizerAction_card_dvd_quotient
    (L S B : Subgroup G) [L.Normal]
    (hBn : B ≤ normalizer (S ⊓ L : Subgroup G))
    (hd : Disjoint (S ⊓ L) B) : Nat.card (normalizerAction S B).range ∣ Nat.card (G ⧸ L) := by
  obtain ⟨f, hf⟩ := normalizerAction_factors_quotient L S B hBn hd
  exact (Subgroup.card_dvd_of_surjective f hf).trans (card_subgroup_dvd_card _)

theorem normalizerAction_card_dvd_outer
    (L S B : Subgroup G) [L.Normal]
    (hC : centralizer (L : Set G) = ⊥)
    (hBn : B ≤ normalizer (S ⊓ L : Subgroup G))
    (hd : Disjoint (S ⊓ L) B) :
    Nat.card (normalizerAction S B).range ∣ Nat.card (MulAut.Outer L) :=
  (normalizerAction_card_dvd_quotient L S B hBn hd).trans
    (card_dvd_of_injective (MulAut.outerAction L) (MulAut.outerAction_injective L hC))


private theorem frattini_eq_bot_of_card_dvd_two {A : Type*} [Group A] [Finite A]
    (hd : Nat.card A ∣ 2) : frattini A = ⊥ := by
  by_cases ht : Subsingleton A
  · let := ht
    exact Subsingleton.elim _ _
  · let : Nontrivial A := not_subsingleton_iff_nontrivial.mp ht
    have hcard : Nat.card A = 2 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left
      (by have := Finite.one_lt_card (α := A); omega)
    let : Fact (Nat.card A).Prime := ⟨hcard ▸ Nat.prime_two⟩
    rcases (frattini A).eq_bot_or_eq_top_of_prime_card with hb | hh
    · exact hb
    · have he : (⊥ : Subgroup A) = ⊤ := frattini_nongenerating (by simpa using hh)
      exact False.elim (bot_ne_top he)

theorem normalizerAction_frattini_centralizes [Finite G] (S B : Subgroup G)
    (hd : Nat.card (normalizerAction S B).range ∣ 2) :
    (frattini (S ⊓ normalizer B : Subgroup G)).map (S ⊓ normalizer B).subtype ≤
      centralizer (B : Set G) := by
  rintro x ⟨s, hs, rfl⟩
  have h := frattini_le_comap_frattini_of_surjective
    (normalizerAction S B).rangeRestrict_surjective hs
  rw [frattini_eq_bot_of_card_dvd_two hd] at h
  have he : normalizerAction S B s = 1 := congrArg Subtype.val (show
    (normalizerAction S B).rangeRestrict s = 1 from h)
  have hk : inclusion (show S ⊓ normalizer B ≤ normalizer B from inf_le_right) s ∈
      B.normalizerMonoidHom.ker := he
  rw [normalizerMonoidHom_ker] at hk
  exact hk

theorem normalizerAction_card_not_dvd_two [Finite G] (S B : Subgroup G)
    (hne : B ≠ ⊥)
    (hcomm : B = ⁅B, (frattini (S ⊓ normalizer B : Subgroup G)).map
      (S ⊓ normalizer B).subtype⁆) :
    ¬ Nat.card (normalizerAction S B).range ∣ 2 := by
  intro hd
  apply hne
  rw [hcomm, commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr (normalizerAction_frattini_centralizes S B hd)

/-- A nontrivial Frattini commutator action with order dividing 2n forces n even. -/
theorem normalizerAction_even_of_card_dvd_two_mul [Finite G] (S B : Subgroup G)
    (hS : IsPGroup 2 S) (hne : B ≠ ⊥)
    (hcomm : B = ⁅B, (frattini (S ⊓ normalizer B : Subgroup G)).map
      (S ⊓ normalizer B).subtype⁆)
    {n : ℕ} (hcard : Nat.card (normalizerAction S B).range ∣ 2*n) : Even n := by
  by_contra hnodd
  have ho : Odd n := Nat.not_even_iff_odd.mp hnodd
  have hN : IsPGroup 2 (S ⊓ normalizer B : Subgroup G) := hS.to_inf_left
  have ha : IsPGroup 2 (normalizerAction S B).range :=
    hN.of_surjective (normalizerAction S B).rangeRestrict
      (normalizerAction S B).rangeRestrict_surjective
  obtain ⟨k, hk⟩ := ha.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (normalizerAction S B).range) n := by
    rw [hk]
    exact (Nat.coprime_two_left.mpr ho).pow_left k
  exact normalizerAction_card_not_dvd_two S B hne hcomm (hcop.dvd_mul_right.mp hcard)


end Theory.GroupTheory
