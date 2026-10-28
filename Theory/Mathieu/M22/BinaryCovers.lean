module

public import Theory.Mathieu.M22.TripleCover.Recognition
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.Representation.Quotient
public import Theory.GroupTheory.PrimeOrderSylowArithmetic

/-!
# Faithful binary covers of M₂₂

A central involution is trivial in a faithful irreducible binary action.
Transfer excludes every remaining prime except three from the center:
the Sylow subgroups for primes other than two and three are cyclic in M₂₂.
The order-nine Sylow theorem bounds the three-primary part of a perfect
central kernel by three. Consequently only M₂₂ and the genuine triple
cover can act faithfully and irreducibly, with no assumption on dimension.

This proves the covering reduction used in Aschbacher–Smith, Chapter K,
printed p.451, for M₂₂. It needs neither the full order-twelve multiplier
calculation nor a small-module classification.
-/

namespace Sporadic.Mathieu.M22BinaryCovers

open Subgroup Theory.GroupTheory PerfectCentralCovering
open Sporadic.Mathieu

private theorem cyclic_sylow (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
    (P : Sylow p M22) : IsCyclic P := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hd : p ∣ Nat.card M22
  · have hdiv : p ∣ 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 := by
      change p ∣ 443520
      rwa [m22_order] at hd
    have hor : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
      rcases hp.dvd_mul.mp hdiv with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · rcases hp.dvd_mul.mp h with h | h
            · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)
            · exact Or.inr (Or.inl ((Nat.dvd_prime Nat.prime_three).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one))
          · exact Or.inr (Or.inr (Or.inl ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp h |>.resolve_left hp.ne_one)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp h |>.resolve_left hp.ne_one))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.dvd_prime (by decide : Nat.Prime 11)).mp h |>.resolve_left hp.ne_one))))
    rcases hor with h | h | rfl | rfl | rfl
    · exact (h2 h).elim
    · exact (h3 h).elim
    · exact isCyclic_of_prime_card (p := 5)
        (P.card_eq_prime_of_dvd_of_not_sq_dvd hd (by rw [m22_order]; norm_num))
    · exact isCyclic_of_prime_card (p := 7)
        (P.card_eq_prime_of_dvd_of_not_sq_dvd hd (by rw [m22_order]; norm_num))
    · exact isCyclic_of_prime_card (p := 11)
        (P.card_eq_prime_of_dvd_of_not_sq_dvd hd (by rw [m22_order]; norm_num))
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have hn0 : n = 0 := by
      by_contra h
      apply hd
      have hpP : p ∣ Nat.card P := by
        rw [hn]
        exact dvd_pow_self p (by omega : n ≠ 0)
      exact hpP.trans P.toSubgroup.card_subgroup_dvd_card
    exact isCyclic_of_card_dvd_prime (p := p) (by rw [hn, hn0, pow_zero]; exact one_dvd p)

/-- The whole center, including all odd covering factors, has order one or three. -/
public theorem center_card_eq_one_or_three_of_binary_irreducible
    {L V : Type*} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) L V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ)
    (e : (L ⧸ center L) ≃* M22) :
    Nat.card (center L) = 1 ∨ Nat.card (center L) = 3 := by
  let f := M22TripleCover.coverOfCentralQuotientEquiv e
  have h2 : ¬ 2 ∣ Nat.card (center L) := by
    intro hd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hd
    let : Representation.IsIrreducible (ρ.comp (⊤ : Subgroup L).subtype) :=
      (Representation.irreducible_comp_surjective_iff _
        (fun x => ⟨⟨x, mem_top x⟩, rfl⟩) ρ).mpr inferInstance
    have hz2 : (z : L) ^ 2 = 1 := by
      exact congrArg Subtype.val (hz ▸ pow_orderOf_eq_one z)
    have hzone := Representation.BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
      ρ ⊤ hf hz2 (fun x _ => (mem_center_iff.mp z.property) x)
    have hz1 : z = 1 := Subtype.ext hzone
    simp [hz1] at hz
  have h3only : ∀ {p : ℕ}, p.Prime → p ∣ Nat.card (center L) → p = 3 := by
    intro p hp hd
    by_contra hn
    have hp2 : p ≠ 2 := fun he => h2 (he ▸ hd)
    let : Fact p.Prime := ⟨hp⟩
    have hcyc : ∀ P : Sylow p M22, IsCyclic P := by
      intro P
      exact cyclic_sylow p hp hp2 hn P
    have hh := f.not_dvd_card_multiplier_of_isCyclic_sylow hcyc
    change ¬ p ∣ Nat.card f.toMonoidHom.ker at hh
    rw [M22TripleCover.coverOfCentralQuotientEquiv_ker] at hh
    exact hh hd
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd
    (Nat.card_pos (α := center L)).ne' h3only
  have hnine := f.not_nine_dvd_card_kernel_of_sylow_nine
    (Classical.choice inferInstance) (M22TripleCover.m22_sylow_three_card _)
  rw [M22TripleCover.coverOfCentralQuotientEquiv_ker] at hnine
  have hk : (Nat.card (center L)).primeFactorsList.length < 2 := by
    by_contra hn
    apply hnine
    change 3 ^ 2 ∣ _
    rw [hpow]
    exact Nat.pow_dvd_pow 3 (Nat.le_of_not_gt hn)
  have hh : (Nat.card (center L)).primeFactorsList.length = 0 ∨
      (Nat.card (center L)).primeFactorsList.length = 1 := by omega
  rcases hh with hh | hh
  · exact Or.inl (by simpa only [hh, pow_zero] using hpow)
  · exact Or.inr (by simpa only [hh, pow_one] using hpow)

/-- The actual quotient marking gives the simple-cover isomorphism when the
center is trivial. -/
public noncomputable def simpleEquiv
    {L : Type*} [Group L] [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* M22) (hc : Nat.card (center L) = 1) : L ≃* M22 :=
  MulEquiv.ofBijective (M22TripleCover.coverOfCentralQuotientEquiv e).toMonoidHom
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
      rw [M22TripleCover.coverOfCentralQuotientEquiv_ker, Subgroup.card_eq_one.mp hc]),
      (M22TripleCover.coverOfCentralQuotientEquiv e).surjective⟩

@[simp] public theorem simpleEquiv_apply
    {L : Type*} [Group L] [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* M22) (hc : Nat.card (center L) = 1) (x : L) :
    simpleEquiv e hc x = e (QuotientGroup.mk' (center L) x) := by
  unfold simpleEquiv
  rfl

/-- Only the simple and genuine triple covers survive a faithful irreducible
binary action. Both alternatives are actual group isomorphisms. -/
public theorem simple_or_triple_of_binary_irreducible
    {L V : Type*} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) L V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (e : (L ⧸ center L) ≃* M22) :
    Nonempty (L ≃* M22) ∨ Nonempty (L ≃* M22TripleCover) := by
  rcases center_card_eq_one_or_three_of_binary_irreducible ρ hf e with h | h
  · exact Or.inl ⟨simpleEquiv e h⟩
  · exact Or.inr (M22TripleCover.nonempty_mulEquiv h ⟨e⟩)

end Sporadic.Mathieu.M22BinaryCovers
