module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Basic
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Data.Finite.Perm

/-!
# Prime support from the earlier local quotients

The two alternatives of 15.3.7 give a quotient of `Y` of order nine or
twenty-seven by its intrinsic two-core. With `M=YT`, normalization and
the product-order formula prove that `M` is a {2,3}-group. Independently,
the intrinsic `S₃ × S₃` quotient of 15.3.67(4) gives the same prime support
for `G_E`; conjugating and restricting gives it for `C_G(Eˢ)`.

The residual is the actual `residualY M Mc`, and every quotient uses its
intrinsic core. These conditional consequences supply the prime-support
inputs in the final Thompson argument without assuming them.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7 on p.1122 and 15.3.67–68 on pp.1152–1155.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G] [Finite G]

private theorem prime_eq_two_of_twoGroup (A : Type*) [Group A] [Finite A]
    (hA : IsPGroup 2 A) (p : ℕ) (hp : p.Prime) (hd : p ∣ Nat.card A) : p = 2 := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  rw [hn] at hd
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)

private theorem support_of_core_quotient (A : Type*) [Group A] [Finite A]
    (hq : ∀ p : ℕ, p.Prime → p ∣ Nat.card (A ⧸ pCore 2 A) → p = 2 ∨ p = 3) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card A → p = 2 ∨ p = 3 := by
  intro p hp hd
  rw [← (pCore 2 A).card_mul_index, index_eq_card] at hd
  rcases hp.dvd_mul.mp hd with hc | hq'
  · exact Or.inl (prime_eq_two_of_twoGroup _ pCore_isPGroup p hp hc)
  · exact hq p hp hq'

/-- The order-nine or order-twenty-seven alternatives of 15.3.7, and the
product `M=YT` of 15.3.67(1), imply the prime support required on p.1155.
The residual is the actual `residualY M Mc`. -/
theorem local_prime_support (T : Sylow 2 G) (M Mc : Subgroup G)
    (hM : M = residualY M Mc ⊔ (T : Subgroup G))
    (hN : M ≤ normalizer (residualY M Mc : Set G))
    (hq : Nat.card (residualY M Mc ⧸ pCore 2 (residualY M Mc)) = 9 ∨
      Nat.card (residualY M Mc ⧸ pCore 2 (residualY M Mc)) = 27) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3 := by
  have hY : ∀ p : ℕ, p.Prime → p ∣ Nat.card (residualY M Mc) → p = 2 ∨ p = 3 := by
    apply support_of_core_quotient
    intro p hp hd
    have hthree : p ∣ 3 := by
      rcases hq with h9 | h27
      · rw [h9] at hd
        exact hp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 from hd)
      · rw [h27] at hd
        exact hp.dvd_of_dvd_pow (show p ∣ 3 ^ 3 from hd)
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hthree)
  have hTN : (T : Subgroup G) ≤ normalizer (residualY M Mc : Set G) :=
    (show (T : Subgroup G) ≤ M from hM ▸ le_sup_right).trans hN
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (residualY M Mc)
    (T : Subgroup G) hTN
  rw [← hM] at hc
  intro p hp hd
  have hprod : p ∣ Nat.card (residualY M Mc) * Nat.card (T : Subgroup G) :=
    hd.trans ⟨Nat.card (residualY M Mc ⊓ (T : Subgroup G) : Subgroup G), by
      simpa only [mul_comm] using hc⟩
  rcases hp.dvd_mul.mp hprod with hYp | hTp
  · exact hY p hp hYp
  · exact Or.inl (prime_eq_two_of_twoGroup _ T.isPGroup' p hp hTp)

/-- The actual intrinsic quotient in 15.3.67(4) makes the full line
normalizer a `{2,3}`-group. -/
theorem lineNormalizer_prime_support (E : Subgroup G)
    (hq : Nonempty ((lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (lineNormalizer E) → p = 2 ∨ p = 3 := by
  obtain ⟨e⟩ := hq
  apply support_of_core_quotient
  intro p hp hd
  have hc : Nat.card (lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [hc] at hd
  have hd6 : p ∣ 6 := hp.dvd_of_dvd_pow (show p ∣ 6 ^ 2 from hd)
  rcases hp.dvd_mul.mp (show p ∣ 2 * 3 from hd6) with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)

/-- Conjugating the full line normalizer transports prime support to the
actual ambient centralizer of `F=Eˢ`. -/
theorem otherLine_centralizer_prime_support (E : Subgroup G) (s : G)
    (hq : Nonempty ((lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (centralizer (otherLine E s : Set G)) →
      p = 2 ∨ p = 3 := by
  have he : lineNormalizer (otherLine E s) =
      (lineNormalizer E).map (MulAut.conj s⁻¹).toMonoidHom := by
    rw [map_equiv_normalizer_eq]
    rfl
  intro p hp hd
  have hcard : Nat.card (lineNormalizer (otherLine E s)) = Nat.card (lineNormalizer E) := by
    rw [he, card_map_of_injective (MulAut.conj s⁻¹).injective]
  apply lineNormalizer_prime_support E hq p hp
  rw [← hcard]
  exact hd.trans (card_dvd_of_le (Subgroup.centralizer_le_normalizer _))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
