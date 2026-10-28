module

public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Cubic subgroups in the full symplectic Borel

The explicit diagonal section embeds two copies of a cyclic order-three
subgroup of the field units. In even binary field degree this constructs
an elementary abelian subgroup of order nine in the actual Borel. In odd
degree the Borel order q⁴(q−1)² is prime to three; conjugation transports
this order restriction to any supplied Sylow normalizer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
15.3.49 after (k), printed p.1144. This calculation uses literal cubic
elements, without replacing their generated subgroup by a residual.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
variable {F : Type*} [Field F] [Finite F]

theorem three_not_dvd_card_normalizer {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 ≤ n) (ho : Odd n) (S : Sylow 2 (Sp F)) :
    ¬ 3 ∣ Nat.card (normalizer (S : Set (Sp F))) := by
  rw [Nat.card_congr (sylowNormalizerEquiv hF hn S).toEquiv, card_borel, hF]
  apply Nat.prime_three.not_dvd_mul
  · intro h
    exact (by decide : ¬ 3 ∣ 2)
      (Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h))
  · intro h
    exact (Nat.prime_three.coprime_iff_not_dvd.mp
      (Nat.BinaryTorusParity.coprime_three_sub_one ho)) (Nat.prime_three.dvd_of_dvd_pow h)

theorem exists_cubic_borel_subgroup {n : ℕ} (hF : Nat.card F = 2 ^ n) (he : Even n) :
    ∃ E : Subgroup (borel (F := F)), IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by
    rw [Nat.card_units, hF]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he)
  let C := zpowers u
  have hC : Nat.card C = 3 := (Nat.card_zpowers u).trans hu
  let f : C × C →* borel (F := F) :=
    torusSection.comp (C.subtype.prodMap C.subtype)
  have hf : Function.Injective f := by
    intro x y h
    have he := congrArg borelCharacters h
    simp only [f, MonoidHom.comp_apply, characters_torusSection] at he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
  have hp : ∀ x : C × C, x ^ 3 = 1 := by
    intro x
    apply Prod.ext
    · simpa [hC] using (pow_card_eq_one' (x := x.1))
    · simpa [hC] using (pow_card_eq_one' (x := x.2))
  refine ⟨f.range, ?_, ?_⟩
  · refine { toIsMulCommutative := IsMulCommutative.of_comm ?_, exponent_dvd_p := ?_ }
    · rintro ⟨x, ⟨a, rfl⟩⟩ ⟨y, ⟨b, rfl⟩⟩
      apply Subtype.ext
      change f a * f b = f b * f a
      rw [← map_mul, ← map_mul, mul_comm]
    · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      rintro ⟨x, ⟨a, rfl⟩⟩
      apply Subtype.ext
      change (f a) ^ 3 = 1
      rw [← map_pow, hp a, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_prod, hC]
    norm_num
end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
