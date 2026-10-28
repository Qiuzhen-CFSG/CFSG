module

public import CFSG.Quasithin.Chapter6.SourceDefs
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The binary field parameter of an actual alternating-five actor

An identification of the literal actor with both PSL₂(2ⁿ) and A₅ forces
n = 2. In characteristic two PSL₂ has order q(q² - 1); comparison with
|A₅| = 60 determines q. Thus the module exit needs no separate numerical
assumption and uses the same field convention as `ClassicalGroup.IsPSL`.

Source: Aschbacher--Smith, 6.2.20(1) and 12.2.2(3d), pp.691 and 795.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source
variable {A : Type*} [Group A] {n : ℕ}

/-- The two concrete actor identifications determine the binary exponent. -/
theorem exponent_eq_two_of_psl_and_a5 (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL A 2 (2 ^ n))
    (e : A ≃* alternatingGroup (Fin 5)) : n = 2 := by
  obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hc : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 60 := by
    rw [← Nat.card_congr f.toEquiv, Nat.card_congr e.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have ho := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1), mul_one, hc, hF] at ho
  have hlow : 4 ≤ 2 ^ n := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ n by omega)
  have hq : 2 ^ n = 4 := by
    by_contra hne
    have hlarge : 5 ≤ 2 ^ n := by omega
    have hslarge : 24 ≤ (2 ^ n) ^ 2 - 1 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_left hlarge 2) 1
    have hprod := Nat.mul_le_mul hlarge hslarge
    omega
  exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) (by simpa using hq)

end CFSG.Quasithin.Chapter6.Source
