module

public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.MarkedInvariants
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Large odd primes in binary PSL₃ involution centralizers

Conjugate the actual involution to the root involution. Its centralizer has
order q³(q−1)/3 in even field degree, and the signed-torus calculation supplies
a prime greater than three when the degree is at least four.

Source: Aschbacher–Smith 14.7.26, printed p.1053, and 16.4.8, p.1188.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.EvenInnerCentralizers

theorem exists_prime_gt_three_dvd_involution_centralizer
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 4 ≤ n) (he : Even n)
    (hF : Nat.card F = 2 ^ n) (t : PSL(3,F)) (ht : orderOf t = 2) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      p ∣ Nat.card (Subgroup.centralizer ({t} : Set PSL(3,F))) := by
  have hm : 2 ^ n % 3 = 1 := by
    rw [Nat.BinaryTorusParity.two_pow_mod_three, if_pos (Nat.even_iff.mp he)]
  obtain ⟨_,p,hp,hp3,hd⟩ := Nat.BinarySignedTorus.linear_quotient (by omega) hm
  refine ⟨p,hp,hp3,?_⟩
  have htne : t ≠ 1 := by intro h; simp [h] at ht
  rw [Nat.card_congr (involutionCentralizerEquiv F (by omega) hF t htne
    (ht ▸ pow_orderOf_eq_one t)).toEquiv,
    MarkedInvariants.centralizer_card F hF (by omega) hm]
  exact dvd_mul_of_dvd_right hd _

end Matrix.PSL3.EvenInnerCentralizers
