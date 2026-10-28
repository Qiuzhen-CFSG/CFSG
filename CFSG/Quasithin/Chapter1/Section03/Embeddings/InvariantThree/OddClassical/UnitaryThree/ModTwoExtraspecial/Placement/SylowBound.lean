module

public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
public import CFSG.Quasithin.ChapterA.Section03.RankThreeSylow

/-!
# The Sylow two-order obstruction to primitive solvable unitary groups

Compare the given finite-field Hermitian model with the standard SU₃(p).
Its checked Sylow presentations have order at least sixteen in the
semidihedral case and at least thirty-two in the wreathed case. In particular,
a subgroup containing a full ambient Sylow two-subgroup cannot have Sylow
two-order at most eight.

Source: Aschbacher–Smith A.3.21(b), printed p.55, and the primitive solvable
case of GLS3, proof of Theorem 6.5.3(d).
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterA.Section03

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

theorem eight_lt_special_sylow_card (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hE : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (S : Sylow 2 J.specialSubgroup) : 8 < Nat.card S := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ := Fintype.ofFinite E
  let _ : CharP E p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hE)
  let K := ABG.unitaryForm 3 p 1 (by decide)
  have hK : ∀ x, K.conj x = x ^ p := by
    intro x
    simp only [K, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]
  obtain ⟨e⟩ := J.nonempty_specialEquiv_of_card K p hE
    (J.card_fixed_of_prime_frobenius hc)
    (GaloisField.card p (2 * 1) (by decide))
    (K.card_fixed_of_prime_frobenius hK)
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card T = Nat.card S := card_map_of_injective e.injective
  rw [← hcard]
  rcases su3_sylow_shape p ho T with ⟨n, hn, hT, _⟩ | ⟨n, hn, hT, _⟩
  · rw [hT]
    exact lt_of_lt_of_le (by norm_num : 8 < 2 ^ 4) (Nat.pow_le_pow_right (by decide) hn)
  · rw [hT]
    exact lt_of_lt_of_le (by norm_num : 8 < 2 ^ 5)
      (Nat.pow_le_pow_right (by decide) (by omega))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement
