module
public import Theory.GroupTheory.DihedralSixteenProducts
public import GorensteinWalter.PSL2DihedralSylow
import Mathlib.Tactic

/-!
# Four-group centralizer products in PSL₂(17)

The actual group has order 2448, so its dihedral Sylow two-subgroups have
order sixteen. The dihedral four-group calculation supplies a centralizing
conjugator and a product conjugate to the square of any order-eight actor.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript p.9; Aschbacher--Smith K.2, printed p.453.
-/

public section
namespace Theory.PSL2.SeventeenGeometry
open Subgroup GorensteinWalter
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The precise dihedral order in the prime-field model. -/
theorem sylow_equiv_dihedral_sixteen
    (S : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 17))) :
    Nonempty (S ≃* DihedralGroup 8) := by
  let hK : IsOddPrimePower (Nat.card (ZMod 17)) :=
    ⟨17, 1, by decide, by decide, by decide, by simp⟩
  have hcard : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 17)) =
      2448 := by
    rw [psl2_card_formula _ hK]
    norm_num
  have hS : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity, hcard,
      show (2448 : ℕ).factorization 2 = 4 by
        rw [show 2448 = 2 ^ 4 * 153 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
        simp [Nat.prime_two.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 153)]]
    norm_num
  obtain ⟨m, _, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model (ZMod 17) hK S
  have hm : m = 3 := by
    have hecard : 2 * 2 ^ m = 16 := by
      simpa only [DihedralGroup.nat_card, hS] using (Nat.card_congr e.toEquiv).symm
    have he : 2 ^ (m + 1) = 2 ^ 4 := by
      rw [pow_succ, mul_comm, hecard]
      decide
    have hm1 := (Nat.pow_right_injective (by decide : 2 ≤ 2)) he
    omega
  subst m
  exact ⟨e⟩

/-- The literal involution-centralizer product for any four-group, using the
square of the supplied order-eight actor. -/
theorem four_group_product
    (r : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 17)) (hr : orderOf r = 8)
    (A : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 17)))
    (hA : IsKleinFour A) :
    ∃ t g a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 17),
      t ∈ A ∧ orderOf t = 2 ∧ Commute g t ∧ a ∈ A ∧ b ∈ A ∧
        IsConj (r ^ 2) (a * (g * b * g⁻¹)) :=
  Theory.GroupTheory.DihedralSixteenProducts.product_of_dihedral_sylows
    sylow_equiv_dihedral_sixteen r hr A hA

end Theory.PSL2.SeventeenGeometry
