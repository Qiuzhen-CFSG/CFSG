module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.ModuleCases
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.FactorIdentification.Kernel
public import Theory.SpecificGroups.BinaryLinear.CubicPairGeometry.Algebra
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The two actual quotients in the first paragraph of 15.3.24

The order of GL₄(2), and also of GL₅(2), has three-part nine. Removing
O₂(L) preserves that three-part, so Y₊ ≤ L rules out the extraspecial
order-27 option in 15.3.11(5i). This constructs Y₊/O₂(Y₊) ≃ E₉.
The earlier O₂,Φ quotient of Y₊S has order 36. The checked normalized-product
order argument makes its kernel a two-group, hence exactly O₂(Y₊S).
Transport along this proved equality constructs the required S₃ × S₃ quotient.

Both identifications use the actual intrinsic two-cores. In particular the
first is not an assertion that the entire image of Y₊ in L/O₂(L) has order
nine. The cubic alternative and Frattini quotient are genuine earlier
15.3.11(5i) inputs, not the preparation conclusions.

Source: Aschbacher–Smith, 15.3.11(5i), printed pp.1123–1124, and
15.3.24, printed p.1129 (combined manuscript, 1 March 2004).
-/

public section

open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation
variable {G : Type*} [Group G] [Finite G]

private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem linear_three_part {n : ℕ} (hn : n = 4 ∨ n = 5) :
    (Nat.card (LinearGroup n)).factorization 3 = 2 := by
  have hc : Nat.card (LinearGroup n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
    rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
    simp
  rw [hc]
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ]
  · rw [show 20160 = 3 ^ 2 * 2240 from rfl,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2240),
      Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_three]
  · rw [show 9999360 = 3 ^ 2 * 1111040 from rfl,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 1111040),
      Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_three]

/-- The component itself has three-part nine; its two-core contributes none. -/
theorem component_three_part {L : Subgroup G} {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : (L ⧸ pCore 2 L) ≃* Projective n) :
    (Nat.card L).factorization 3 = 2 := by
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  have hq := Nat.card_congr (e.trans (projectiveEquivLinear (by omega))).toEquiv
  rw [← (pCore 2 L).card_mul_index, index_eq_card, hq, hk,
    Nat.factorization_mul (pow_ne_zero _ (by decide)) Nat.card_pos.ne',
    Finsupp.add_apply, Nat.factorization_pow]
  simp only [Finsupp.smul_apply,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2), smul_zero, zero_add]
  exact linear_three_part hn

/-- The binary model excludes the earlier extraspecial alternative and yields the literal E₉ quotient. -/
theorem yplus_quotient (d : LocalData G) {L : Subgroup G} {n : ℕ}
    (hn : n = 4 ∨ n = 5) (e : (L ⧸ pCore 2 L) ≃* Projective n)
    (hYL : d.Yplus ≤ L)
    (halt : OutsideStructure.CubicQuotient (d.Yplus ⧸ pCore 2 d.Yplus)) :
    Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3)) := by
  rcases halt with h | ⟨_, hc, _⟩
  · exact h
  · have hd : 27 ∣ Nat.card L := hc ▸
      ((pCore 2 d.Yplus).index_dvd_card.trans (card_dvd_of_le hYL))
    have hh := (Nat.factorization_le_iff_dvd (by decide : 27 ≠ 0)
      (Nat.card_pos (α := L)).ne').mpr hd 3
    rw [component_three_part hn e] at hh
    have h27 : (27 : ℕ).factorization 3 = 3 := by
      rw [show 27 = 3 ^ 3 from rfl, Nat.factorization_pow]
      simp [Nat.Prime.factorization_self Nat.prime_three]
    rw [h27] at hh
    omega

/-- The original Frattini denominator equals the two-core, by its proved two-group order. -/
theorem coreFrattini_eq_twoCore (d : LocalData G)
    (hY : Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3)))
    (hSY : d.S ≤ normalizer (d.Yplus : Set G))
    (hshadow : Nonempty (((d.Yplus ⊔ d.S : Subgroup G) ⧸
      OutsideStructure.coreFrattiniSubgroup (d.Yplus ⊔ d.S : Subgroup G)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    OutsideStructure.coreFrattiniSubgroup (d.Yplus ⊔ d.S : Subgroup G) =
      pCore 2 (d.Yplus ⊔ d.S : Subgroup G) := by
  obtain ⟨eY⟩ := hY
  have h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9 := by
    rw [Nat.card_congr eY.toEquiv]
    change Nat.card (Fin 2 → ZMod 3) = 9
    simp
  obtain ⟨eH⟩ := hshadow
  have htwo := RankTwo.rankTwoShadow_kernel_isTwoGroup h9
    (d.T.isPGroup'.to_le (show d.S ≤ (d.T : Subgroup G) from inf_le_left)) hSY eH
  refine le_antisymm ?_ ?_
  · exact le_sSup ⟨inferInstance, htwo⟩
  · intro x hx
    change QuotientGroup.mk' (pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) x ∈
      frattini ((d.Yplus ⊔ d.S : Subgroup G) ⧸ pCore 2 (d.Yplus ⊔ d.S : Subgroup G))
    have hx' : QuotientGroup.mk' (pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx']
    exact one_mem _

/-- Construct the source quotient by O₂, retaining the original Frattini projection through a proved denominator equality. -/
theorem join_quotient (d : LocalData G) {L : Subgroup G} {n : ℕ}
    (hn : n = 4 ∨ n = 5) (e : (L ⧸ pCore 2 L) ≃* Projective n)
    (hYL : d.Yplus ≤ L)
    (halt : OutsideStructure.CubicQuotient (d.Yplus ⧸ pCore 2 d.Yplus))
    (hSY : d.S ≤ normalizer (d.Yplus : Set G))
    (hshadow : Nonempty (((d.Yplus ⊔ d.S : Subgroup G) ⧸
      OutsideStructure.coreFrattiniSubgroup (d.Yplus ⊔ d.S : Subgroup G)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    Nonempty (((d.Yplus ⊔ d.S : Subgroup G) ⧸ pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  have hy := yplus_quotient d hn e hYL halt
  have heq := coreFrattini_eq_twoCore d hy hSY hshadow
  obtain ⟨eqv⟩ := hshadow
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans eqv⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation
