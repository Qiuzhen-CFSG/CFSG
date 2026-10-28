module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.ModuleCases
public import Theory.GroupTheory.ComponentLocalPrimeFree
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Identifying the smaller component through the missing prime 31

The genuine smaller component supplied by 15.3.15 has core quotient
PSL₃(2), PSL₄(2), or PSL₅(2), by 15.3.22. The maximal-parabolic Levi
quotients have no factor of 31 in their order. Neither a two-core nor a
normalizing two-group introduces that prime. Thus the PSL₅(2) alternative
cannot occur in the actual subgroup PS. Its remaining component quotient
is one of the two earlier exclusions, with its original star action intact.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the last paragraph of 15.3.24, printed p.1130 (PDF p.1147).
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics

private theorem projective_card (n : ℕ) (hn : 0 < n) :
    Nat.card (Projective n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  rw [Nat.card_congr (projectiveEquivLinear hn).toEquiv,
    ← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

private theorem projective_three_card : Nat.card (Projective 3) = 168 := by
  rw [projective_card 3 (by decide)]
  norm_num [Fin.prod_univ_succ]

private theorem projective_four_card : Nat.card (Projective 4) = 20160 := by
  rw [projective_card 4 (by decide)]
  norm_num [Fin.prod_univ_succ]

private theorem projective_five_card : Nat.card (Projective 5) = 9999360 := by
  rw [projective_card 5 (by decide)]
  norm_num [Fin.prod_univ_succ]

private theorem not_thirtyOne_dvd_twoGroup {H : Type*} [Group H] [Finite H]
    (h : IsPGroup 2 H) : ¬ 31 ∣ Nat.card H := by
  obtain ⟨n, hn⟩ := h.exists_card_eq
  rw [hn]
  intro hd
  have := (by decide : Nat.Prime 31).dvd_of_dvd_pow hd
  norm_num at this

/-- Neither maximal-parabolic Levi factor has a factor of 31. Removing its
intrinsic two-core introduces no such prime either. -/
theorem not_thirtyOne_dvd_of_levi {H : Type*} [Group H] [Finite H]
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Projective 3)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Projective 4)) : ¬ 31 ∣ Nat.card H := by
  have hm : ¬ 31 ∣ Nat.card (H ⧸ pCore 2 H) := by
    rcases he with hprod | hfour
    · obtain ⟨e⟩ := hprod
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, projective_three_card]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    · obtain ⟨e⟩ := hfour
      rw [Nat.card_congr e.toEquiv, projective_four_card]
      decide
  intro hd
  have hc := (pCore 2 H).card_mul_index
  change Nat.card (pCore 2 H) * Nat.card (H ⧸ pCore 2 H) = Nat.card H at hc
  rw [← hc] at hd
  exact ((by decide : Nat.Prime 31).dvd_mul.mp hd).elim
    (not_thirtyOne_dvd_twoGroup pCore_isPGroup) hm

variable {G : Type*} [Group G] [Finite G]

/-- Adjoining the normalizing Sylow factor cannot restore the missing prime.
The hypothesis is relative normalization, not ambient normality of P. -/
theorem not_thirtyOne_dvd_join (P S : Subgroup G)
    (hn : S ≤ normalizer (P : Set G)) (hS : IsPGroup 2 S)
    (he : Nonempty ((P ⧸ pCore 2 P) ≃* (Equiv.Perm (Fin 3) × Projective 3)) ∨
      Nonempty ((P ⧸ pCore 2 P) ≃* Projective 4)) :
    ¬ 31 ∣ Nat.card (P ⊔ S : Subgroup G) :=
  Theory.GroupTheory.not_dvd_card_sup_of_normalizes (by decide) P S hn
    (not_thirtyOne_dvd_of_levi he) (not_thirtyOne_dvd_twoGroup hS)

omit [Finite G] in
/-- A genuine component of the new outside overgroup cannot have the
five-dimensional quotient. Its actual embedding supplies the order divisibility. -/
theorem component_not_five (d : LocalData G) {K : Subgroup G}
    (c : ComponentWitness d K) (hK : ¬ 31 ∣ Nat.card K)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 5) : False := by
  have hd : 31 ∣ Nat.card (c.L ⧸ pCore 2 c.L) := by
    rw [Nat.card_congr e.toEquiv, projective_five_card]
    decide
  exact hK (hd.trans ((pCore 2 c.L).index_dvd_card.trans (card_dvd_of_le (component_le c))))

omit [Finite G] in
/-- Apply the exact three-case conclusion of 15.3.22 to the new component.
The output concerns its own core quotient; no star action is transported
from the original component. -/
theorem smaller_component_models (d : LocalData G) {K : Subgroup G}
    (c : ComponentWitness d K) (hK : ¬ 31 ∣ Nat.card K)
    (h22 : ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧
      Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Projective n)) :
    Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Projective 3) ∨
      Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Projective 4) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := h22
  rcases hn with rfl | rfl | rfl
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e⟩
  · exact (component_not_five d c hK e).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics

end
