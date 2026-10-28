module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Linear
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure.Symplectic
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure

/-!
# Odd symplectic and G₂ Case I source branches

The actual symplectic complementary group has defining rank at most one
inside the fundamental involution centralizer. Its concrete root groups
force rank two and a prime field; rank one transports to PSL₂. The G₂ root
pair similarly forces a prime field. The independent defining root triples
exclude the surviving PSp₄ and G₂ models from the strong list.

The conclusions are the literal Theorem B and C alternatives, with every
local-rank and parameter premise derived from the original quasithin model.
Source: Aschbacher–Smith, A.2.17, printed p.39.
-/

open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
open ClassificationModels
variable {G : Type*} [Group G] [Finite G] {r e : ℕ} [Fact r.Prime]

/-- The actual symplectic fundamental plane reduces the whole odd simple
symplectic branch to PSL₂ or prime-field PSp₄. -/
public theorem symplectic_caseI {n : ℕ} (hn : 1 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPSp G n (r ^ e)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  by_cases hn1 : n = 1
  · subst n
    obtain ⟨F, hF, hfin, hcard, ⟨iso⟩⟩ := model
    apply linear_caseI (n := 2) (by decide) hr he hqt
    exact ⟨F, hF, hfin, hcard,
      ⟨iso.trans Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv⟩⟩
  obtain ⟨k, hk, rfl⟩ : ∃ k, 0 < k ∧ n = k+1 := ⟨n-1, by omega, by omega⟩
  obtain ⟨F, hF, hfin, hcard, ⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hqtF := Theory.GroupTheory.isQuasithin_of_equiv iso hqt
  let j := ClassicalStructure.symplecticFundamental F k
  have hC := fundamental_centralizer_rank_le_one hr hcard hqtF j
    (ClassicalStructure.symplecticFundamental_injective F k hk)
  have hJ : primeRank r (ClassicalStructure.symplecticResidual F k r) ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective r
      (ClassicalStructure.symplecticResidual F k r).subtype Subtype.val_injective).trans hC
  obtain ⟨hn, he1⟩ := ClassicalStructure.symplectic_dimension_of_residual_rank F k hk
    hcard (by omega) hJ
  have hk1 : k = 1 := by omega
  subst k
  subst e
  have hc : Nat.card F = r := by simpa only [pow_one] using hcard
  have m : ClassicalGroup.IsPSp G 2 r := ⟨F, hF, hfin, hc, ⟨iso⟩⟩
  refine ⟨.odd (.symplectic r Fact.out hr m), ?_⟩
  intro hsq
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  exact (psp4_not_stronglyQuasithin hr2 hcard (by decide : 1 ≤ 1)
    iso.symm.toMonoidHom iso.symm.injective hsq).elim

/-- The two orthogonal root groups force a prime field in G₂, while the
three independent roots exclude strong quasithinness. -/
public theorem g2_caseI
    (hr : Odd r) (he : 1 ≤ e) (hqt : IsQuasithin G)
    (model : IsG2At G (r ^ e)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  obtain ⟨F, hF, hfin, hcard, ⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have he1 := g2_fieldExponent_eq_one_of_quasithin hr he hcard
    iso.symm.toMonoidHom iso.symm.injective hqt
  subst e
  have m : IsG2At G r := ⟨F, hF, hfin, by simpa only [pow_one] using hcard, ⟨iso⟩⟩
  refine ⟨.odd (.g2 r Fact.out hr m), ?_⟩
  intro hsq
  exact (g2_not_stronglyQuasithin hr (by decide : 1 ≤ 1) hcard
    iso.symm.toMonoidHom iso.symm.injective hsq).elim
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
