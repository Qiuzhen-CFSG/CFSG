module
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import CFSG.Quasithin.ChapterA.Section02.OddLie
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalRanks

/-!
# The complete split-linear Case I branch of A.2.17

An actual fundamental SL₂ and its complementary block subgroup put the
source residual inside an involution centralizer. Quasithinness bounds that
residual directly, forcing degree three with field exponent at most two, or
degree four over a prime field. The actual split torus imposes the Fermat
parameter in degree four. Ordinary defining ranks supply exactly the C-list
restriction. Rank one retains every odd field in B and exponent at most two
in C. No residual-rank or family-recognition premise remains.

Source: Aschbacher–Smith, A.2.17, printed pp.38–39.
-/

open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  {r e : ℕ} [Fact r.Prime] [CharP F r]

private theorem local_bound (hqt : IsQuasithin G) (hr : Odd r)
    (z : G) (hz : z ≠ 1) (hz2 : z^2=1) :
    primeRank r (centralizer ({z} : Set G)) ≤ 2 :=
  Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt _
    (Theory.GroupTheory.isTwoLocal_involution_centralizer (orderOf_eq_prime hz2 hz))
    r Fact.out hr

/-- The actual centralizer of a fundamental SL₂ has defining-prime rank at
most one, directly from quasithinness of its containing group. -/
public theorem fundamental_centralizer_rank_le_one
    (hr : Odd r) (hcard : Nat.card F = r ^ e)
    (hqt : IsQuasithin G) (j : SL(2,F) →* G) (hj : Function.Injective j) :
    primeRank r (centralizer (j.range : Set G)) ≤ 1 := by
  have hr2 : r ≠ 2 := fun he => by subst r; exact (by decide : ¬ Odd 2) hr
  have hd : r ∣ Nat.card SL(2,F) := by
    rw [GorensteinWalter.sl2_card_formula F, hcard]
    have he : e ≠ 0 := by
      intro he
      have hFcard : 1 < Nat.card F := Finite.one_lt_card
      simp [he] at hcard
      omega
    exact dvd_mul_of_dvd_left (dvd_pow_self r he) _
  exact (RootCoverTransfer.sl2_complementary_primeRank_le_one hr2 hr
    (by rw [hcard]; exact hr.pow) j hj (centralizer (j.range : Set G)) le_rfl hd
    (local_bound hqt hr) (MonoidHom.id _) Function.surjective_id).1

/-- The actual split-linear model has only the source dimensions and field
degrees under quasithinness, without a residual-rank assumption. -/
public theorem linear_parameters_of_quasithin (d : ℕ)
    (hr : Odd r) (he : 1 ≤ e) (hcard : Nat.card F = r ^ e)
    (hqt : IsQuasithin (ClassicalStructure.LinearAmbient F d)) :
    e ≤ 2 ∧ (3 + d = 3 ∨ 3 + d = 4 ∧ e = 1) := by
  let j := ClassicalStructure.linearFundamental F d
  have hj := ClassicalStructure.linearFundamental_injective F d
  have hC := fundamental_centralizer_rank_le_one hr hcard hqt j hj
  have hJ : primeRank r (ClassicalStructure.linearResidual F d r) ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective r
      (ClassicalStructure.linearResidual F d r).subtype Subtype.val_injective).trans hC
  have hr2 : r ≠ 2 := fun he => by subst r; exact (by decide : ¬ Odd 2) hr
  exact ⟨sl2_fieldExponent_le_two hr2 hcard j hj (local_bound hqt hr),
    ClassicalStructure.linear_dimension_of_residual_rank F d hcard (by omega) hJ⟩

/-- The full odd split-linear Case I branch, with the exact original field
parameter, produces the B-list and the stronger C-list when appropriate. -/
public theorem linear_caseI {n : ℕ} (hn : 2 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPSL G n (r ^ e)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hr2 : r ≠ 2 := fun hh => by subst r; exact (by decide : ¬ Odd 2) hr
  by_cases hn2 : n = 2
  · subst n
    refine ⟨.odd (.linear_two (r^e) hr.pow model), ?_⟩
    intro hsq
    obtain ⟨F, hF, hfin, hcard, ⟨iso⟩⟩ := model
    let : Fintype F := Fintype.ofFinite F
    let : CharP F r := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hcard)
    have hdeg : e ≤ 2 := psl2_fieldExponent_le_two hcard iso.symm.toMonoidHom
      iso.symm.injective (hsq r Fact.out hr)
    exact .odd (.linear_two r e Fact.out hr hdeg
      ⟨F, hF, hfin, hcard, ⟨iso⟩⟩)
  obtain ⟨d, rfl⟩ : ∃ d, n = 3 + d := ⟨n-3, by omega⟩
  obtain ⟨F, hF, hfin, hcard, ⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hqtF := Theory.GroupTheory.isQuasithin_of_equiv iso hqt
  have hqtSum := Theory.GroupTheory.isQuasithin_of_equiv
    (ClassicalStructure.linearModelEquiv F d).symm hqtF
  obtain ⟨hdeg, hd | ⟨hd, he1⟩⟩ := linear_parameters_of_quasithin d hr he hcard hqtSum
  · have hd0 : d = 0 := by omega
    subst d
    have m : ClassicalGroup.IsPSL G 3 (r^e) := ⟨F, hF, hfin, hcard, ⟨iso⟩⟩
    refine ⟨.odd (.linear_three r e Fact.out hr hdeg m), ?_⟩
    intro hsq
    have he1 := psl3_fieldExponent_eq_one_of_stronglyQuasithin hr2 hcard he
      iso.symm.toMonoidHom iso.symm.injective hsq
    subst e
    exact .odd (.linear_three r Fact.out hr (by simpa only [pow_one] using m))
  · have hd1 : d = 1 := by omega
    subst d
    subst e
    have hcard' : Nat.card F = r := by simpa only [pow_one] using hcard
    have m : ClassicalGroup.IsPSL G 4 r := ⟨F, hF, hfin, hcard', ⟨iso⟩⟩
    refine ⟨.odd (.linear_four r Fact.out
      (psl4_fermat_parameter_of_quasithin hr2 hcard' iso hqt) m), ?_⟩
    intro hsq
    exact (psl4_not_stronglyQuasithin hr2 hcard (by decide : 1 ≤ 1)
      iso.symm.toMonoidHom iso.symm.injective hsq).elim
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
