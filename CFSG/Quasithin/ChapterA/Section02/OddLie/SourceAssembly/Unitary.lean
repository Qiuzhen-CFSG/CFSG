module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Linear
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure.Unitary
public import CFSG.KnownSimple.UnitaryRankOne

/-!
# The complete odd unitary Case I source branch

The actual fundamental SL₂ over the fixed field and complementary SU maps
work for every stored Hermitian form. The complementary defining rank bound
is derived inside its actual fundamental centralizer; the known residual
identification then restricts the dimension. Degree three yields the B/C
exponent bounds, and degree four yields the Mersenne parameter and failure
of strong quasithinness. The rank-one alias is transported to PSL₂.

Source: Aschbacher–Smith, A.2.17, printed p.39.
-/

open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental
variable {F : Type*} [Field F] [Finite F] {r e : ℕ} [Fact r.Prime]

/-- An arbitrary stored Hermitian model satisfies the source dimension and
field restrictions, using its actual fundamental and complementary maps. -/
public theorem unitary_parameters_of_quasithin {n : ℕ} (hn : 0 < n)
    (J : HermitianForm (2+n) F) (hr : Odd r) (he : 1 ≤ e)
    (hcard : Nat.card F = (r^e)^2) (hconj : ∀ x, J.conj x = x^(r^e))
    (hqt : IsQuasithin (ProjectiveSpecialUnitaryMatrixGroup J)) :
    e ≤ 2 ∧ (n = 1 ∨ n = 2 ∧ e = 1) := by
  let : NeZero n := ⟨by omega⟩
  let : Finite (ProjGenLinGroup (Fin (2+n)) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  obtain ⟨f, c, hf, _, hc, hcomm, hz, hz2, hdeg⟩ :=
    ClassicalStructure.unitary_fundamental J hr2 (by omega) hcard hconj
  have hq : IsPrimePow (r^e) := (isPrimePow_nat_iff _).mpr ⟨r,e,Fact.out,by omega,rfl⟩
  have hfixed : Nat.card (FixedBy.subfield F J.conj) = r^e :=
    J.fixed_card_prime_power hq hcard hconj
  let : Fintype (FixedBy.subfield F J.conj) := Fintype.ofFinite _
  let : CharP (FixedBy.subfield F J.conj) r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hfixed)
  have hC := fundamental_centralizer_rank_le_one hr hfixed hqt f hf
  let cc : (form J.conj J.conj_involutive n).specialSubgroup →*
      centralizer (f.range : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    c.codRestrict _ (fun b => by
      apply mem_centralizer_iff.mpr
      rintro _ ⟨a,rfl⟩
      exact (hcomm a b).eq)
  have hcc : Function.Injective cc := by
    intro a b hab
    exact hc (congrArg Subtype.val hab)
  have hSU : primeRank r (form J.conj J.conj_involutive n).specialSubgroup ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective r cc hcc).trans hC
  have hres : primeRank r (residual J.conj J.conj_involutive (n := n) r) ≤ 1 := by
    rw [primeRank_residual J.conj J.conj_involutive hr2 (by omega) hcard hconj hn r]
    exact hSU
  have he2 : e ≤ 2 := hdeg.trans
    (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt _
      (Theory.GroupTheory.isTwoLocal_involution_centralizer (orderOf_eq_prime hz2 hz))
      r Fact.out hr)
  exact ⟨he2, dimension_restriction_of_residual_rank_le_one J.conj J.conj_involutive
    hr2 (by omega) hn hcard hconj hres⟩

/-- The full odd unitary Case I branch for every Hermitian form and every
catalogue dimension, with the original fixed-field parameter. -/
public theorem unitary_caseI {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPSU G n (r ^ e)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  by_cases hn2 : n = 2
  · subst n
    apply linear_caseI (n := 2) (by decide) hr he hqt
    exact model.isPSL_two ((isPrimePow_nat_iff _).mpr ⟨r,e,Fact.out,by omega,rfl⟩)
  obtain ⟨d, hd, rfl⟩ : ∃ d, 0 < d ∧ n = 2+d := ⟨n-2, by omega, by omega⟩
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨iso⟩⟩ := model
  have hqtF := Theory.GroupTheory.isQuasithin_of_equiv iso hqt
  obtain ⟨he2, hd1 | ⟨hd2, he1⟩⟩ := unitary_parameters_of_quasithin hd J hr he hcard hconj hqtF
  · subst d
    have m : ClassicalGroup.IsPSU G 3 (r^e) := ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩
    refine ⟨.odd (.unitary_three r e Fact.out hr he2 m), ?_⟩
    intro hsq
    have he1 := psu3_fieldExponent_eq_one_of_stronglyQuasithin J hr2 hcard he hconj
      iso.symm.toMonoidHom iso.symm.injective hsq
    subst e
    exact .odd (.unitary_three r Fact.out hr (by simpa only [pow_one] using m))
  · subst d
    subst e
    have hcard' : Nat.card F = r^2 := by simpa only [pow_one] using hcard
    have hconj' : ∀ x, J.conj x = x^r := by simpa only [pow_one] using hconj
    have m : ClassicalGroup.IsPSU G 4 r := ⟨F,hF,hfin,J,hcard',hconj',⟨iso⟩⟩
    obtain ⟨b, _, hb⟩ := psu4_mersenne_parameter_of_quasithin J hr2 hcard' hconj' iso hqt
    refine ⟨.odd (.unitary_four r Fact.out ⟨b,hb⟩ m), ?_⟩
    intro hsq
    exact (psu4_not_stronglyQuasithin J hr2 hcard' hconj'
      iso.symm.toMonoidHom iso.symm.injective hsq).elim
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
