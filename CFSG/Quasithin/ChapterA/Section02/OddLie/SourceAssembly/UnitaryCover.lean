module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.OrdinaryRootTransfer
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Unitary
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.CoverCases
public import Theory.SpecificGroups.PSU3.OddCenterRecognition

/-!
# Odd unitary central quotients in source A.2.17

Ordinary root transfer bounds the unitary dimension and field degree using
quasithinness of the original group. For degree three, this restricts the
fixed field to a prime or prime square. The concrete covering-kernel
calculations then force a nontrivial odd center to have order three, and
the projective three-rank bound contradicts the actual A.2.14 witness.
Source: Aschbacher–Smith A.2.14 and A.2.17, printed pp.37–39.
-/

open Subgroup Matrix Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- The original group's quasithinness supplies all unitary dimension and
field restrictions outside the two exceptional SL₂ field orders. -/
public theorem unitary_parameters_of_ordinary_central_quotient
    {n r e : ℕ} [Fact r.Prime] (hn : 0 < n)
    (J : HermitianForm (2+n) F) (hr : Odd r) (he : 1 ≤ e)
    (hcard : Nat.card F = (r^e)^2) (hconj : ∀ x, J.conj x = x^(r^e))
    (hgt : 3 < r^e) (h9 : r^e ≠ 9)
    (iso : G ⧸ center G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hqt : IsQuasithin G) : e ≤ 2 ∧ (n = 1 ∨ n = 2 ∧ e = 1) := by
  let : NeZero n := ⟨by omega⟩
  let : Finite (ProjGenLinGroup (Fin (2+n)) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  obtain ⟨f,c,hf,_,hc,hcomm,_,_,_⟩ :=
    ClassicalStructure.unitary_fundamental J hr2 (by omega) hcard hconj
  have hq : IsPrimePow (r^e) := (isPrimePow_nat_iff _).mpr ⟨r,e,Fact.out,by omega,rfl⟩
  have hfixed : Nat.card (FixedBy.subfield F J.conj) = r^e :=
    J.fixed_card_prime_power hq hcard hconj
  let : Fintype (FixedBy.subfield F J.conj) := Fintype.ofFinite _
  let : CharP (FixedBy.subfield F J.conj) r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hfixed)
  let π := iso.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hπ : Function.Surjective π := iso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπc : π.ker ≤ center G := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    change QuotientGroup.mk' (center G) x = 1
    exact iso.map_eq_one_iff.mp (MonoidHom.mem_ker.mp hx)
  obtain ⟨he2,hC,_⟩ := ordinary_root_source_bounds hr he hfixed
    (by rwa [hfixed]) (by rwa [hfixed]) π hπ hπc f hf hqt
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
  exact ⟨he2,dimension_restriction_of_residual_rank_le_one J.conj J.conj_involutive
    hr2 (by omega) hn hcard hconj hres⟩

/-- Original source Case II's ordinary-field unitary model is PSU₃ of
exponent at most two or PSU₄ over a prime field. -/
public theorem unitary_central_quotient_parameters_of_ordinary_field
    {n r e : ℕ} [Fact r.Prime] (hn : 3 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (hgt : 3 < r^e) (h9 : r^e ≠ 9) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) n (r^e)) :
    e ≤ 2 ∧ (n = 3 ∨ n = 4 ∧ e = 1) := by
  obtain ⟨d,hd,rfl⟩ : ∃ d, 0 < d ∧ n = 2+d := ⟨n-2,by omega,by omega⟩
  obtain ⟨F,hF,hfin,J,hc,hj,⟨iso⟩⟩ := model
  obtain ⟨he2,hD⟩ := unitary_parameters_of_ordinary_central_quotient hd J hr he hc hj hgt h9 iso hqt
  exact ⟨he2,by omega⟩

/-- No original odd central cover with ordinary fixed-field parameter can
have unitary degree at least five. No kernel-prime condition is assumed. -/
public theorem unitary_high_degree_central_quotient_false
    {n r e : ℕ} [Fact r.Prime] (hn : 5 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (hgt : 3 < r^e) (h9 : r^e ≠ 9) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) n (r^e)) : False := by
  have hh := unitary_central_quotient_parameters_of_ordinary_field (by omega) hr he hgt h9 hqt model
  omega

/-- All original quasithin central quotients of degree-three unitary type
have prime or prime-square fixed field, including q = 3 and q = 9. -/
public theorem unitary_three_fieldExponent_le_two_of_central_quotient
    {r e : ℕ} [Fact r.Prime] (hr : Odd r) (he : 1 ≤ e)
    (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) 3 (r^e)) : e ≤ 2 := by
  by_contra hle
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hr3 : 3 ≤ r := by have := (Fact.out : r.Prime).two_le; omega
  have hlarge : 27 ≤ r^e := (by norm_num : 27 = 3^3) ▸
    ((Nat.pow_le_pow_left hr3 3).trans (Nat.pow_le_pow_right (by omega) (by omega)))
  have hh := unitary_central_quotient_parameters_of_ordinary_field
    (by decide : 3 ≤ 3) hr he (by omega) (by omega) hqt model
  exact hle hh.1

universe u
variable {K : GroupClass.{u}} {G₀ S : Type u} [Group G₀] [Finite G₀]
  [Group S] [Finite S] [IsQuasisimple G₀] {p : ℕ}

/-- Every odd PSU₃ central quotient is excluded in source Case II. The
actual covering center has order three, and A.2.14 contradicts the proved
nondefining projective three-rank bound. -/
public theorem unitary_three_caseII
    (h : CounterexampleToTheoremA K G₀ S p) (ih : TheoremsOnProperSections K G₀)
    (hP : IsPGroup p (center G₀)) {r e : ℕ} [Fact r.Prime]
    (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSU (G₀ ⧸ center G₀) 3 (r^e)) : False := by
  have he2 := unitary_three_fieldExponent_le_two_of_central_quotient hr he h.1 model
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩ := model
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have ho : Odd (Nat.card (center G₀)) := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    rw [hk]
    exact h.2.2.2.2.2.1.pow
  obtain ⟨hZ,hm⟩ := HermitianForm.OddCenterRecognition.nontrivial_center_card
    J Fact.out hr2 he he2 hcard hconj iso ho (h.center_ne_bot ih.theoremA)
  have hp3 : p = 3 := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    have hd : 3 ∣ p^k := by rw [← hk,hZ]
    exact ((Nat.dvd_prime h.2.2.2.2.1).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)).resolve_left (by decide) |>.symm
  subst p
  have hr3 : r ≠ 3 := by
    intro hh
    subst r
    have hd : 3 ∣ 3^e := dvd_pow_self 3 (by omega)
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  have hl := ClassicalRanks.NondefiningThree.threeRank_le_two_of_psu3_equiv
    J iso hcard hconj he hr2 hr3
  exact (not_le_of_gt (lemma_A_2_14_center h ih.theoremA hZ)) hl

end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
