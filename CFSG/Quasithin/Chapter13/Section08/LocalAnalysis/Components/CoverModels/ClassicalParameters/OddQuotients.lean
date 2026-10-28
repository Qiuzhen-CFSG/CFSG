module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels
public import Theory.SpecificGroups.SU3.PrimeOrderDivisibility
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.MatrixCocycle
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.SpecificGroups.ProjectiveLinearInvolutions

/-!
# Central quotients of odd-prime classical triple covers

Basis change preserves the stored Frobenius involution of the Hermitian
form. The explicit projective scalar-centralizer theorem then makes PSU₃
centerless. Consequently the natural SU-to-PSU kernel is exactly the center,
giving the genuine quotient comparison rather than an identification by name.
For SL₃ the projective carrier is already defined as this central quotient.

At the prime three the special-to-projective maps are isomorphisms, so
neither special group has center of order three. Finally the root groups
supply defining-prime cubes in both projective orders. These are the shared
inputs for comparing A.3.6 with the actual F.9.18 carriers.

Source: Aschbacher–Smith, A.3.6(2), printed p.43; F.9.18(4), pp.325–326;
and 13.8.17, p.953. The imported scalar and root calculations are proved
matrix-group results, with no classification assumption.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
private def centerQuotientCongr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (G ⧸ center G) ≃* (H ⧸ center H) :=
  QuotientGroup.congr (center G) (center H) e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro y hy
      exact ⟨e.symm y, (centerCongr e.symm ⟨y, hy⟩).property, e.apply_symm_apply y⟩)

private theorem standard_center_eq_bot {F : Type*} [Field F]
    (J : HermitianForm 3 F) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (h2 : (2 : F) ≠ 0) (hconj : ∃ t : F, J.conj t ≠ t) :
    center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨u, rfl⟩ := J.specialToProjective_surjective x
  apply mem_bot.mpr
  apply Subtype.ext
  rw [J.specialToProjective_apply_val]
  apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
  apply Descent.projective_centralizer_scalar J hJ h2 hconj
  intro b
  have he := congrArg Subtype.val ((mem_center_iff.mp hx b).symm)
  change (Matrix.ProjGenLinGroup.mk (u : Matrix.GeneralLinearGroup (Fin 3) F)) *
      (b : Matrix.ProjGenLinGroup (Fin 3) F) =
      (b : Matrix.ProjGenLinGroup (Fin 3) F) *
        Matrix.ProjGenLinGroup.mk (u : Matrix.GeneralLinearGroup (Fin 3) F)
  simpa only [Subgroup.coe_mul, J.specialToProjective_apply_val] using he

private theorem unitary_center_eq_bot {F : Type} [Field F] [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p) :
    center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa using hcard) (by simpa using hconj)
  have hnonfixed : ∃ t : F, J.conj t ≠ t := by
    by_contra! h
    have hc : Nat.card {x : F // J.conj x = x} = Nat.card F :=
      Nat.card_congr (Equiv.subtypeUnivEquiv h)
    rw [hcard, hfixed] at hc
    have := hp.two_le
    nlinarith
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J p hcard hfixed
  have hz := standard_center_eq_bot (FormTransport.standardForm J) rfl
    (Field.two_ne_zero_of_odd_card F (by rw [hcard]; exact ho.pow)) hnonfixed
  apply Subgroup.card_eq_one.mp
  rw [Nat.card_congr (centerCongr e).toEquiv, hz]
  exact Subgroup.card_bot

/-- The central quotient is the actual projective model over the same fixed field. -/
theorem quotient_isPSLSign {G : Type*} [Group G] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) {unitary : Bool} (h : IsSLSign G unitary 3 p) :
    IsPSLSign (G ⧸ center G) unitary 3 p := by
  cases unitary with
  | false =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    exact ⟨F, inferInstance, inferInstance, hF, ⟨centerQuotientCongr e⟩⟩
  | true =>
    obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
    have hker := J.specialToProjective_ker_eq_center (unitary_center_eq_bot J hp ho hF hconj)
    let f : (J.specialSubgroup ⧸ center J.specialSubgroup) ≃*
        ProjectiveSpecialUnitaryMatrixGroup J :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective J.specialToProjective_surjective)
    exact ⟨F, inferInstance, inferInstance, J, hF, hconj, ⟨(centerQuotientCongr e).trans f⟩⟩

/-- The defining-prime root group contributes a cube to the projective order. -/
theorem prime_cube_dvd_card {G : Type*} [Group G] {p : ℕ}
    (hp : p.Prime) {unitary : Bool} (h : IsPSLSign G unitary 3 p) :
    p ^ 3 ∣ Nat.card G := by
  cases unitary with
  | false =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv, ← hF]
    exact Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card
  | true =>
    obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact J.prime_cube_dvd_card_projective hp hF hconj

/-- A nontrivial center of order three excludes defining characteristic three. -/
theorem odd_parameter_ge_five {G : Type*} [Group G] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) {unitary : Bool}
    (hz : Nonempty (center G ≃* Multiplicative (ZMod 3)))
    (h : IsSLSign G unitary 3 p) : 5 ≤ p := by
  have hc : Nat.card (center G) = 3 := by
    obtain ⟨e⟩ := hz
    exact (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 3)
  have hne : p ≠ 3 := by
    rintro rfl
    cases unitary with
    | false =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
      rw [Nat.card_congr (centerCongr e).toEquiv, Atlas.ExceptionalSupport.card_sl_center, hF] at hc
      norm_num at hc
    | true =>
      obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
      let f := e.trans (J.specialProjectiveEquivOfCardNine (by simpa using hF))
      have hZ := unitary_center_eq_bot J hp ho hF hconj
      rw [Nat.card_congr (centerCongr f).toEquiv, hZ, Subgroup.card_bot] at hc
      norm_num at hc
  have hp2 := hp.two_le
  have hodd := ho.not_two_dvd_nat
  omega
end CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
