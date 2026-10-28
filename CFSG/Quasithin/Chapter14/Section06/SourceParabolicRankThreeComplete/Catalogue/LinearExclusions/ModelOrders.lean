module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.ModelBounds
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic

/-!
# Central-quotient orders in the higher linear catalogue comparison

The two candidate star models have central quotients of order 20,160.
Every odd degree-three model retains a defining-prime cube after quotienting
by its whole center. For SU₃ this uses the actual special-to-projective map:
simplicity and perfectness of PSU₃ identify its kernel with the full center.
The proof uses the existing root-group divisor, not a full unitary order count.

Source: Aschbacher--Smith original 14.6.10(5), p.1029, comparing C.2.7(3)
with F.6.18(10)--(11), pp.309--310; Huppert II.10.12--13 for the unitary step.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.LinearExclusions
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open FSource BenderSuzuki.MatrixGroups

private noncomputable def centralCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)

/-- An actual SL₃(4) marking has central quotient of order 20,160. -/
theorem linearThree_central_card {D F : Type*} [Group D] [Field F] [Finite F]
    (e : D ≃* SL(3,F)) (hF : Nat.card F = 4) :
    Nat.card (D ⧸ center D) = 20160 := by
  rw [Nat.card_congr (centralCongr e).toEquiv]
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  norm_num [hF, Fin.prod_univ_succ] at h
  change Nat.card (SL(3,F) ⧸ center SL(3,F)) * 3 * 3 = 181440 at h
  omega

/-- An actual SL₄(2) marking has central quotient of order 20,160. -/
theorem linearFour_central_card {D F : Type*} [Group D] [Field F] [Finite F]
    (e : D ≃* SL(4,F)) (hF : Nat.card F = 2) :
    Nat.card (D ⧸ center D) = 20160 := by
  rw [Nat.card_congr (centralCongr e).toEquiv]
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  norm_num [hF, Fin.prod_univ_succ] at h
  exact h

private theorem cube_unitary {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hc : Nat.card F = p ^ 2) (hf : ∀ x, J.conj x = x ^ p) :
    p ^ 3 ∣ Nat.card (J.specialSubgroup ⧸ center J.specialSubgroup) ∧
    p ^ 3 ∣ Nat.card ((ProjectiveSpecialUnitaryMatrixGroup J) ⧸
      center (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa using hc) (by simpa using hf)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J p (lt_of_le_of_ne hp.two_le (Ne.symm hp2)) hc hfixed
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    J.projective_isPerfect_of_fixed_card (lt_of_le_of_ne hp.two_le (Ne.symm hp2)) hc hfixed
  have hz : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
        with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
  have hproj := J.prime_cube_dvd_card_projective hp hc hf
  constructor
  · let a := (QuotientGroup.quotientMulEquivOfEq
      (J.specialToProjective_ker_eq_center hz).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
        J.specialToProjective_surjective)
    rwa [Nat.card_congr a.toEquiv]
  · rwa [hz, Nat.card_congr (QuotientGroup.quotientBot.toEquiv)]

/-- The defining-prime cube survives quotienting by the whole center in
each special or projective degree-three row. -/
theorem degreeThree_central_prime_cube {D : Type*} [Group D] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : DegreeThree p D) : p ^ 3 ∣ Nat.card (D ⧸ center D) := by
  cases h with
  | linear F hc _ e =>
    rw [Nat.card_congr (centralCongr e).toEquiv, ← hc]
    exact Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card
  | projectiveLinear F hc _ e =>
    rw [Nat.card_congr (centralCongr e).toEquiv,
      Group.IsPerfect.center_quotient_center_eq_bot SL(3,F),
      Nat.card_congr (QuotientGroup.quotientBot.toEquiv), ← hc]
    exact Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card
  | unitary F J hc hf _ e =>
    rw [Nat.card_congr (centralCongr e).toEquiv]
    exact (cube_unitary J hp hp2 hc hf).1
  | projectiveUnitary F J hc hf _ e =>
    rw [Nat.card_congr (centralCongr e).toEquiv]
    exact (cube_unitary J hp hp2 hc hf).2

/-- The common candidate quotient order has no odd-prime cube divisor. -/
theorem no_odd_prime_cube_20160 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 3 ∣ 20160) : False := by
  have hd : p ∣ 2 * 2 * 2 * 2 * 2 * 2 * 3 * 3 * 5 * 7 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans h
  have he : p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 3 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    simpa only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7), or_assoc] using hd
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hp2 rfl | norm_num at h


end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.LinearExclusions
