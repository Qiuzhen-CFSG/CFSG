module
public import CFSG.Quasithin.ChapterF.Section01.RankOneSmallTwoPart
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder

/-!
# Rank-one sections in the larger Mathieu orders

The M24 order permits only PSL₂(4) and PSL₂(8) among nonsolvable source
rank-one models. The defining-characteristic parts bound all field degrees;
the exact Suzuki and unitary orders exclude their remaining parameters.
The projective unitary calculation retains the cubic scalar denominator.

This is the order reduction for the M22, M23 and M24 containing-component
rows of original 5.2.2. The actual quotient-marked applications are in
Chapter6/SourceReduction/RankOneModuleGenericExceptionalCartanGlobalPrimeSylowMathieu.
Source: Aschbacher–Smith F.1.1 and5.2.2, pp.259 and648–649
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source
variable {X : Type*} [Group X] [Finite X]
private theorem solvable_of_six (hc : Nat.card X = 6) : Group.IsSolvable X := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  rw [hc] at hd
  have hh : p = 2 ∨ p = 3 := by
    have := hp.dvd_mul.mp (show p ∣ 2 * 3 from hd)
    exact this.imp ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp)
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp)
  exact hh

private theorem unitary_small_solvable {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hc : Nat.card F = 2 ^ 2)
    (hj : ∀ x, J.conj x = x ^ 2) : Group.IsSolvable J.specialSubgroup := by
  let := HermitianForm.FixedFieldTwo.projective_isSolvable J hc hj
  let : Group.IsSolvable J.specialToProjective.ker :=
    Group.isSolvable_of_isSolvable_injective
      (inclusion_injective J.specialToProjective_ker_le_center)
  exact Group.isSolvable_of_ker_le_range J.specialToProjective.ker.subtype
    J.specialToProjective (by simp)


private theorem unitary_degree_one {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hj : ∀ x, J.conj x = x ^ (2 ^ f))
    (hd : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) ∣ 244823040) : f = 1 := by
  have hpow := (HermitianForm.BinarySylowOrder.cube_dvd_card_projective J
    (by omega : f ≠ 0) hF hj).trans hd
  have hf3 : f ≤ 3 := by
    by_contra hh
    have hh := (pow_dvd_pow 2 (by omega : 11 ≤ f * 3)).trans
      (by simpa only [pow_mul] using hpow : 2 ^ (f * 3) ∣ 244823040)
    norm_num at hh
  have hfix := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 f
    (by omega) hF hj
  rw [Representation.SU3.BinaryDegree.card_projective J hF hfix] at hd
  interval_cases f
  · rfl
  all_goals norm_num at hd

/-- The common M24 order permits only PSL2(4) and PSL2(8) among nonsolvable
source rank-one sections. -/
theorem IsRankOneModel.mathieu_section (hm : IsRankOneModel X)
    (hns : ¬ Group.IsSolvable X) (hd : Nat.card X ∣ 244823040) :
    ClassicalGroup.IsPSL X 2 4 ∨ ClassicalGroup.IsPSL X 2 8 := by
  cases hm with
  | linear f hf hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
    rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (CharTwo.neg_eq 1),mul_one,hF,←Nat.card_congr e.toEquiv] at hc
    have hpow : 2 ^ f ∣ 244823040 := by
      apply dvd_trans (dvd_mul_right _ ((2 ^ f)^2 - 1))
      rwa [←hc]
    have hf10 : f ≤ 10 := by
      by_contra hh
      have hh := (pow_dvd_pow 2 (by omega : 11 ≤ f)).trans hpow
      norm_num at hh
    have hf23 : f = 2 ∨ f = 3 := by
      interval_cases f
      · exact (hns (solvable_of_six (by norm_num at hc; exact hc))).elim
      · exact .inl rfl
      · exact .inr rfl
      all_goals rw [hc] at hd; norm_num at hd
    rcases hf23 with rfl | rfl
    · exact .inl ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩
    · exact .inr ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩
  | suzuki m hm =>
    obtain ⟨e⟩ := hm
    by_cases hm0 : m = 0
    · subst m
      let := suzukiZero_isSolvable
      exact (hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
    have hc := suzukiMatrixGroup_card m (by omega)
    rw [Nat.card_congr e.toEquiv,hc] at hd
    have hpow : 2 ^ ((2*m+1)*2) ∣ 244823040 := by
      rw [pow_mul]
      exact (dvd_mul_of_dvd_left (dvd_mul_left _ _) _).trans hd
    have hm2 : m ≤ 2 := by
      by_contra hh
      have hh := (pow_dvd_pow 2 (by omega : 11 ≤ (2*m+1)*2)).trans hpow
      norm_num at hh
    have hmpos : 1 ≤ m := by omega
    interval_cases m <;> norm_num at hd
  | projective_unitary f hf hm =>
    obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
    have hf1 := unitary_degree_one J hf hF hj ((Nat.card_congr e.toEquiv) ▸ hd)
    subst f
    let := HermitianForm.FixedFieldTwo.projective_isSolvable J (by simpa using hF) (by simpa using hj)
    exact (hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  | special_unitary f hf hm =>
    obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
    have hproj := (card_dvd_of_surjective J.specialToProjective J.specialToProjective_surjective).trans
      ((Nat.card_congr e.toEquiv) ▸ hd)
    have hf1 := unitary_degree_one J hf hF hj hproj
    subst f
    let := unitary_small_solvable J (by simpa using hF) (by simpa using hj)
    exact (hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  | dihedral hm =>
    obtain ⟨e⟩ := hm
    let := GLS3.Chapter5.dihedralGroup_isSolvable 5
    exact (hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
end CFSG.Quasithin.ChapterF.Source
