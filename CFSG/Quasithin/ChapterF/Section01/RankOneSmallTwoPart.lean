module
public import CFSG.Quasithin.ChapterF.Section01.SourceBasic
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.SpecificGroups.DihedralSolvable
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Source rank-one models with two-part at most eight

The defining-characteristic root groups exclude every positive Suzuki
parameter and every unitary degree above one. The small Suzuki, unitary,
dihedral and linear endpoints are solvable. Thus a nonsolvable model in
F.1.1 whose order is not divisible by sixteen is PSL₂(4) or PSL₂(8).
Both special and projective unitary alternatives are retained in the proof.

The actual consumer is the alternating-seven containing-component branch
of original 5.2.2. Source: Aschbacher–Smith F.1.1, printed p.259, and
5.2.2, printed pp.648–649 (`refs/quasithin.pdf`).
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

/-- A nonsolvable source rank-one model with two-part at most eight is
binary PSL₂ over the field of order four or eight. -/
theorem IsRankOneModel.binary_of_small_twoPart (hm : IsRankOneModel X)
    (hns : ¬ Group.IsSolvable X) (hsmall : ¬ 16 ∣ Nat.card X) :
    ∃ f : ℕ, 1 < f ∧ f ≤ 3 ∧ ClassicalGroup.IsPSL X 2 (2 ^ f) := by
  cases hm with
  | linear f hf hm =>
    have hm' := hm
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hf1 : f ≠ 1 := by
      intro he
      have hF2 : Nat.card F = 2 := by simpa [he] using hF
      obtain ⟨a⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two hF2
      apply hns
      apply solvable_of_six
      rw [Nat.card_congr (e.trans a).toEquiv,Nat.card_perm,Nat.card_fin]
      rfl
    have hd : 2 ^ f ∣ Nat.card X := by
      have ha := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
      have htwo : CharP F 2 := by
        let : Fintype F := Fintype.ofFinite F
        exact charP_of_card_eq_prime_pow (p := 2) (f := f)
          (by simpa [Nat.card_eq_fintype_card] using hF)
      let := htwo
      rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
        (CharTwo.neg_eq 1),mul_one,hF] at ha
      rw [Nat.card_congr e.toEquiv,ha]
      exact dvd_mul_right _ _
    refine ⟨f,by omega,?_,hm'⟩
    by_contra hn
    exact hsmall ((pow_dvd_pow 2 (by omega : 4 ≤ f)).trans hd)
  | suzuki m hm =>
    obtain ⟨e⟩ := hm
    by_cases hm0 : m = 0
    · subst m
      let := suzukiZero_isSolvable
      exact (hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
    · apply False.elim
      apply hsmall
      rw [Nat.card_congr e.toEquiv,suzukiMatrixGroup_card m (by omega)]
      apply dvd_mul_of_dvd_left
      apply dvd_mul_of_dvd_right
      change 2 ^ 4 ∣ (2 ^ (2 * m + 1)) ^ 2
      rw [←pow_mul]
      exact pow_dvd_pow 2 (by omega)
  | projective_unitary f hf hm =>
    obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
    by_cases hf1 : f = 1
    · subst f
      let := HermitianForm.FixedFieldTwo.projective_isSolvable J (by simpa using hF) (by simpa using hj)
      exact (hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
    · apply False.elim
      have hd := HermitianForm.BinarySylowOrder.cube_dvd_card_projective J (by omega : f ≠ 0) hF hj
      rw [←Nat.card_congr e.toEquiv] at hd
      exact hsmall ((show 16 ∣ (2 ^ f) ^ 3 from by
        change 2 ^ 4 ∣ (2 ^ f) ^ 3
        rw [←pow_mul]; exact pow_dvd_pow 2 (by omega)).trans hd)
  | special_unitary f hf hm =>
    obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
    by_cases hf1 : f = 1
    · subst f
      let := unitary_small_solvable J (by simpa using hF) (by simpa using hj)
      exact (hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
    · apply False.elim
      have hd := (HermitianForm.BinarySylowOrder.cube_dvd_card_projective J
        (by omega : f ≠ 0) hF hj).trans
        (card_dvd_of_surjective J.specialToProjective J.specialToProjective_surjective)
      rw [←Nat.card_congr e.toEquiv] at hd
      exact hsmall ((show 16 ∣ (2 ^ f) ^ 3 from by
        change 2 ^ 4 ∣ (2 ^ f) ^ 3
        rw [←pow_mul]; exact pow_dvd_pow 2 (by omega)).trans hd)
  | dihedral hm =>
    obtain ⟨e⟩ := hm
    let := GLS3.Chapter5.dihedralGroup_isSolvable 5
    exact (hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
end CFSG.Quasithin.ChapterF.Source
