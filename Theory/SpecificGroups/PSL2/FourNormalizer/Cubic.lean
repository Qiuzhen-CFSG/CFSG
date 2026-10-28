module
public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage.RootGroups
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
import Mathlib.Tactic

/-!
# A cubic automizer of every four-group in odd PSL₂

Choose two distinct nonidentity elements of the four-group. Their lifts A,B
have squares minus identity and anticommute. The determinant-one matrix
(I+A)(I+B)/2 conjugates A to B and B to AB. Its projective image therefore
induces a three-cycle on the three nonidentity elements of the original
four-group, so three divides the order of its actual normalizer.

This matrix calculation supplies the cubic part of Aschbacher–Smith
2.5.8(5), printed pp.556–557. It works over every finite field of odd
characteristic and does not assume a normalizer or subgroup classification.
-/

open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.PSL2.FourNormalizer
open Theory.PSL2.OuterSolvable.OddCoverage
variable {K : Type*} [Field K]

private theorem lift_sq (h2 : (2 : K) ≠ 0) (A : SL(2,K))
    (hne : quotientMap K A ≠ 1) (hsq : quotientMap K A ^ 2 = 1) : A ^ 2 = -1 := by
  have hcenter : A ^ 2 ∈ center SL(2,K) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change quotientMap K (A ^ 2) = 1
    simpa only [map_pow] using hsq
  rcases center_eq_one_or_neg_one _ hcenter with h | h
  · have hd : (SpecialLinearGroup.toGL A).det = 1 := by apply Units.ext; exact A.property
    rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one h2
        (SpecialLinearGroup.toGL A) (by rw [← map_pow, h, map_one]) hd with he | he
    · have hA : A = 1 := SpecialLinearGroup.toGL_injective (by simpa using he)
      exact (hne (by rw [hA, map_one])).elim
    · have hA : A = -1 := Subtype.ext (congrArg Units.val he)
      apply (hne _).elim
      simpa using (quotientMap_eq_iff A 1).mpr (Or.inr hA)
  · exact h

private theorem trace_of_sq (A : SL(2,K)) (hA : A ^ 2 = -1) : trace A.val = 0 := by
  have hi : A⁻¹ = -A := inv_eq_of_mul_eq_one_right (by
    rw [mul_neg, ← pow_two, hA, neg_neg])
  have he := congrArg (fun X : SL(2,K) => X.val 0 0) hi
  have he' : A.val 1 1 = -A.val 0 0 := by
    simpa only [SpecialLinearGroup.coe_inv, adjugate_fin_two, SpecialLinearGroup.coe_neg,
      Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using he
  rw [trace_fin_two, he', add_neg_cancel]


private theorem anti (h2 : (2 : K) ≠ 0) (A B : SL(2,K))
    (hA : A ^ 2 = -1) (hB : B ^ 2 = -1) (hAB : (A * B) ^ 2 = -1)
    (hcomm : quotientMap K A * quotientMap K B = quotientMap K B * quotientMap K A) :
    A * B = -(B * A) := by
  rcases (quotientMap_eq_iff (A * B) (B * A)).mp (by simpa only [map_mul] using hcomm) with h | h
  · have hp : (A * B) ^ 2 = 1 := by rw [(show Commute A B from h).mul_pow, hA, hB]; simp
    have he := congrArg (fun X : SL(2,K) => X.val 0 0) (hAB.symm.trans hp)
    have he' : (-1 : K) = 1 := by simpa using he
    exact (h2 (by linear_combination -he')).elim
  · exact h

private theorem det_one_add (A : SL(2,K)) (ht : trace A.val = 0) :
    det (1 + A.val) = 2 := by
  have hd := A.property
  simp only [det_fin_two, trace_fin_two] at hd ht ⊢
  norm_num [Matrix.add_apply, Matrix.one_apply]
  linear_combination hd + ht

private def cubicMatrix (A B : SL(2,K)) : Matrix (Fin 2) (Fin 2) K :=
  (2 : K)⁻¹ • ((1 + A.val) * (1 + B.val))

private theorem cubic_det (h2 : (2 : K) ≠ 0) (A B : SL(2,K))
    (hA : A ^ 2 = -1) (hB : B ^ 2 = -1) : det (cubicMatrix A B) = 1 := by
  rw [cubicMatrix, det_smul, Fintype.card_fin, det_mul,
    det_one_add A (trace_of_sq A hA), det_one_add B (trace_of_sq B hB)]
  field_simp

private def cubic (h2 : (2 : K) ≠ 0) (A B : SL(2,K))
    (hA : A ^ 2 = -1) (hB : B ^ 2 = -1) : SL(2,K) :=
  ⟨cubicMatrix A B, cubic_det h2 A B hA hB⟩

private theorem cubic_moves (h2 : (2 : K) ≠ 0) (A B : SL(2,K))
    (hA : A ^ 2 = -1) (hB : B ^ 2 = -1) (hab : A * B = -(B * A)) :
    cubic h2 A B hA hB * A = B * cubic h2 A B hA hB ∧
      cubic h2 A B hA hB * B = (A * B) * cubic h2 A B hA hB := by
  have ha : A.val * A.val = -1 := by simpa only [pow_two, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one] using congrArg Subtype.val hA
  have hb : B.val * B.val = -1 := by simpa only [pow_two, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one] using congrArg Subtype.val hB
  have hab' : B.val * A.val = -(A.val * B.val) := by
    have h := congrArg Subtype.val hab
    simpa only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_neg, neg_neg] using congrArg Neg.neg h.symm
  have haba : (A.val * B.val) * A.val = B.val := by
    rw [mul_assoc, hab', mul_neg, ← mul_assoc, ha, neg_mul, one_mul, neg_neg]
  have habb : (A.val * B.val) * B.val = -A.val := by rw [mul_assoc, hb, mul_neg, mul_one]
  have hbab : B.val * (A.val * B.val) = A.val := by
    rw [← mul_assoc, hab', neg_mul, habb, neg_neg]
  have habab : (A.val * B.val) * (A.val * B.val) = -1 := by rw [← mul_assoc, haba, hb]
  constructor <;> apply Subtype.ext
  all_goals change ((2 : K)⁻¹ • ((1 + A.val) * (1 + B.val))) * _ = _ * ((2 : K)⁻¹ • ((1 + A.val) * (1 + B.val)))
  all_goals rw [Matrix.smul_mul, Matrix.mul_smul]; congr 1
  all_goals simp only [SpecialLinearGroup.coe_mul, add_mul, mul_add, one_mul, mul_one,
    ha, hb, haba, habb, hbab, habab, hab']
  all_goals abel


/-- Every four-group in finite odd-characteristic PSL₂ has a cubic automizer. -/
public theorem three_dvd_four_normalizer [Finite K] (h2 : (2 : K) ≠ 0)
    (F : Subgroup PSL(2,K)) [IsKleinFour F] :
    3 ∣ Nat.card (normalizer (F : Set PSL(2,K))) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hc : Nat.card F = 4 := IsKleinFour.card_four
  let : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsMulCommutative F := IsKleinFour.isMulCommutative
  obtain ⟨a, ha⟩ := exists_ne (1 : F)
  obtain ⟨b, hb, hba⟩ : ∃ b : F, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    have hsub : (Finset.univ : Finset F) ⊆ {1, a} := by
      intro b _
      by_cases hb : b = 1
      · simp [hb]
      · have he : b = a := Classical.byContradiction fun hba => h ⟨b,hb,hba⟩
        simp [he]
    have hd := Finset.card_le_card hsub
    simp only [Finset.card_univ, IsKleinFour.card_four', Finset.card_pair (Ne.symm ha)] at hd
    omega
  have hcases (x : F) : x = a * b ∨ x = a ∨ x = b ∨ x = 1 := by
    have hh := Finset.mem_univ x
    rw [← IsKleinFour.eq_finset_univ ha hb hba.symm] at hh
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  have hap : (a : PSL(2,K)) ≠ 1 := fun h => ha (Subtype.ext h)
  have hbp : (b : PSL(2,K)) ≠ 1 := fun h => hb (Subtype.ext h)
  have habp : (a : PSL(2,K)) * b ≠ 1 := by
    intro h
    have h' : a * b = 1 := Subtype.ext h
    have h'' : a = b := by simpa only [IsKleinFour.inv_eq_self] using (mul_eq_one_iff_eq_inv.mp h')
    exact hba h''.symm
  have hpow (x : F) : (x : PSL(2,K)) ^ 2 = 1 := by
    exact congrArg Subtype.val (show x ^ 2 = 1 from by simpa only [pow_two] using IsKleinFour.mul_self x)
  obtain ⟨A, hA⟩ := quotientMap_surjective K (a : PSL(2,K))
  obtain ⟨B, hB⟩ := quotientMap_surjective K (b : PSL(2,K))
  have hAs : A ^ 2 = -1 := lift_sq h2 A (hA ▸ hap) (hA ▸ hpow a)
  have hBs : B ^ 2 = -1 := lift_sq h2 B (hB ▸ hbp) (hB ▸ hpow b)
  have hAB : quotientMap K (A * B) = (a : PSL(2,K)) * b := by rw [map_mul, hA, hB]
  have hABs : (A * B) ^ 2 = -1 := lift_sq h2 (A * B) (hAB ▸ habp) (hAB ▸ hpow (a*b))
  have hab : A * B = -(B * A) := anti h2 A B hAs hBs hABs (by
    rw [hA, hB]
    exact congrArg Subtype.val (mul_comm' a b))
  let C := cubic h2 A B hAs hBs
  let g := quotientMap K C
  obtain ⟨hCa, hCb⟩ := cubic_moves h2 A B hAs hBs hab
  have hga : (MulAut.conj g) (a : PSL(2,K)) = b := by
    apply mul_inv_eq_iff_eq_mul.mpr
    have h := congrArg (quotientMap K) hCa
    simpa only [map_mul, hA, hB] using h
  have hgb : (MulAut.conj g) (b : PSL(2,K)) = (a : PSL(2,K)) * b := by
    apply mul_inv_eq_iff_eq_mul.mpr
    have h := congrArg (quotientMap K) hCb
    simpa only [map_mul, hA, hB] using h
  have hgab : (MulAut.conj g) ((a : PSL(2,K)) * b) = a := by
    rw [map_mul, hga, hgb]
    exact congrArg Subtype.val (show b * (a * b) = a from by
      rw [← mul_assoc, mul_comm' b a, mul_assoc, IsKleinFour.mul_self, mul_one])
  have hnorm : g ∈ normalizer (F : Set PSL(2,K)) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      change MulAut.conj g x ∈ F
      rcases hcases ⟨x,hx⟩ with h | h | h | h
      · rw [show x = (a : PSL(2,K)) * b from congrArg Subtype.val h, hgab]
        exact a.property
      · rw [show x = (a : PSL(2,K)) from congrArg Subtype.val h, hga]
        exact b.property
      · rw [show x = (b : PSL(2,K)) from congrArg Subtype.val h, hgb]
        exact F.mul_mem a.property b.property
      · rw [show x = (1 : PSL(2,K)) from congrArg Subtype.val h, map_one]
        exact F.one_mem
    · rw [card_map_of_injective (MulAut.conj g).injective]
  let gn : normalizer (F : Set PSL(2,K)) := ⟨g, hnorm⟩
  let α := F.normalizerMonoidHom gn
  have haa : α a = b := Subtype.ext hga
  have habb : α b = a * b := Subtype.ext hgb
  have habab : α (a * b) = a := Subtype.ext hgab
  have ha3 : α ^ 3 = 1 := by
    apply MulEquiv.ext
    intro x
    change α (α (α x)) = x
    rcases hcases x with rfl | rfl | rfl | rfl
    · rw [habab, haa, habb]
    · rw [haa, habb, habab]
    · rw [habb, habab, haa]
    · simp only [map_one]
  have hane : α ≠ 1 := by
    intro h
    have hh := DFunLike.congr_fun h a
    exact hba (haa.symm.trans hh)
  have hao : orderOf α = 3 := orderOf_eq_prime ha3 hane
  have hd := (orderOf_map_dvd F.normalizerMonoidHom gn).trans (_root_.orderOf_dvd_natCard gn)
  exact hao ▸ hd

end Theory.PSL2.FourNormalizer
