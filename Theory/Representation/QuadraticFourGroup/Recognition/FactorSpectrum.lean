module

public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows
public import Theory.Representation.QuadraticFourGroup.Recognition.Spectrum
public import Theory.SpecificGroups.PSL2.InvolutionFusion

/-!
# The element-order spectrum of binary PSL₂

An even-order element centralizes an involution in its own cyclic subgroup.
Involution fusion transports this involution to the upper transvection.
Commuting with that matrix forces upper-unipotent shape and square one.
Thus every element of SL₂ or its actual characteristic-two projective
quotient has order two or odd order.

Source: the elementary rank-one calculation behind GLS volume 2,
Chapter G, Theorem 25.14 Step 3 and the final argument of 26.24.
-/

open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups IsMulCommutative
namespace Representation.QuadraticFourGroup

variable {F : Type*} [Field F] [CharP F 2]

def markedUpper : SL(2,F) := SpecialLinearGroup.transvection zero_ne_one 1

lemma markedUpper_sq : (markedUpper : SL(2,F)) ^ 2 = 1 := by
  rw [markedUpper, pow_two, ← SpecialLinearGroup.transvection_add]
  simp [CharTwo.add_self_eq_zero]

omit [CharP F 2] in
lemma markedUpper_ne_one : (markedUpper : SL(2,F)) ≠ 1 := by
  intro he
  have hh := congrArg (fun t : SL(2,F) => t.val 0 1) he
  simp [markedUpper, SpecialLinearGroup.transvection_coe] at hh

lemma square_eq_one_of_commute_markedUpper (g : SL(2,F))
    (hc : Commute g (markedUpper : SL(2,F))) : g ^ 2 = 1 := by
  have he := hc.eq
  have h10 : g.val 1 0 = 0 := by
    have hh := congrArg (fun t : SL(2,F) => t.val 0 0) he
    simpa [markedUpper, SpecialLinearGroup.transvection_coe, mul_apply, Fin.sum_univ_two] using hh
  have hdiag : g.val 0 0 = g.val 1 1 := by
    have hh := congrArg (fun t : SL(2,F) => t.val 0 1) he
    have heq : g.val 0 0 + g.val 0 1 = g.val 0 1 + g.val 1 1 := by
      simpa [markedUpper, SpecialLinearGroup.transvection_coe, mul_apply, Fin.sum_univ_two] using hh
    exact add_right_cancel (heq.trans (add_comm _ _))
  have hsq : g.val 0 0 ^ 2 = 1 := by
    simpa only [det_fin_two, h10, ← hdiag, pow_two, mul_zero, sub_zero] using g.property
  have h00 : g.val 0 0 = 1 := by
    rcases sq_eq_one_iff.mp hsq with hh | hh
    · exact hh
    · simpa only [CharTwo.neg_eq] using hh
  have hu : g = SpecialLinearGroup.transvection zero_ne_one (g.val 0 1) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.transvection_coe, h10, h00, ← hdiag]
  rw [hu, pow_two, ← SpecialLinearGroup.transvection_add]
  simp [CharTwo.add_self_eq_zero]

public theorem specialLinear_involutionOddSpectrum [Finite F] : InvolutionOddSpectrum SL(2,F) := by
  intro g
  by_cases ho : Odd (orderOf g)
  · exact Or.inr ho
  left
  have hd : 2 ∣ orderOf g := Nat.not_odd_iff_even.mp ho |>.two_dvd
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' 2 (G := zpowers g)
    (by simpa only [Nat.card_zpowers] using hd)
  have ht' : orderOf (t : SL(2,F)) = 2 := by simpa only [Subgroup.orderOf_coe] using ht
  let e := SL2NaturalH1.projectiveEquiv (K := F)
  have htq : orderOf (e.symm t) = 2 := by
    change orderOf (e.symm.toMonoidHom t) = 2
    rw [orderOf_injective e.symm.toMonoidHom e.symm.injective, ht']
  have huq : orderOf (e.symm (markedUpper : SL(2,F))) = 2 := by
    change orderOf (e.symm.toMonoidHom (markedUpper : SL(2,F))) = 2
    rw [orderOf_injective e.symm.toMonoidHom e.symm.injective]
    exact orderOf_eq_prime markedUpper_sq markedUpper_ne_one
  obtain ⟨x,hx⟩ := isConj_iff.mp (Theory.PSL2.involutions_isConj
    (e.symm t) (e.symm (markedUpper : SL(2,F))) htq huq)
  have hx' : e x * (t : SL(2,F)) * (e x)⁻¹ = markedUpper := by
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using congrArg e hx
  have hc : Commute g (t : SL(2,F)) := by
    have hh : Commute (⟨g,mem_zpowers g⟩ : zpowers g) t := Commute.all _ _
    exact hh.map (zpowers g).subtype
  have hcc := hc.map (MulAut.conj (e x)).toMonoidHom
  change Commute (MulAut.conj (e x) g) (e x * (t : SL(2,F)) * (e x)⁻¹) at hcc
  rw [hx'] at hcc
  have hs := square_eq_one_of_commute_markedUpper (MulAut.conj (e x) g) hcc
  have hg2 : g ^ 2 = 1 := (MulAut.conj (e x)).injective (by simpa only [map_pow, map_one] using hs)
  have hd2 := orderOf_dvd_of_pow_eq_one hg2
  exact Nat.dvd_antisymm hd2 hd

public theorem factor_involutionOddSpectrum (n : ℕ) : InvolutionOddSpectrum (Factor n) :=
  specialLinear_involutionOddSpectrum.of_surjective
    (SL2NaturalH1.projectiveEquiv (K := GaloisField 2 n)).symm.toMonoidHom
    (SL2NaturalH1.projectiveEquiv (K := GaloisField 2 n)).symm.surjective
end Representation.QuadraticFourGroup
