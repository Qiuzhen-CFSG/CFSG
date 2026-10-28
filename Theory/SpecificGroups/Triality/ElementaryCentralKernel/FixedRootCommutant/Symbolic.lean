module
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.ScalarForm
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.Sparse

/-!
# A folded root with distinct parameters removes the extra commutant entries

Four entries of the commutator with `x₀(a)x₂(b)x₃(c)` force the five-parameter
constant-root commutant to be scalar whenever `a,b,c` are pairwise distinct.
This calculation works in any field of characteristic two.

Source: the fixed-root parametrizations in GLS3 §2.4. The Frobenius-orbit
specialization is made in the main commutant module.
-/

public section
namespace Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
variable {F : Type*} [Field F] [CharP F 2]

set_option maxRecDepth 8000 in
private lemma folded_equation_0 (A : Matrix (Fin 28) (Fin 28) F) (a b c : F)
    (h : Commute (normalForm A)
      (rootMatrix 0 true a * rootMatrix 2 true b * rootMatrix 3 true c)) :
    (c + a) * A 0 3 = 0 := by
  have he : (normalForm A * rootMatrix 0 true a * rootMatrix 2 true b *
      rootMatrix 3 true c) 0 27 =
      (rootMatrix 0 true a * (rootMatrix 2 true b * (rootMatrix 3 true c * normalForm A))) 0 27 := by
    simpa only [Matrix.mul_assoc] using
      congrArg (fun M : Matrix (Fin 28) (Fin 28) F => M 0 27) h.eq
  simp [mul_root_entry, root_mul_entry, rootCols, rootRows, quadraticPosition] at he
  simp [normalForm] at he
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) he

set_option maxRecDepth 8000 in
private lemma folded_equation_1 (A : Matrix (Fin 28) (Fin 28) F) (a b c : F)
    (h : Commute (normalForm A)
      (rootMatrix 0 true a * rootMatrix 2 true b * rootMatrix 3 true c)) :
    (b + a) * A 2 0 = 0 := by
  have he : (normalForm A * rootMatrix 0 true a * rootMatrix 2 true b *
      rootMatrix 3 true c) 2 6 =
      (rootMatrix 0 true a * (rootMatrix 2 true b * (rootMatrix 3 true c * normalForm A))) 2 6 := by
    simpa only [Matrix.mul_assoc] using
      congrArg (fun M : Matrix (Fin 28) (Fin 28) F => M 2 6) h.eq
  simp [mul_root_entry, root_mul_entry, rootCols, rootRows, quadraticPosition] at he
  simp [normalForm] at he
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) he

set_option maxRecDepth 8000 in
private lemma folded_equation_2 (A : Matrix (Fin 28) (Fin 28) F) (a b c : F)
    (h : Commute (normalForm A)
      (rootMatrix 0 true a * rootMatrix 2 true b * rootMatrix 3 true c)) :
    (c + a) * (A 0 2 + A 0 3 + A 2 0) = 0 := by
  have he : (normalForm A * rootMatrix 0 true a * rootMatrix 2 true b *
      rootMatrix 3 true c) 3 6 =
      (rootMatrix 0 true a * (rootMatrix 2 true b * (rootMatrix 3 true c * normalForm A))) 3 6 := by
    simpa only [Matrix.mul_assoc] using
      congrArg (fun M : Matrix (Fin 28) (Fin 28) F => M 3 6) h.eq
  simp [mul_root_entry, root_mul_entry, rootCols, rootRows, quadraticPosition] at he
  simp [normalForm] at he
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) he

set_option maxRecDepth 8000 in
private lemma folded_equation_3 (A : Matrix (Fin 28) (Fin 28) F) (a b c : F)
    (h : Commute (normalForm A)
      (rootMatrix 0 true a * rootMatrix 2 true b * rootMatrix 3 true c)) :
    (c + b) * (A 0 0 + A 0 3 + A 2 2) = 0 := by
  have he : (normalForm A * rootMatrix 0 true a * rootMatrix 2 true b *
      rootMatrix 3 true c) 3 26 =
      (rootMatrix 0 true a * (rootMatrix 2 true b * (rootMatrix 3 true c * normalForm A))) 3 26 := by
    simpa only [Matrix.mul_assoc] using
      congrArg (fun M : Matrix (Fin 28) (Fin 28) F => M 3 26) h.eq
  simp [mul_root_entry, root_mul_entry, rootCols, rootRows, quadraticPosition] at he
  simp [normalForm] at he
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) he

/-- A folded root with three distinct parameters makes the constant-root
normal form scalar. -/
theorem normalForm_scalar_of_folded (A : Matrix (Fin 28) (Fin 28) F)
    (a b c : F) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : Commute (normalForm A)
      (rootMatrix 0 true a * rootMatrix 2 true b * rootMatrix 3 true c)) :
    normalForm A = A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F) := by
  have hca : c + a ≠ 0 := fun he => hac (CharTwo.add_eq_zero.mp he).symm
  have hba : b + a ≠ 0 := fun he => hab (CharTwo.add_eq_zero.mp he).symm
  have hcb : c + b ≠ 0 := fun he => hbc (CharTwo.add_eq_zero.mp he).symm
  have h₂ : A 0 3 = 0 := (mul_eq_zero.mp (folded_equation_0 A a b c h)).resolve_left hca
  have h₃ : A 2 0 = 0 := (mul_eq_zero.mp (folded_equation_1 A a b c h)).resolve_left hba
  have h₁ : A 0 2 = 0 := by
    have he := (mul_eq_zero.mp (folded_equation_2 A a b c h)).resolve_left hca
    simpa only [h₂, h₃, add_zero] using he
  have h₄ : A 2 2 = A 0 0 := by
    have he := (mul_eq_zero.mp (folded_equation_3 A a b c h)).resolve_left hcb
    rw [h₂, add_zero, CharTwo.add_eq_zero] at he
    exact he.symm
  exact normalForm_scalar A h₁ h₂ h₃ h₄

end Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
