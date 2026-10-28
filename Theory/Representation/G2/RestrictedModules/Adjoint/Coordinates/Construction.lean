module

public import Theory.Representation.G2.RestrictedModules.AdjointAction

/-!
# Fourteen explicit octonion derivations

In characteristic two the trace-zero three-by-three block and two three-vectors
in the Zorn description supply fourteen parameters. In Wilson's eight-coordinate
convention the formula below satisfies the actual octonion Leibniz rule. We check
its eight polynomial coordinates separately. Reading fourteen specified matrix
entries is a left inverse; the converse is proved in `Reconstruction`.

Source: GLS3, Examples 1.14.9(c) and 2.8.10(g). The literal multiplication and
coordinate convention are from the attributed ATLAS split-octonion imports.
-/

@[expose] public section
namespace Atlas.G2.Restricted.Adjoint.Coordinates
open Atlas.SplitOctonion
variable {F : Type*} [Field F] [CharP F 2]

/-- The eight-coordinate formula before imposing the Leibniz subtype. -/
def endomorphism (p : Fin 14 → F) : Module.End F (Carrier F) where
  toFun x := ![
    p 13*x 0 + p 7*x 1 + p 4*x 2 + p 2*x 3 + p 2*x 4 + p 1*x 5 + p 0*x 6,
    p 12*x 0 + p 6*x 1 + p 3*x 2 + p 4*x 3 + p 4*x 4 + p 2*x 5 + p 0*x 7,
    p 11*x 0 + p 5*x 1 + (p 6+p 13)*x 2 + p 7*x 3 + p 7*x 4 + p 2*x 6 + p 1*x 7,
    p 10*x 0 + p 11*x 1 + p 12*x 2 + p 7*x 5 + p 4*x 6 + p 2*x 7,
    p 10*x 0 + p 11*x 1 + p 12*x 2 + p 7*x 5 + p 4*x 6 + p 2*x 7,
    p 9*x 0 + p 10*x 1 + p 12*x 3 + p 12*x 4 + (p 6+p 13)*x 5 + p 3*x 6 + p 4*x 7,
    p 8*x 0 + p 10*x 2 + p 11*x 3 + p 11*x 4 + p 5*x 5 + p 6*x 6 + p 7*x 7,
    p 8*x 1 + p 9*x 2 + p 10*x 3 + p 10*x 4 + p 11*x 5 + p 12*x 6 + p 13*x 7]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

private theorem leibniz_0 (r : Fin 14 → F) (x y : Carrier F) :
    endomorphism r (mul x y) 0 =
      (mul (endomorphism r x) y + mul x (endomorphism r y)) 0 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp [endomorphism, mul, sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp [char_two]

private theorem leibniz_1 (r : Fin 14 → F) (x y : Carrier F) :
    endomorphism r (mul x y) 1 =
      (mul (endomorphism r x) y + mul x (endomorphism r y)) 1 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp [endomorphism, mul, sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp [char_two]

private theorem leibniz_2 (r : Fin 14 → F) (x y : Carrier F) :
    endomorphism r (mul x y) 2 =
      (mul (endomorphism r x) y + mul x (endomorphism r y)) 2 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp [endomorphism, mul, sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp [char_two]

private theorem leibniz_3 (r : Fin 14 → F) (x y : Carrier F) :
    endomorphism r (mul x y) 3 =
      (mul (endomorphism r x) y + mul x (endomorphism r y)) 3 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp [endomorphism, mul, sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp [char_two]

private theorem leibniz_4 (r : Fin 14 → F) (x y : Carrier F) :
    endomorphism r (mul x y) 4 =
      (mul (endomorphism r x) y + mul x (endomorphism r y)) 4 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp [endomorphism, mul, sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp [char_two]

private theorem leibniz_5 (r : Fin 14 → F) (x y : Carrier F) :
    endomorphism r (mul x y) 5 =
      (mul (endomorphism r x) y + mul x (endomorphism r y)) 5 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp [endomorphism, mul, sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp [char_two]

private theorem leibniz_6 (r : Fin 14 → F) (x y : Carrier F) :
    endomorphism r (mul x y) 6 =
      (mul (endomorphism r x) y + mul x (endomorphism r y)) 6 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp [endomorphism, mul, sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp [char_two]

private theorem leibniz_7 (r : Fin 14 → F) (x y : Carrier F) :
    endomorphism r (mul x y) 7 =
      (mul (endomorphism r x) y + mul x (endomorphism r y)) 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp [endomorphism, mul, sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp [char_two]

/-- The polynomial formula is an actual derivation of the split octonions. -/
theorem endomorphism_mem (r : Fin 14 → F) : endomorphism r ∈ Adjoint.derivations F := by
  intro x y
  ext i
  fin_cases i
  · exact leibniz_0 r x y
  · exact leibniz_1 r x y
  · exact leibniz_2 r x y
  · exact leibniz_3 r x y
  · exact leibniz_4 r x y
  · exact leibniz_5 r x y
  · exact leibniz_6 r x y
  · exact leibniz_7 r x y

/-- Coordinates ordered by the fourteen prescribed independent matrix entries. -/
abbrev Space (F : Type*) := Fin 14 → F

/-- A matrix entry, with the output coordinate first. -/
def entry (D : Module.End F (Carrier F)) (i j : Fin 8) : F := D (basisVector j) i

variable (F)

/-- Realize fourteen parameters as an actual octonion derivation. -/
def fromParams : Space F →ₗ[F] Adjoint.Space F where
  toFun r := ⟨endomorphism r, endomorphism_mem r⟩
  map_add' r s := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    ext i
    fin_cases i <;> simp [endomorphism] <;> ring
  map_smul' a r := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    ext i
    fin_cases i <;> simp [endomorphism] <;> ring

@[simp] theorem fromParams_val (r : Space F) :
    (fromParams F r).val = endomorphism r := rfl

/-- Transparent Wilson-coordinate equations for the realized derivation. -/
theorem fromParams_apply (r : Space F) (x : Carrier F) :
    (fromParams F r).val x = ![
    r 13*x 0 + r 7*x 1 + r 4*x 2 + r 2*x 3 + r 2*x 4 + r 1*x 5 + r 0*x 6,
    r 12*x 0 + r 6*x 1 + r 3*x 2 + r 4*x 3 + r 4*x 4 + r 2*x 5 + r 0*x 7,
    r 11*x 0 + r 5*x 1 + (r 6+r 13)*x 2 + r 7*x 3 + r 7*x 4 + r 2*x 6 + r 1*x 7,
    r 10*x 0 + r 11*x 1 + r 12*x 2 + r 7*x 5 + r 4*x 6 + r 2*x 7,
    r 10*x 0 + r 11*x 1 + r 12*x 2 + r 7*x 5 + r 4*x 6 + r 2*x 7,
    r 9*x 0 + r 10*x 1 + r 12*x 3 + r 12*x 4 + (r 6+r 13)*x 5 + r 3*x 6 + r 4*x 7,
    r 8*x 0 + r 10*x 2 + r 11*x 3 + r 11*x 4 + r 5*x 5 + r 6*x 6 + r 7*x 7,
    r 8*x 1 + r 9*x 2 + r 10*x 3 + r 10*x 4 + r 11*x 5 + r 12*x 6 + r 13*x 7] := rfl

/-- Read the independent entries in the fixed order. -/
def params : Adjoint.Space F →ₗ[F] Space F where
  toFun D := ![
    entry D.val 1 7, entry D.val 2 7, entry D.val 4 7, entry D.val 5 6,
    entry D.val 5 7, entry D.val 6 5, entry D.val 6 6, entry D.val 6 7,
    entry D.val 7 1, entry D.val 7 2, entry D.val 7 4, entry D.val 7 5,
    entry D.val 7 6, entry D.val 7 7]
  map_add' D E := by ext i; fin_cases i <;> rfl
  map_smul' a D := by ext i; fin_cases i <;> rfl

private theorem params_fromParams_0 (r : Space F) :
    params F (fromParams F r) 0 = r 0 := by
  change entry (endomorphism r) 1 7 = r 0
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_1 (r : Space F) :
    params F (fromParams F r) 1 = r 1 := by
  change entry (endomorphism r) 2 7 = r 1
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_2 (r : Space F) :
    params F (fromParams F r) 2 = r 2 := by
  change entry (endomorphism r) 4 7 = r 2
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_3 (r : Space F) :
    params F (fromParams F r) 3 = r 3 := by
  change entry (endomorphism r) 5 6 = r 3
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_4 (r : Space F) :
    params F (fromParams F r) 4 = r 4 := by
  change entry (endomorphism r) 5 7 = r 4
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_5 (r : Space F) :
    params F (fromParams F r) 5 = r 5 := by
  change entry (endomorphism r) 6 5 = r 5
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_6 (r : Space F) :
    params F (fromParams F r) 6 = r 6 := by
  change entry (endomorphism r) 6 6 = r 6
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_7 (r : Space F) :
    params F (fromParams F r) 7 = r 7 := by
  change entry (endomorphism r) 6 7 = r 7
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_8 (r : Space F) :
    params F (fromParams F r) 8 = r 8 := by
  change entry (endomorphism r) 7 1 = r 8
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_9 (r : Space F) :
    params F (fromParams F r) 9 = r 9 := by
  change entry (endomorphism r) 7 2 = r 9
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_10 (r : Space F) :
    params F (fromParams F r) 10 = r 10 := by
  change entry (endomorphism r) 7 4 = r 10
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_11 (r : Space F) :
    params F (fromParams F r) 11 = r 11 := by
  change entry (endomorphism r) 7 5 = r 11
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_12 (r : Space F) :
    params F (fromParams F r) 12 = r 12 := by
  change entry (endomorphism r) 7 6 = r 12
  simp [entry, endomorphism, basisVector]

private theorem params_fromParams_13 (r : Space F) :
    params F (fromParams F r) 13 = r 13 := by
  change entry (endomorphism r) 7 7 = r 13
  simp [entry, endomorphism, basisVector]

@[simp] theorem params_fromParams (r : Space F) : params F (fromParams F r) = r := by
  ext i
  fin_cases i
  · exact params_fromParams_0 F r
  · exact params_fromParams_1 F r
  · exact params_fromParams_2 F r
  · exact params_fromParams_3 F r
  · exact params_fromParams_4 F r
  · exact params_fromParams_5 F r
  · exact params_fromParams_6 F r
  · exact params_fromParams_7 F r
  · exact params_fromParams_8 F r
  · exact params_fromParams_9 F r
  · exact params_fromParams_10 F r
  · exact params_fromParams_11 F r
  · exact params_fromParams_12 F r
  · exact params_fromParams_13 F r

end Atlas.G2.Restricted.Adjoint.Coordinates
