module
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.NormalForm

/-! Scalar specialization of the constant-root normal form. Each row is checked
separately to keep the kernel certificates and elaboration contexts small. -/

public section
namespace Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private lemma scalar_row_0 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 0 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 0 c := by
  intro c
  fin_cases c
  · change A 0 0 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 2 = A 0 0 * 0
    simp_all
  · change A 0 3 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_1 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 1 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 1 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_2 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 2 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 2 c := by
  intro c
  fin_cases c
  · change A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 2 2 = A 0 0 * 1
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_3 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 3 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 3 c := by
  intro c
  fin_cases c
  · change A 0 2 + A 0 3 + A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 3 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change A 0 3 + A 2 0 + A 2 2 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_4 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 4 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 4 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_5 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 5 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 5 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 3 = A 0 0 * 0
    simp_all
  · change A 0 2 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_6 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 6 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 6 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 2 = A 0 0 * 0
    simp_all
  · change A 0 3 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_7 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 7 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 7 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_8 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 8 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 8 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_9 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 9 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 9 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 3 = A 0 0 * 0
    simp_all
  · change A 0 2 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_10 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 10 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 10 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 2 = A 0 0 * 0
    simp_all
  · change A 0 3 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_11 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 11 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 11 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_12 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 12 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 12 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 2 2 = A 0 0 * 1
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_13 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 13 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 13 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 3 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change A 0 3 + A 2 0 + A 2 2 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 2 + A 0 3 + A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_14 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 14 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 14 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 3 + A 2 0 + A 2 2 = A 0 0 * 1
    simp_all
  · change A 0 0 + A 0 3 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 2 + A 0 3 + A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_15 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 15 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 15 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change A 2 2 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_16 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 16 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 16 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 2 = A 0 0 * 0
    simp_all
  · change A 0 3 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_17 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 17 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 17 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_18 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 18 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 18 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

omit [CharP F 2] in
private lemma scalar_row_19 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 19 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 19 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 3 = A 0 0 * 0
    simp_all
  · change A 0 2 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_20 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 20 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 20 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 2 + A 0 3 + A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 3 + A 2 0 + A 2 2 = A 0 0 * 1
    simp_all
  · change A 0 0 + A 0 3 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_21 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 21 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 21 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change A 2 2 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_22 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 22 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 22 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 2 2 = A 0 0 * 1
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_23 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 23 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 23 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 2 + A 0 3 + A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 3 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change A 0 3 + A 2 0 + A 2 2 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_24 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 24 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 24 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 2 + A 0 3 + A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 3 + A 2 0 + A 2 2 = A 0 0 * 1
    simp_all
  · change A 0 0 + A 0 3 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_25 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 25 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 25 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change A 2 2 = A 0 0 * 1
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all

private lemma scalar_row_26 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 26 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 26 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 2 2 = A 0 0 * 1
    simp_all
  · change A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _

private lemma scalar_row_27 (A : Matrix (Fin 28) (Fin 28) F)
    (_h₁ : A 0 2 = 0) (_h₂ : A 0 3 = 0) (_h₃ : A 2 0 = 0) (_h₄ : A 2 2 = A 0 0) :
    ∀ c, normalForm A 27 c = (A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F)) 27 c := by
  intro c
  fin_cases c
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 2 + A 0 3 + A 2 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change 0 = A 0 0 * 0
    simp_all
  · change A 0 0 + A 0 3 + A 2 2 = A 0 0 * 0
    simp_all
    exact CharTwo.add_self_eq_zero _
  · change A 0 3 + A 2 0 + A 2 2 = A 0 0 * 1
    simp_all

/-- The four vanishing/off-diagonal conditions make the normal form scalar. -/
theorem normalForm_scalar (A : Matrix (Fin 28) (Fin 28) F)
    (h₁ : A 0 2 = 0) (h₂ : A 0 3 = 0) (h₃ : A 2 0 = 0) (h₄ : A 2 2 = A 0 0) :
    normalForm A = A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F) := by
  ext r c
  fin_cases r
  · exact scalar_row_0 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_1 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_2 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_3 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_4 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_5 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_6 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_7 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_8 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_9 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_10 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_11 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_12 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_13 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_14 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_15 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_16 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_17 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_18 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_19 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_20 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_21 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_22 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_23 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_24 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_25 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_26 A h₁ h₂ h₃ h₄ c
  · exact scalar_row_27 A h₁ h₂ h₃ h₄ c

end Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
