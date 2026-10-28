module

public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinaryGeometry

/-!
# Faithfulness on the isotropic lines of GF(4)⁶

A matrix fixing every isotropic line fixes the lines of `eᵢ + c eⱼ`
for every nonzero scalar `c`. Two distinct nonzero choices force its
off-diagonal entries to vanish. Fixing the lines of `eᵢ + eⱼ` then makes
all diagonal entries equal. Such a scalar matrix is trivial in PGL.

This supplies the geometric faithfulness needed in the Fi22 fixed-point
comparison for GLS3 Table 5.3t (`refs/KGroup/GLS3/Chapter5(sec3-).tex`).
It uses only the specified matrix model, without any Fischer identification.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups LinearAlgebra.Projectivization
namespace Theory.SpecificGroups.U6Two

private theorem exists_field_ne_zero_one : ∃ c : Field, c ≠ 0 ∧ c ≠ 1 := by
  classical
  let := Fintype.ofFinite Field
  by_contra h
  push Not at h
  have hs : (Finset.univ : Finset Field) ⊆ {0, 1} := by
    intro c _
    by_cases hc : c = 0
    · simp [hc]
    · simp [h c hc]
  have hc := Finset.card_le_card hs
  have hcard : Fintype.card Field = 4 := by
    simpa only [Nat.card_eq_fintype_card] using field_card
  simp [hcard] at hc

private noncomputable def pairVector (i j : Fin 6) (c : Field) : Vector :=
  Pi.single i 1 + Pi.single j c

private theorem pairVector_ne_zero (i j : Fin 6) (hij : i ≠ j) (c : Field) :
    pairVector i j c ≠ 0 := by
  intro h
  have := congrFun h i
  simp [pairVector, hij] at this

private theorem pairVector_norm (i j : Fin 6) (hij : i ≠ j) (c : Field) (hc : c ≠ 0) :
    hermitianNorm (pairVector i j c) = 0 := by
  simp [hermitianNorm, pairVector, dotProduct_add, dotProduct_single,
    Pi.single_apply, hij, hij.symm, conjugation_mul_self_of_ne_zero c hc, CharTwo.add_self_eq_zero]

private theorem mulVec_pairVector (A : Matrix (Fin 6) (Fin 6) Field)
    (i j k : Fin 6) (c : Field) :
    (A *ᵥ pairVector i j c) k = A k i + c * A k j := by
  simp [pairVector, mulVec_add, mulVec_single]

private theorem scalar_of_fixes_isotropic (A : GL (Fin 6) Field)
    (hfix : ∀ v : Vector, ∀ hv : v ≠ 0, hermitianNorm v = 0 →
      Projectivization.mk Field (A • v) ((smul_ne_zero_iff_ne A).mpr hv) =
      Projectivization.mk Field v hv) :
    ∃ c : Field, Matrix.scalar (Fin 6) c = A.val := by
  have hpair (i j : Fin 6) (hij : i ≠ j) (c : Field) (hc : c ≠ 0) :
      ∃ d : Field, ∀ k : Fin 6,
        A.val k i + c * A.val k j = d * pairVector i j c k := by
    obtain ⟨d, hd⟩ := (Projectivization.mk_eq_mk_iff' Field _ _ _ _).mp
      (hfix (pairVector i j c) (pairVector_ne_zero i j hij c) (pairVector_norm i j hij c hc))
    refine ⟨d, fun k => ?_⟩
    have hdk := congrFun hd k
    change d * pairVector i j c k = (A.val *ᵥ pairVector i j c) k at hdk
    rw [mulVec_pairVector] at hdk
    exact hdk.symm
  obtain ⟨w, hw0, hw1⟩ := exists_field_ne_zero_one
  have hoff (k i : Fin 6) (hki : k ≠ i) : A.val k i = 0 := by
    obtain ⟨j, hji, hjk⟩ : ∃ j : Fin 6, j ≠ i ∧ j ≠ k := by
      fin_cases i <;> fin_cases k <;> decide
    obtain ⟨d, hd⟩ := hpair i j hji.symm 1 one_ne_zero
    obtain ⟨e, he⟩ := hpair i j hji.symm w hw0
    have h1 := hd k
    have hw := he k
    simp [pairVector, hki, Ne.symm hjk] at h1 hw
    have hz : (w - 1) * A.val k j = 0 := by linear_combination hw - h1
    have hj0 : A.val k j = 0 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hw1)
    simpa [hj0] using h1
  have hdiag (i j : Fin 6) : A.val i i = A.val j j := by
    by_cases hij : i = j
    · subst j; rfl
    obtain ⟨d, hd⟩ := hpair i j hij 1 one_ne_zero
    have hi := hd i
    have hj := hd j
    simp [pairVector, Ne.symm hij, hoff i j hij] at hi
    simp [pairVector, hij, hoff j i (Ne.symm hij)] at hj
    exact hi.trans hj.symm
  refine ⟨A.val 0 0, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using hdiag 0 i
  · simp [Matrix.scalar_apply, hij, hoff i j hij]

/-- The projective unitary action on isotropic lines is faithful. -/
theorem isotropicAction_injective : Function.Injective isotropicAction := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨A, rfl⟩ := project_surjective g
  have hfix : ∀ v : Vector, ∀ hv : v ≠ 0, hermitianNorm v = 0 →
      Projectivization.mk Field (A.val • v) ((smul_ne_zero_iff_ne A.val).mpr hv) =
      Projectivization.mk Field v hv := by
    intro v hv hi
    have h := congrArg (fun e : Equiv.Perm IsotropicPoint =>
      (e (mkIsotropicPoint v hv hi)).val) hg
    rw [isotropicAction_project_mk] at h
    exact h
  obtain ⟨c, hc⟩ := scalar_of_fixes_isotropic A.val hfix
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk A.val = 1
  exact Matrix.ProjGenLinGroup.mk_eq_one.mpr
    (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨c, hc⟩)

/-- Adjoining a fixed point preserves faithfulness. -/
theorem isotropicActionWithSingleton_injective :
    Function.Injective isotropicActionWithSingleton :=
  isotropicActionWithSingleton_injective_iff.mpr isotropicAction_injective

end Theory.SpecificGroups.U6Two
