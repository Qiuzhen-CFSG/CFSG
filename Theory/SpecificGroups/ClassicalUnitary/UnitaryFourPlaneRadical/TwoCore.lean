module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.PGroupCore
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Two-core recognition for the unitary plane restriction

The two-core of SL₂ over any finite characteristic-two field is trivial:
normality places it in the upper unipotent Sylow and in its opposite conjugate,
whose intersection is trivial. Therefore a surjective plane restriction has
exactly its Hermitian kernel as two-core. The quotient equivalence is the first
isomorphism theorem, and its value on a coset is the original restriction.

Source: the local quotient calculation underlying Aschbacher--Smith
F.1.12(I)(6), printed pp.263–264. Surjectivity is an explicit remaining premise;
no Levi section or source block theorem is assumed or asserted here.
-/

open Matrix
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

private def swapSL2 : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0,1;1,0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

omit [Finite F] in
private theorem swapSL2_inv : (swapSL2 F)⁻¹ = swapSL2 F := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) F) * !![0,1;1,0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- A normal two-subgroup lies in both opposite unipotent Sylows and is trivial. -/
theorem sl2_twoCore_eq_bot : pCore 2 (SpecialLinearGroup (Fin 2) F) = ⊥ := by
  have hle : pCore 2 (SpecialLinearGroup (Fin 2) F) ≤ SpecialLinearGroup.upperUnipotent F :=
    pCore_isPGroup.le_sylow_of_normal (SpecialLinearGroup.upperUnipotentSylow F 2)
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  obtain ⟨t,rfl⟩ := (SpecialLinearGroup.mem_upperUnipotent F g).mp (hle hg)
  have hc := (inferInstance : (pCore 2 (SpecialLinearGroup (Fin 2) F)).Normal).conj_mem
    _ hg (swapSL2 F)
  obtain ⟨s,hs⟩ := (SpecialLinearGroup.mem_upperUnipotent F _).mp (hle hc)
  have he := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.val 1 0) hs
  rw [swapSL2_inv] at he
  change (Matrix.transvection (0 : Fin 2) 1 s) 1 0 =
    ((!![0,1;1,0] : Matrix (Fin 2) (Fin 2) F) *
      Matrix.transvection (0 : Fin 2) 1 t * !![0,1;1,0] : Matrix (Fin 2) (Fin 2) F) 1 0 at he
  have ht : t = 0 := by
    simpa [Matrix.transvection, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using he.symm
  rw [ht, SpecialLinearGroup.transvection_coeff_zero]

open UnitaryFourFlag UnitaryFourPlaneLocal
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

/-- Once restriction is surjective, its proved elementary kernel is exactly the two-core. -/
theorem radical_eq_twoCore_of_surjective
    (hsurj : Function.Surjective (factorRestriction F (form F σ hσ))) :
    radical F σ hσ = pCore 2 (localFactor F (form F σ hσ)) := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 _⟩
  · let f := factorRestriction F (form F σ hσ)
    have : ((pCore 2 (localFactor F (form F σ hσ))).map f).Normal :=
      Subgroup.Normal.map inferInstance f hsurj
    have hle : (pCore 2 (localFactor F (form F σ hσ))).map f ≤
        pCore 2 (SpecialLinearGroup (Fin 2) F) :=
      le_sSup ⟨inferInstance, pCore_isPGroup.map f⟩
    rw [sl2_twoCore_eq_bot] at hle
    intro g hg
    exact Subgroup.mem_bot.mp (hle ⟨g,hg,rfl⟩)

/-- The first isomorphism theorem on the actual two-core, conditional only on surjectivity. -/
def quotientEquivSL2OfSurjective
    (hsurj : Function.Surjective (factorRestriction F (form F σ hσ))) :
    (localFactor F (form F σ hσ) ⧸ pCore 2 (localFactor F (form F σ hσ))) ≃*
      SpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.quotientMulEquivOfEq
    (radical_eq_twoCore_of_surjective F σ hσ hsurj).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (factorRestriction F (form F σ hσ)) hsurj)

@[simp] theorem quotientEquivSL2OfSurjective_mk
    (hsurj : Function.Surjective (factorRestriction F (form F σ hσ)))
    (g : localFactor F (form F σ hσ)) :
    quotientEquivSL2OfSurjective F σ hσ hsurj (QuotientGroup.mk g) =
      factorRestriction F (form F σ hσ) g := rfl

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
