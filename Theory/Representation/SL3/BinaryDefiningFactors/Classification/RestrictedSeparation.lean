module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic.FinCases

/-!
# Separation of the four concrete SL₃ factors

The dimensions distinguish all factors except the natural action and its dual.
An explicit determinant-one matrix has natural trace zero and inverse trace
minus one, so those actions are inequivalent as well. This works for every
field embedding, even without finiteness or characteristic-two hypotheses.
It proves separation only, not irreducibility or completeness.

Source: GLS III, 2.8.10(c). The trace argument generalizes the binary case in
Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual.
-/

public section

set_option backward.isDefEq.respectTransparency false
open scoped MatrixGroups
namespace Representation.SL3.BinaryDefiningFactors

variable {F K : Type*} [Field F] [Field K]

private theorem natural_character (ι : F →+* K) (g : SL(3,F)) :
    (natural ι).character g = ι (Matrix.trace g.val) := by
  change LinearMap.trace K (Fin 3 → K) (Matrix.toLin' (g.val.map ι)) = _
  rw [Matrix.trace_toLin'_eq]
  simp [Matrix.trace, map_sum]

private def testElement : SL(3,F) :=
  ⟨!![0,0,1;1,0,1;0,1,0], by simp [Matrix.det_fin_three]⟩

private theorem testElement_inv : (testElement (F := F))⁻¹ =
    ⟨!![-1,1,0;0,0,1;1,0,0], by simp [Matrix.det_fin_three]⟩ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (!![0,0,1;1,0,1;0,1,0] : Matrix (Fin 3) (Fin 3) F) *
    !![-1,1,0;0,0,1;1,0,0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- Natural and contragredient actions are inequivalent over every extension field. -/
theorem natural_not_equiv_dual (ι : F →+* K) :
    ¬ Nonempty ((natural ι).Equiv (natural ι).dual) := by
  rintro ⟨e⟩
  have h := congrFun (Representation.char_iso e) (testElement (F := F))
  rw [Representation.char_dual, testElement_inv, natural_character, natural_character] at h
  simp [testElement, Matrix.trace_fin_three] at h

/-- An equivalence between two concrete restricted factors identifies their labels. -/
theorem factorRep_equiv_imp_eq (ι : F →+* K) (a b : Factor)
    (e : (factorRep ι a).Equiv (factorRep ι b)) : a = b := by
  have hd := e.toLinearEquiv.finrank_eq
  rw [finrank_space, finrank_space] at hd
  cases a <;> cases b <;> simp_all [Factor.dimension]
  · exact (natural_not_equiv_dual ι ⟨e⟩).elim
  · exact (natural_not_equiv_dual ι ⟨e.symm⟩).elim

/-- The four labels classify their four concrete factor actions without repetitions. -/
theorem factorRep_equiv_iff (ι : F →+* K) (a b : Factor) :
    Nonempty ((factorRep ι a).Equiv (factorRep ι b)) ↔ a = b := by
  constructor
  · rintro ⟨e⟩
    exact factorRep_equiv_imp_eq ι a b e
  · rintro rfl
    exact ⟨Representation.Equiv.refl _⟩

end Representation.SL3.BinaryDefiningFactors
