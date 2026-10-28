module
public import Theory.Representation.ThreeWeightSquare
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-!
# Literal matrix formulas for the three-weight argument

Conjugation and conjugated inverse transpose supply actual equivalences to
the natural and contragredient representations. Scalar extension preserves
these formulas, so the square-one theorem applies over the original field.
Source: the odd degree-three cases of Aschbacher–Smith A.3.15 and 1.3.4.
-/
public section
noncomputable section
namespace Representation.ThreeWeightSquare
open Matrix
variable {E B : Type*} [Field E] [Group B]

private theorem natural_apply (g : GL (Fin 3) E) (v : Fin 3→E) :
    generalLinearNatural 3 g v=g.val *ᵥ v := rfl

/-- Matrix conjugation gives the literal natural representation equivalence. -/
def naturalEquiv (j : B→*GL (Fin 3) E) (α : MulAut B) (g : GL (Fin 3) E)
    (h : ∀b,j (α b)=g*j b*g⁻¹) :
    Representation.Equiv ((generalLinearNatural 3).comp (j.comp α.toMonoidHom))
      ((generalLinearNatural 3).comp j) :=
  Representation.Equiv.mk ((GeneralLinearGroup.toLin g⁻¹).toLinearEquiv) (by
    intro b
    apply LinearMap.ext
    intro v
    change generalLinearNatural 3 g⁻¹ (generalLinearNatural 3 (j (α b)) v)=
      generalLinearNatural 3 (j b) (generalLinearNatural 3 g⁻¹ v)
    rw [h]
    simp only [map_mul,Module.End.mul_apply]
    rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one]
    rfl)

/-- Conjugated inverse transpose gives the literal contragredient equivalence. -/
def dualEquiv (j : B→*GL (Fin 3) E) (α : MulAut B) (g : GL (Fin 3) E)
    (h : ∀b,(j (α b)).val=g.val*(j b).inv.transpose*g.inv) :
    Representation.Equiv ((generalLinearNatural 3).comp (j.comp α.toMonoidHom))
      (Representation.dual ((generalLinearNatural 3).comp j)) :=
  Representation.Equiv.mk (((GeneralLinearGroup.toLin g⁻¹).toLinearEquiv).trans
    (dotProductEquiv E (Fin 3))) (by
    intro b
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change (g.inv *ᵥ ((j (α b)).val *ᵥ v)) ⬝ᵥ w =
      (g.inv *ᵥ v) ⬝ᵥ ((j b⁻¹).val *ᵥ w)
    rw [h,map_inv]
    rw [mulVec_mulVec,← mul_assoc,← mul_assoc,g.inv_val,one_mul,← mulVec_mulVec]
    rw [dotProduct_mulVec,← vecMul_transpose]
    rfl)

/-- Exact linear-or-inverse-transpose matrix formulas suffice for the
nondefining degree-three square-action conclusion. -/
theorem matrix_square_eq_one [IsAlgClosed E] [IsMulCommutative B]
    (j : B→*GL (Fin 3) E) (hj : Function.Injective j)
    (horder : (Nat.card B:E)≠0) (α : MulAut B) (ha : ∃n:ℕ,α^(2^n)=1)
    (hform : ∃g:GL (Fin 3) E,
      (∀b,j (α b)=g*j b*g⁻¹) ∨
      (∀b,(j (α b)).val=g.val*(j b).inv.transpose*g.inv)) : α^2=1 := by
  apply square_eq_one_of_equiv_or_dual ((generalLinearNatural 3).comp j)
    ((generalLinearNatural_injective 3).comp hj) horder (by simp) α ha
  obtain ⟨g,h|h⟩ := hform
  · exact Or.inl ⟨naturalEquiv j α g h⟩
  · exact Or.inr ⟨dualEquiv j α g h⟩

/-- The same exact matrix criterion over the original field. -/
theorem matrix_square_eq_one_of_field [IsMulCommutative B]
    (j : B→*GL (Fin 3) E) (hj : Function.Injective j)
    (horder : (Nat.card B:E)≠0) (α : MulAut B) (ha : ∃n:ℕ,α^(2^n)=1)
    (hform : ∃g:GL (Fin 3) E,
      (∀b,j (α b)=g*j b*g⁻¹) ∨
      (∀b,(j (α b)).val=g.val*(j b).inv.transpose*g.inv)) : α^2=1 := by
  let F := AlgebraicClosure E
  let M := GeneralLinearGroup.map (algebraMap E F) (n := Fin 3)
  have hM : Function.Injective M := by
    intro x y h
    apply Units.ext
    ext i k
    exact (algebraMap E F).injective (congrArg (fun z:GL (Fin 3) F=>z.val i k) h)
  refine matrix_square_eq_one (M.comp j) (hM.comp hj) ?_ α ha ?_
  · intro he
    apply horder
    apply (algebraMap E F).injective
    simpa only [map_natCast,map_zero] using he
  · obtain ⟨g,h|h⟩ := hform
    · refine ⟨M g,Or.inl ?_⟩
      intro b
      change M (j (α b))=M g*M (j b)*(M g)⁻¹
      rw [h,map_mul,map_mul,map_inv]
    · refine ⟨M g,Or.inr ?_⟩
      intro b
      change ((j (α b)).val.map (algebraMap E F))=
        (g.val.map (algebraMap E F))*((j b).inv.map (algebraMap E F)).transpose*
          (g.inv.map (algebraMap E F))
      rw [h,Matrix.map_mul,Matrix.map_mul]
      rfl
end Representation.ThreeWeightSquare
