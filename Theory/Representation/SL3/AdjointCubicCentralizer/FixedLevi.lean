module
public import Theory.Representation.SL3.AdjointCubicCentralizer.Projective
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Fixed sections of the two adjoint extensions

The determinant-twisted cubic fixes the lower-left column. Direct block
multiplication identifies the full action of the lower SL₂ on that column
with its natural representation. This is stronger than the fixed-space
dimension calculation and keeps the actual Levi inclusion.

For the ordinary adjoint extension, the trace blocks embed into the fixed
subgroup of any action whose generator has the marked diagonal action.
Over F₄ they supply 256 fixed elements. The nonblock source application
compares this with its bound of sixteen on original component-core sections.

Source: Aschbacher--Smith B.4.14, printed p.98, and the terminal argument
for 4.3.2, pp.618--619. These are calculations for specified extensions;
no extension recognition from the restricted SL₃ action is asserted.
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
namespace Representation.SL3.AdjointCubicCentralizer
noncomputable section
variable (F : Type*) [Field F]

/-- The lower Levi acts naturally on the column fixed by the twisted cubic. -/
theorem column_levi_action (g : SL(2,F)) (v : Fin 2 → F) :
    determinantTwist F (levi F g) (column F v) = column F (g.val.mulVec v) := by
  have hd : Matrix.det (levi F g).val = 1 := by
    change Matrix.det (block F 1 g.val) = 1
    have hg := g.property
    rw [Matrix.det_fin_two] at hg
    simpa [block,Matrix.det_fin_three] using hg
  change Matrix.det (levi F g).val •
    ((levi F g).val * column F v * (levi F g)⁻¹.val) = _
  rw [hd,one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [levi,block,column,Matrix.mul_apply,Matrix.mulVec,dotProduct,
      Fin.sum_univ_three,Fin.sum_univ_two]

private theorem column_reconstruct (ω : Fˣ) (hω : (ω : F) ≠ 1)
    (hω2 : (ω : F)^2 ≠ 1) (X : twistedFixedSpace F ω) :
    column F ![X.val 1 0,X.val 2 0] = X.val :=
  congrArg Subtype.val ((twistedFixedEquiv F ω hω hω2).symm_apply_apply X)

/-- The actual twisted cubic fixed space, invariant under the lower Levi. -/
def twistedFixedSubrepresentation (ω : Fˣ) (hω : (ω : F) ≠ 1)
    (hω2 : (ω : F)^2 ≠ 1) :
    Subrepresentation ((determinantTwist F).comp (levi F)) where
  toSubmodule := twistedFixedSpace F ω
  apply_mem_toSubmodule g X hX := by
    change determinantTwist F (levi F g) X ∈ twistedFixedSpace F ω
    have he : column F ![X 1 0,X 2 0] = X := column_reconstruct F ω hω hω2 ⟨X,hX⟩
    rw [←he,column_levi_action]
    exact column_mem_twistedFixedSpace F ω _

/-- Its full Levi action is the natural two-dimensional representation. -/
def twistedFixedRepresentationEquiv (ω : Fˣ) (hω : (ω : F) ≠ 1)
    (hω2 : (ω : F)^2 ≠ 1) :
    (twistedFixedSubrepresentation F ω hω hω2).toRepresentation.Equiv
      (Representation.specialLinearNatural (k := F) 2) :=
  .mk (twistedFixedEquiv F ω hω hω2) (by
    intro g
    apply LinearMap.ext
    intro X
    change ![(determinantTwist F (levi F g) X.val) 1 0,
      (determinantTwist F (levi F g) X.val) 2 0] =
        g.val.mulVec ![X.val 1 0,X.val 2 0]
    rw [←column_reconstruct F ω hω hω2 X,column_levi_action]
    ext i
    fin_cases i <;> rfl)

variable {A M : Type*} [Group A] [Group M] [Finite M] [MulDistribMulAction A M]

/-- An ordinary adjoint cubic action has at least 256 fixed elements over F₄.
The equivariant bijection and generator refer to the original action. -/
theorem fixed_card_ge_of_adjoint_generator [Finite F] (hF : Nat.card F = 4)
    (a : A) (hgen : Subgroup.zpowers a = ⊤) (ω : Fˣ)
    (e : M ≃ TraceZero F)
    (he : ∀ v, e (a • v) = projectiveAdjoint F
      (Matrix.ProjGenLinGroup.mk (diagonalUnit F ω)) (e v)) :
    256 ≤ Nat.card (FixedPoints.subgroup A M) := by
  let lift : Mat2 F → M := fun D => e.symm ⟨traceBlock F D,trace_traceBlock F D⟩
  have hfixed (D : Mat2 F) (x : A) : x • lift D = lift D := by
    have ha : a • lift D = lift D := by
      apply e.injective
      rw [he]
      change projectiveAdjoint F _ (e (e.symm _)) = e (e.symm _)
      rw [e.apply_symm_apply]
      apply Subtype.ext
      exact ((mem_fixedSpace_iff_fixed F ω (traceBlock F D)).mp
        (traceBlock_mem F ω D)).2
    have hh : (⊤ : Subgroup A) ≤ MulAction.stabilizer A (lift D) := by
      rw [←hgen]
      exact Subgroup.zpowers_le.mpr ha
    exact hh (Subgroup.mem_top x)
  let f : Mat2 F → FixedPoints.subgroup A M := fun D => ⟨lift D,hfixed D⟩
  have hi : Function.Injective f := by
    intro D E hDE
    have hh := congrArg (fun v : FixedPoints.subgroup A M => (e v.val).val) hDE
    change (e (e.symm _)).val = (e (e.symm _)).val at hh
    simp only [e.apply_symm_apply] at hh
    simpa only [lowerBlock_traceBlock] using congrArg (lowerBlock F) hh
  have hc := Nat.card_le_card_of_injective f hi
  have hcard : Nat.card (Mat2 F) = 256 := by
    change Nat.card (Fin 2 → Fin 2 → F) = 256
    rw [Nat.card_fun,Nat.card_fun,Nat.card_fin,hF]
    decide
  rwa [hcard] at hc
end
end Representation.SL3.AdjointCubicCentralizer
