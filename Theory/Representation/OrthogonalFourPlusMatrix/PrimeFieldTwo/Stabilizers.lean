module

public import Theory.Representation.OrthogonalFourPlusMatrix.Action
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Singular point stabilizers over the field of two elements

For the literal left-right determinant action, nonzero singular points have
stabilizers of order four, while nonsingular points have stabilizers of order
six. Two singular points with nonzero polar pairing have a common hyperbolic
frame. Their stabilizers generate the whole ordered pair of special linear
groups: in the standard frame every element is a product from the first,
second, and first stabilizers.

The three small finite calculations below are checked by kernel reduction on
the actual matrices. Subsequent arguments use their structural interfaces.
Source: Aschbacher–Smith, G.2.6, printed p.336.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.PrimeFieldTwo
open Matrix Subgroup

abbrev M := Mat (F := ZMod 2)
abbrev P := PairSL (F := ZMod 2)

/-- Stabilizer in the literal determinant representation. -/
def stabilizer (X : M) : Subgroup P :=
  (MulAction.stabilizer (M ≃ₗ[ZMod 2] M) X).comap matrixHom

theorem mem_stabilizer (a : P) (X : M) :
    a ∈ stabilizer X ↔ matrixAction a X = X := Iff.rfl

/-- The inverse-free equation used by the finite calculations. -/
theorem action_eq_iff (a : P) (X Y : M) :
    matrixAction a X = Y ↔ a.1.val * X = Y * a.2.val := by
  change a.1.val * X * a.2⁻¹.val = Y ↔ _
  constructor
  · intro h
    have he := congrArg (fun Z : M => Z * a.2.val) h
    simpa only [mul_assoc, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
      SpecialLinearGroup.coe_one, mul_one] using he
  · intro h
    rw [h, mul_assoc, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
      SpecialLinearGroup.coe_one, mul_one]

private theorem count_fixed : ∀ X : M, X ≠ 0 →
    (Finset.univ.filter (fun a : P => a.1.val * X = X * a.2.val)).card =
      if X.det = 0 then 4 else 6 := by
  decide +kernel

/-- Both orbits of nonzero vectors, distinguished by their determinant. -/
theorem stabilizer_card (X : M) (hX : X ≠ 0) :
    Nat.card (stabilizer X) = if X.det = 0 then 4 else 6 := by
  let e : stabilizer X ≃ {a : P // a.1.val * X = X * a.2.val} :=
    Equiv.subtypeEquivRight (fun a => (mem_stabilizer a X).trans (action_eq_iff a X X))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact count_fixed X hX

/-- The two standard opposite singular points. -/
def firstPoint : M := !![1, 0; 0, 0]
def secondPoint : M := !![0, 0; 0, 1]

private theorem common_frame : ∀ X Y : M,
    X.det = 0 → Y.det = 0 → (X + Y).det ≠ 0 →
    ∃ a : P, a.1.val * firstPoint = X * a.2.val ∧
      a.1.val * secondPoint = Y * a.2.val := by
  decide +kernel

private theorem standard_words : ∀ a : P,
    ∃ u : P, u.1.val * firstPoint = firstPoint * u.2.val ∧
    ∃ v : P, v.1.val * secondPoint = secondPoint * v.2.val ∧
    ∃ w : P, w.1.val * firstPoint = firstPoint * w.2.val ∧ a = u * v * w := by
  decide +kernel

/-- Conjugation carries the actual stabilizer to that of the translated point. -/
theorem stabilizer_action (a : P) (X : M) :
    stabilizer (matrixAction a X) = (stabilizer X).map (MulAut.conj a).toMonoidHom := by
  let : MulAction P M := MulAction.compHom M matrixHom
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj a X

/-- Opposite standard point stabilizers generate both ordered SL₂ factors. -/
theorem standard_stabilizers_generate : stabilizer firstPoint ⊔ stabilizer secondPoint = ⊤ := by
  apply eq_top_iff.mpr
  intro a _
  obtain ⟨u, hu, v, hv, w, hw, rfl⟩ := standard_words a
  exact mul_mem
    (mul_mem (mem_sup_left ((action_eq_iff u _ _).mpr hu))
      (mem_sup_right ((action_eq_iff v _ _).mpr hv)))
    (mem_sup_left ((action_eq_iff w _ _).mpr hw))

/-- Nonorthogonal singular point stabilizers generate the determinant group. -/
theorem singular_stabilizers_generate (X Y : M) (hX : X.det = 0) (hY : Y.det = 0)
    (hXY : (determinantForm (F := ZMod 2)).polarBilin X Y ≠ 0) :
    stabilizer X ⊔ stabilizer Y = ⊤ := by
  have hsum : (X + Y).det ≠ 0 := by
    simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      determinantForm_apply, hX, hY, sub_zero] using hXY
  obtain ⟨a, ha, hb⟩ := common_frame X Y hX hY hsum
  rw [← (action_eq_iff a firstPoint X).mpr ha,
    ← (action_eq_iff a secondPoint Y).mpr hb, stabilizer_action, stabilizer_action,
    ← Subgroup.map_sup, standard_stabilizers_generate]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj a).surjective

end ClassicalOrthogonal.FourPlusMatrix.PrimeFieldTwo
