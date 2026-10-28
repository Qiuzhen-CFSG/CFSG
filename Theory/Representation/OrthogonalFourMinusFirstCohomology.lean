module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.TensorVanishing

/-!
# First cohomology of the four-dimensional minus-type orthogonal module

For every positive `n`, the finite Hermitian matrix model over `GF(2^(2n))`
has zero first cohomology. Its defining field is the actual Frobenius fixed
field of order `2^n`; the space has dimension four, its determinant form is
nonsingular of Witt index one, and its SL₂ action is faithful. These geometric
and action facts are re-exported from `FiniteModel`.

The ambient twisted tensor calculation makes every cocycle principal and
proves that there are no fixed vectors. Hermitian descent then forces the
unique principal vector of a Hermitian-valued cocycle to be Hermitian. Thus
both hypotheses of the descent theorem are discharged here, including `n = 1`.
Scalar restriction gives the same vanishing over F₂ on a space of dimension
`4 * n`. The canonical SL₂-to-PSL₂ equivalence transports the result to the
actual projective group, with its action identified with the Hermitian image.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma I.1.6(3), printed p.408 (PDF p.419), citing
Jones--Parshall [JP76]. The source's vanishing assertion is
`finrank_H1_binaryPSL2Action`. The additional A₅ identification and projectivity
clause are separate from this uniform cohomology calculation.
-/

@[expose] public noncomputable section

namespace Representation.OrthogonalFourMinus.FiniteModel

open OneCohomology

variable (n : ℕ) [NeZero n]

/-- Every cocycle of the actual four-dimensional Hermitian action is principal. -/
theorem action_principal_surjective : Function.Surjective (principal (action n)) :=
  action_principal_surjective_of_tensor n
    (tensorAction_frobenius_fixed_eq_bot n (Nat.pos_of_ne_zero (NeZero.ne n)))
    (tensorAction_frobenius_principal_surjective n (Nat.pos_of_ne_zero (NeZero.ne n)))

/-- First cohomology of the Hermitian action is the zero module. -/
theorem action_H1_subsingleton : Subsingleton (H1 (action n)) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  exact LinearMap.range_eq_top.mpr (action_principal_surjective n)

/-- Vanishing over the defining field of order `2^n`. -/
theorem finrank_H1_action : Module.finrank (fixedField n) (H1 (action n)) = 0 := by
  let := action_H1_subsingleton n
  exact Module.finrank_zero_of_subsingleton

-- Use the inherited F₂-module structure, so the scalar tower agrees with
-- the one already present on the Hermitian subspace of matrices.
local instance : Algebra (ZMod 2) (fixedField n) :=
  ZMod.algebraOfModule 2 (fixedField n)

/-- The same Hermitian SL₂ action, restricted to its binary prime field. -/
def binaryAction :
    Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) (Field n)) (Space n) :=
  restrictScalars (k := ZMod 2) (action n)

@[simp] theorem binaryAction_apply
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    binaryAction n A X = action n A X := rfl

/-- Scalar restriction leaves every Hermitian cocycle principal. -/
theorem binaryAction_principal_surjective :
    Function.Surjective (principal (binaryAction n)) := by
  intro f
  obtain ⟨v, hv⟩ := action_principal_surjective n
    (cocyclesRestrictEquiv (k := ZMod 2) (action n) f)
  exact ⟨v, (cocyclesRestrictEquiv (k := ZMod 2) (action n)).injective hv⟩

/-- First cohomology remains zero after restriction to F₂. -/
theorem binaryAction_H1_subsingleton : Subsingleton (H1 (binaryAction n)) := by
  let := action_H1_subsingleton n
  exact (H1RestrictEquiv (k := ZMod 2) (action n)).injective.subsingleton

/-- The binary first-cohomology dimension of the Hermitian SL₂ action is zero. -/
theorem finrank_H1_binaryAction : Module.finrank (ZMod 2) (H1 (binaryAction n)) = 0 := by
  let := binaryAction_H1_subsingleton n
  exact Module.finrank_zero_of_subsingleton

/-- The defining field has degree `n` over F₂. -/
theorem finrank_binary_fixedField : Module.finrank (ZMod 2) (fixedField n) = n := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  exact (FiniteField.pow_finrank_eq_natCard 2 (fixedField n)).trans (card_fixedField n)

/-- The orthogonal module has binary dimension `4 * n`, including four at `n = 1`. -/
theorem finrank_binary_space : Module.finrank (ZMod 2) (Space n) = 4 * n := by
  rw [← Module.finrank_mul_finrank (ZMod 2) (fixedField n),
    finrank_binary_fixedField, finrank_space, Nat.mul_comm]

/-- The Hermitian action of PSL₂ through its canonical characteristic-two identification. -/
def psl2Action : Representation (fixedField n)
    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field n)) (Space n) :=
  (action n).comp (sl2EquivPSL2 n).symm.toMonoidHom

/-- A projective class acts by the original Hermitian matrix congruence. -/
@[simp] theorem psl2Action_mk_apply
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    psl2Action n (QuotientGroup.mk A) X = action n A X := by
  change action n ((sl2EquivPSL2 n).symm (QuotientGroup.mk A)) X = _
  rw [← sl2EquivPSL2_apply n A, MulEquiv.symm_apply_apply]

/-- The projective action agrees with the natural action of the actual Hermitian image. -/
theorem psl2Action_apply
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    psl2Action n g X = psl2EquivActionImage n g • X :=
  (sl2EquivActionImage_smul n ((sl2EquivPSL2 n).symm g) X).symm

/-- The canonical group identification transports vanishing to PSL₂. -/
theorem psl2Action_H1_subsingleton : Subsingleton (H1 (psl2Action n)) := by
  let := action_H1_subsingleton n
  exact (H1Congr (action n) (psl2Action n) (sl2EquivPSL2 n)
    (LinearEquiv.refl (fixedField n) (Space n))
    (fun A X => (psl2Action_mk_apply n A X).symm)).symm.injective.subsingleton

/-- Every cocycle of the actual Hermitian PSL₂ action is principal. -/
theorem psl2Action_principal_surjective : Function.Surjective (principal (psl2Action n)) :=
  LinearMap.range_eq_top.mp
    (Submodule.Quotient.subsingleton_iff.mp (psl2Action_H1_subsingleton n))

/-- The defining-field first-cohomology dimension of the PSL₂ action is zero. -/
theorem finrank_H1_psl2Action : Module.finrank (fixedField n) (H1 (psl2Action n)) = 0 := by
  let := psl2Action_H1_subsingleton n
  exact Module.finrank_zero_of_subsingleton

/-- The source's binary orthogonal PSL₂ module. -/
def binaryPSL2Action : Representation (ZMod 2)
    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field n)) (Space n) :=
  restrictScalars (k := ZMod 2) (psl2Action n)

/-- Restricting scalars preserves the matrix-action formula. -/
@[simp] theorem binaryPSL2Action_mk_apply
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    binaryPSL2Action n (QuotientGroup.mk A) X = action n A X :=
  psl2Action_mk_apply n A X

/-- The binary first cohomology of the actual orthogonal PSL₂ module is zero. -/
theorem binaryPSL2Action_H1_subsingleton : Subsingleton (H1 (binaryPSL2Action n)) := by
  let := psl2Action_H1_subsingleton n
  exact (H1RestrictEquiv (k := ZMod 2) (psl2Action n)).injective.subsingleton

/-- Every binary cocycle of the actual orthogonal PSL₂ module is principal. -/
theorem binaryPSL2Action_principal_surjective :
    Function.Surjective (principal (binaryPSL2Action n)) :=
  LinearMap.range_eq_top.mp
    (Submodule.Quotient.subsingleton_iff.mp (binaryPSL2Action_H1_subsingleton n))

/-- Aschbacher--Smith I.1.6(3), vanishing clause, for every positive `n`. -/
theorem finrank_H1_binaryPSL2Action :
    Module.finrank (ZMod 2) (H1 (binaryPSL2Action n)) = 0 := by
  let := binaryPSL2Action_H1_subsingleton n
  exact Module.finrank_zero_of_subsingleton

end Representation.OrthogonalFourMinus.FiniteModel
