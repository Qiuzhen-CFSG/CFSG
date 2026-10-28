module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.Descent
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison.Transport
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.FormIsometry

/-!
# Quadratic coordinates for the minus-six norm model

The chosen minus form over an arbitrary field of order `2^n` is transported
semilinearly to the actual Frobenius fixed field. The existing coefficient
transport includes the Artin–Schreier shear correcting the independently
chosen anisotropic-plane parameters. The proved Hermitian determinant
isometry then changes one hyperbolic plane plus the anisotropic plane into
one hyperbolic plane plus the extension norm. Adjoining the other hyperbolic
plane yields the literal form in `MinusThreeComparison.Model`.

Conjugation by these coordinates identifies the full orthogonal groups and
intertwines their natural actions. This discharges the quadratic-transport
input of the minus-six/unitary-four assembly, without any unitary-action or
commutator-image hypothesis. The construction works for every positive `n`.

Sources: GLS3 §2.7 (`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith,
A.2.18, printed p.40, and Theorem D, printed pp.1078–1079
(`refs/quasithin.pdf`). The anisotropic-plane root construction is reused
from `OrthogonalFourMinusHermitianEquiv.FormIsometry`.
-/

public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
open Representation.OrthogonalFourMinus
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable (n : ℕ) [NeZero n]

private def splitHyperbolic : Minus.Space (FixedField n) 2 ≃ₗ[FixedField n]
    (FixedField n × FixedField n) × Minus.Space (FixedField n) 1 where
  toFun v := (v.1 0, ((fun _ => v.1 1), v.2))
  invFun v := (![v.1, v.2.1 0], v.2.2)
  left_inv v := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  right_inv v := by
    refine Prod.ext ?_ ?_
    · rfl
    · apply Prod.ext
      · funext i
        fin_cases i
        rfl
      · rfl
  map_add' v w := rfl
  map_smul' c v := rfl

private def joinHyperbolic :
    ((FixedField n × FixedField n) × ((FixedField n × FixedField n) × Field n))
      ≃ₗ[FixedField n] Space n where
  toFun v := (![v.1, v.2.1], v.2.2)
  invFun v := (v.1 0, (v.1 1, v.2))
  left_inv v := rfl
  right_inv v := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  map_add' v w := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  map_smul' c v := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl

/-- The actual fixed-field coordinates, obtained by adjoining a hyperbolic plane
to the proved Hermitian determinant isometry. -/
def fixedFieldCoordinates : Minus.Space (FixedField n) 2 ≃ₗ[FixedField n] Space n :=
  (splitHyperbolic n).trans
    (((LinearEquiv.refl (FixedField n) (FixedField n × FixedField n)).prodCongr
      ((HermitianEquiv.hermitianMinusIsometry n).symm.toLinearEquiv.trans
        (FiniteModel.coordinates n))).trans (joinHyperbolic n))

/-- Explicit evaluation of the coordinate map in the published norm model. -/
theorem fixedFieldCoordinates_apply (v : Minus.Space (FixedField n) 2) :
    fixedFieldCoordinates n v =
      let w := FiniteModel.coordinates n
        ((HermitianEquiv.hermitianMinusIsometry n).symm ((fun _ => v.1 1), v.2))
      (![v.1 0, w.1], w.2) := by rfl

/-- The coordinate map preserves the full quadratic value, including the norm term. -/
@[simp] theorem form_fixedFieldCoordinates (v : Minus.Space (FixedField n) 2) :
    form n (fixedFieldCoordinates n v) = Minus.quadraticForm (FixedField n) 3 v := by
  let u : Minus.Space (FixedField n) 1 := ((fun _ => v.1 1), v.2)
  let w := FiniteModel.coordinates n ((HermitianEquiv.hermitianMinusIsometry n).symm u)
  have hw : w.1.1 * w.1.2 + FiniteModel.norm n w.2 =
      Minus.quadraticForm (FixedField n) 2 u := by
    have h := (HermitianEquiv.hermitianMinusIsometry n).symm.map_app u
    rw [← (FiniteModel.coordinates n).symm_apply_apply
      ((HermitianEquiv.hermitianMinusIsometry n).symm u), FiniteModel.form_coordinates] at h
    simpa only [CharTwo.sub_eq_add] using h
  rw [fixedFieldCoordinates_apply, form_apply]
  change (v.1 0).1 * (v.1 0).2 + w.1.1 * w.1.2 + FiniteModel.norm n w.2 = _
  rw [add_assoc, hw]
  simp [Minus.quadraticForm, Minus.form_apply, Fin.sum_univ_succ, u, add_assoc]

/-- A quadratic isometry from the chosen fixed-field minus-six form to the norm form. -/
def fixedFieldFormIsometry :
    (Minus.quadraticForm (FixedField n) 3).IsometryEquiv (form n) where
  toLinearEquiv := fixedFieldCoordinates n
  map_app' := form_fixedFieldCoordinates n

variable {F : Type} [_root_.Field F] [Finite F]

/-- Equality of field orders gives the coefficient isomorphism into the actual fixed field. -/
def coefficientEquiv (hcard : Nat.card F = 2 ^ n) : F ≃+* FixedField n := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (FixedField n) := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcard.trans (card_fixedField n).symm)

/-- The semilinear quadratic coordinates for the independently chosen minus form over `F`.
The field-transport shear respects its actual chosen anisotropic parameter. -/
def quadraticCoordinates (hcard : Nat.card F = 2 ^ n) :
    Minus.Space F 2 ≃ₛₗ[(coefficientEquiv n hcard : F →+* FixedField n)] Space n :=
  (MinusTwoComparison.minusSpaceEquiv (coefficientEquiv n hcard) 3).trans
    (fixedFieldFormIsometry n).toLinearEquiv

/-- Evaluation as coefficient transport, parameter correction, and norm coordinates. -/
theorem quadraticCoordinates_apply (hcard : Nat.card F = 2 ^ n)
    (v : Minus.Space F 2) :
    quadraticCoordinates n hcard v = fixedFieldCoordinates n
      (MinusTwoComparison.minusSpaceEquiv (coefficientEquiv n hcard) 3 v) := by rfl

/-- Exact quadratic-value preservation across the coefficient isomorphism. -/
@[simp] theorem form_quadraticCoordinates (hcard : Nat.card F = 2 ^ n)
    (v : Minus.Space F 2) :
    form n (quadraticCoordinates n hcard v) =
      coefficientEquiv n hcard (Minus.quadraticForm F 3 v) := by
  change form n (fixedFieldCoordinates n
    (MinusTwoComparison.minusSpaceEquiv (coefficientEquiv n hcard) 3 v)) = _
  rw [form_fixedFieldCoordinates, MinusTwoComparison.quadraticForm_minusSpaceEquiv]

/-- The required equivalence of the full orthogonal groups, induced by the actual
semilinear quadratic-space equivalence. -/
def fullOrthogonalEquiv (hcard : Nat.card F = 2 ^ n) :
    Minus.Orthogonal F (Minus.Space F 2) (Minus.quadraticForm F 3) ≃* FullOrthogonal n :=
  MinusTwoComparison.orthogonalSemilinearCongr (coefficientEquiv n hcard)
    (quadraticCoordinates n hcard) (form_quadraticCoordinates n hcard)

/-- The group comparison intertwines the natural actions on the displayed coordinates. -/
@[simp] theorem fullOrthogonalEquiv_apply (hcard : Nat.card F = 2 ^ n)
    (g : Minus.Orthogonal F (Minus.Space F 2) (Minus.quadraticForm F 3))
    (v : Minus.Space F 2) :
    (fullOrthogonalEquiv n hcard g).val (quadraticCoordinates n hcard v) =
      quadraticCoordinates n hcard (g.val v) :=
  MinusTwoComparison.orthogonalSemilinearCongr_apply (coefficientEquiv n hcard)
    (quadraticCoordinates n hcard) (form_quadraticCoordinates n hcard) g v

end ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
