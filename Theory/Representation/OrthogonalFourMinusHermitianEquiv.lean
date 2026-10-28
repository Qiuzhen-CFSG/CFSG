module

public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.OrthogonalAction
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.Transport
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.FormIsometry
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.CommutatorImage
public import Theory.Representation.OrthogonalNatural

/-!
# Assembly of the Hermitian identification with the minus Omega model

For every positive `n`, this module identifies SL₂ over GF(2^(2n)) with the
commutator subgroup of the full isometry group of the chosen four-dimensional
minus form over the Frobenius fixed field of order `2^n`. The quadratic
isometry `hermitianMinusIsometry` identifies the Hermitian determinant action
with the literal natural action, preserving the full quadratic form.

`FormIsometry` constructs the quadratic isometry using a root of the chosen
anisotropic-plane polynomial. `CommutatorImage` identifies the Hermitian SL₂
image with the full orthogonal commutator by classifying determinant isometries.
Conjugation by the quadratic isometry then gives `sl2EquivMinusOmega`; its
intertwining theorem has no additional isometry or image-containment premise.
The conditional assembly interfaces are retained for other choices of isometry.

This proves the exceptional equivariant identification used in
Aschbacher--Smith, C.1.30 and F.1.12(I)(6), printed pp.135 and 263, and stated
in I.1.6(3), printed p.408, including q = 2.
-/

@[expose] public noncomputable section

namespace Representation.OrthogonalFourMinus.HermitianEquiv
open FiniteModel
open ClassicalOrthogonal.Minus (Orthogonal Omega)
variable (n : ℕ) [NeZero n]

/-- The reverse containment makes the faithful homomorphism onto Omega. -/
def sl2EquivHermitianOmegaOfContainment
    (h : commutator (Orthogonal (fixedField n) (Space n) (form n)) ≤
      (orthogonalAction n).range) :
    Matrix.SpecialLinearGroup (Fin 2) (Field n) ≃*
      Omega (fixedField n) (Space n) (form n) :=
  MulEquiv.ofBijective (omegaAction n) ⟨omegaAction_injective n, by
    intro g
    obtain ⟨A, hA⟩ := h g.property
    exact ⟨A, Subtype.ext hA⟩⟩

@[simp] theorem sl2EquivHermitianOmegaOfContainment_apply
    (h : commutator (Orthogonal (fixedField n) (Space n) (form n)) ≤
      (orthogonalAction n).range)
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    (sl2EquivHermitianOmegaOfContainment n h A).val.val X = action n A X := rfl

/-- Conditional assembly with the existing chosen minus quadratic form. -/
def sl2EquivMinusOmegaOfIsometry
    (e : (form n).IsometryEquiv (ClassicalOrthogonal.Minus.quadraticForm (fixedField n) 2))
    (h : commutator (Orthogonal (fixedField n) (Space n) (form n)) ≤
      (orthogonalAction n).range) :
    Matrix.SpecialLinearGroup (Fin 2) (Field n) ≃*
      Omega (fixedField n) (ClassicalOrthogonal.Minus.Space (fixedField n) 1)
        (ClassicalOrthogonal.Minus.quadraticForm (fixedField n) 2) :=
  (sl2EquivHermitianOmegaOfContainment n h).trans (omegaCongr e)

/-- Equivariance refers to restriction of the actual quadratic isometries. -/
theorem sl2EquivMinusOmegaOfIsometry_intertwines
    (e : (form n).IsometryEquiv (ClassicalOrthogonal.Minus.quadraticForm (fixedField n) 2))
    (h : commutator (Orthogonal (fixedField n) (Space n) (form n)) ≤
      (orthogonalAction n).range)
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    ClassicalOrthogonal.subgroupNatural
      (Omega (fixedField n) (ClassicalOrthogonal.Minus.Space (fixedField n) 1)
        (ClassicalOrthogonal.Minus.quadraticForm (fixedField n) 2))
      (sl2EquivMinusOmegaOfIsometry n e h A) (e X) = e (action n A X) := by
  exact omegaCongr_apply e (sl2EquivHermitianOmegaOfContainment n h A) X

/-- The faithful Hermitian action identifies SL₂ with the full orthogonal
commutator subgroup, for every positive exponent, including `n = 1`. -/
def sl2EquivHermitianOmega :
    Matrix.SpecialLinearGroup (Fin 2) (Field n) ≃*
      Omega (fixedField n) (Space n) (form n) :=
  sl2EquivHermitianOmegaOfContainment n (commutator_le_range_orthogonalAction n)

@[simp] theorem sl2EquivHermitianOmega_apply
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    (sl2EquivHermitianOmega n A).val.val X = action n A X := rfl

/-- The exceptional identification SL₂(q²) ≃ Ω₄⁻(q), using the existing chosen
minus form over the field of order `q = 2^n`. Both geometric inputs are proved. -/
def sl2EquivMinusOmega :
    Matrix.SpecialLinearGroup (Fin 2) (Field n) ≃*
      Omega (fixedField n) (ClassicalOrthogonal.Minus.Space (fixedField n) 1)
        (ClassicalOrthogonal.Minus.quadraticForm (fixedField n) 2) :=
  sl2EquivMinusOmegaOfIsometry n (hermitianMinusIsometry n)
    (commutator_le_range_orthogonalAction n)

/-- The quadratic coordinate isometry intertwines the Hermitian congruence
action and the literal natural action of the chosen minus Omega model. -/
theorem sl2EquivMinusOmega_intertwines
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    ClassicalOrthogonal.subgroupNatural
      (Omega (fixedField n) (ClassicalOrthogonal.Minus.Space (fixedField n) 1)
        (ClassicalOrthogonal.Minus.quadraticForm (fixedField n) 2))
      (sl2EquivMinusOmega n A) (hermitianMinusIsometry n X) =
        hermitianMinusIsometry n (action n A X) :=
  sl2EquivMinusOmegaOfIsometry_intertwines n (hermitianMinusIsometry n)
    (commutator_le_range_orthogonalAction n) A X

end Representation.OrthogonalFourMinus.HermitianEquiv
