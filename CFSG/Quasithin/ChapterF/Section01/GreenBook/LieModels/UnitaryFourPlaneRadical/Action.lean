module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.Action
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneRadical
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneBlock.Defs

/-!
# Literal action of the unitary-four plane local on its Hermitian kernel

The entire local factor acts on its actual restriction kernel by the finite
Hermitian action. The theory-level calculation applies to arbitrary local
elements, and coefficient transport turns its A X A† formula into
`FiniteModel.action`. The same identity descends along `L2ProjectIso`, using
the published restriction map and the compatible kernel isomorphism.

Both the parametrization and its inverse are equivariant, and the inverse
formulas display the literal two-by-two matrix action. All results hold for
every positive n, including n = 1. No identification with the two-core,
surjectivity of restriction, or Levi section is assumed.

Source: Aschbacher--Smith F.1.12(I)(6), `refs/quasithin.pdf`, printed pp.263–264.
These are the conjugation identities for the Ω₄⁻ block; identification of the
kernel with the two-core and the quotient remain with the assembly module.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Matrix
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
open Representation.OrthogonalFourMinus
variable (n : ℕ) (hn : 1 ≤ n)

/-- Coefficient transport intertwines the actual Hermitian congruence actions. -/
theorem planeHermitianEquiv_congruence [NeZero n]
    (A : SpecialLinearGroup (Fin 2) (MatrixField n))
    (X : hermitianMatrices (MatrixField n) (fieldConj n)) :
    planeHermitianEquiv n
      (hermitianCongruence (MatrixField n) (fieldConj n) (fieldConj_involutive n hn) A X) =
      FiniteModel.action n (planeSL2Equiv n A) (planeHermitianEquiv n X) := by
  apply Subtype.ext
  exact (planeHermitianEquiv_action_val n A X).symm

/-- Inverse coefficient transport of the finite Hermitian action. -/
theorem planeHermitianEquiv_symm_action [NeZero n]
    (A : SpecialLinearGroup (Fin 2) (MatrixField n)) (X : FiniteModel.Space n) :
    (planeHermitianEquiv n).symm (FiniteModel.action n (planeSL2Equiv n A) X) =
      hermitianCongruence (MatrixField n) (fieldConj n) (fieldConj_involutive n hn) A
        ((planeHermitianEquiv n).symm X) := by
  apply (planeHermitianEquiv n).injective
  rw [AddEquiv.apply_symm_apply, planeHermitianEquiv_congruence n hn, AddEquiv.apply_symm_apply]

/-- The full matrix local acts on its entire kernel by the finite Hermitian action. -/
theorem L2MatrixRadicalEquiv_conj [NeZero n] (g : L2Matrix n hn)
    (X : Multiplicative (FiniteModel.Space n)) :
    MulAut.conjNormal g (L2MatrixRadicalEquiv n hn X) =
      L2MatrixRadicalEquiv n hn (Multiplicative.ofAdd
        (FiniteModel.action n (planeSL2Equiv n (L2MatrixRestriction n hn g)) X.toAdd)) := by
  let g' : localFactor
      (MatrixField n) (form
        (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)) := g
  apply Subtype.ext
  apply Subtype.ext
  change g'.val * unipotentSU (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)
      ((planeHermitianEquiv n).symm X.toAdd) * g'.val⁻¹ =
    unipotentSU (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)
      ((planeHermitianEquiv n).symm
        (FiniteModel.action n (planeSL2Equiv n (L2MatrixRestriction n hn g)) X.toAdd))
  rw [unipotentSU_conj (MatrixField n) (fieldConj n) (fieldConj_involutive n hn) g',
    planeHermitianEquiv_symm_action n hn]
  rfl

/-- Projectivization intertwines literal conjugation inside the two kernels. -/
theorem L2RadicalProjectIso_conj (g : L2Matrix n hn) (u : L2MatrixRadical n hn) :
    L2RadicalProjectIso n hn (MulAut.conjNormal g u) =
      MulAut.conjNormal (L2ProjectIso n hn g) (L2RadicalProjectIso n hn u) := by
  apply Subtype.ext
  change L2ProjectIso n hn (g * u.val * g⁻¹) =
    L2ProjectIso n hn g * L2ProjectIso n hn u.val * (L2ProjectIso n hn g)⁻¹
  rw [map_mul, map_mul, map_inv]

/-- The arbitrary-element formula inside the actual projective restriction kernel. -/
theorem L2RadicalEquiv_conj [NeZero n] (g : L2 n hn)
    (X : Multiplicative (FiniteModel.Space n)) :
    MulAut.conjNormal g (L2RadicalEquiv n hn X) =
      L2RadicalEquiv n hn (Multiplicative.ofAdd
        (FiniteModel.action n (planeSL2Equiv n (L2Restriction n hn g)) X.toAdd)) := by
  obtain ⟨g, rfl⟩ := (L2ProjectIso n hn).surjective g
  change MulAut.conjNormal (L2ProjectIso n hn g)
    (L2RadicalProjectIso n hn (L2MatrixRadicalEquiv n hn X)) =
    L2RadicalProjectIso n hn (L2MatrixRadicalEquiv n hn (Multiplicative.ofAdd
      (FiniteModel.action n (planeSL2Equiv n (L2Restriction n hn (L2ProjectIso n hn g))) X.toAdd)))
  rw [← L2RadicalProjectIso_conj, L2MatrixRadicalEquiv_conj, L2Restriction_project]

/-- Coordinates of the conjugate of any matrix-kernel element. -/
theorem L2MatrixRadicalEquiv_symm_conj [NeZero n]
    (g : L2Matrix n hn) (u : L2MatrixRadical n hn) :
    (L2MatrixRadicalEquiv n hn).symm (MulAut.conjNormal g u) =
      Multiplicative.ofAdd (FiniteModel.action n
        (planeSL2Equiv n (L2MatrixRestriction n hn g)) ((L2MatrixRadicalEquiv n hn).symm u).toAdd) := by
  obtain ⟨X, rfl⟩ := (L2MatrixRadicalEquiv n hn).surjective u
  rw [L2MatrixRadicalEquiv_conj, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

/-- Coordinates of the conjugate of any projective-kernel element. -/
theorem L2RadicalEquiv_symm_conj [NeZero n] (g : L2 n hn) (u : L2Radical n hn) :
    (L2RadicalEquiv n hn).symm (MulAut.conjNormal g u) =
      Multiplicative.ofAdd (FiniteModel.action n
        (planeSL2Equiv n (L2Restriction n hn g)) ((L2RadicalEquiv n hn).symm u).toAdd) := by
  obtain ⟨X, rfl⟩ := (L2RadicalEquiv n hn).surjective u
  rw [L2RadicalEquiv_conj, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

/-- Literal A X A† formula for coordinates of conjugation in the matrix kernel. -/
theorem L2MatrixRadicalEquiv_symm_conj_val [NeZero n]
    (g : L2Matrix n hn) (u : L2MatrixRadical n hn) :
    ((L2MatrixRadicalEquiv n hn).symm (MulAut.conjNormal g u)).toAdd.val =
      (planeSL2Equiv n (L2MatrixRestriction n hn g)).val *
        ((L2MatrixRadicalEquiv n hn).symm u).toAdd.val *
          adjoint (FiniteModel.conjugation n) (planeSL2Equiv n (L2MatrixRestriction n hn g)).val := by
  rw [L2MatrixRadicalEquiv_symm_conj]
  rfl

/-- Literal A X A† formula for coordinates of conjugation in the projective kernel. -/
theorem L2RadicalEquiv_symm_conj_val [NeZero n]
    (g : L2 n hn) (u : L2Radical n hn) :
    ((L2RadicalEquiv n hn).symm (MulAut.conjNormal g u)).toAdd.val =
      (planeSL2Equiv n (L2Restriction n hn g)).val *
        ((L2RadicalEquiv n hn).symm u).toAdd.val *
          adjoint (FiniteModel.conjugation n) (planeSL2Equiv n (L2Restriction n hn g)).val := by
  rw [L2RadicalEquiv_symm_conj]
  rfl

/-- The same formula as a group equality in the actual matrix local. -/
theorem L2Matrix_conj_unipotent [NeZero n] (g : L2Matrix n hn)
    (X : Multiplicative (FiniteModel.Space n)) :
    g * (L2MatrixRadicalEquiv n hn X).val * g⁻¹ =
      (L2MatrixRadicalEquiv n hn (Multiplicative.ofAdd
        (FiniteModel.action n (planeSL2Equiv n (L2MatrixRestriction n hn g)) X.toAdd))).val :=
  congrArg Subtype.val (L2MatrixRadicalEquiv_conj n hn g X)

/-- The same formula as a group equality in the actual projective local. -/
theorem L2_conj_unipotent [NeZero n] (g : L2 n hn)
    (X : Multiplicative (FiniteModel.Space n)) :
    g * (L2RadicalEquiv n hn X).val * g⁻¹ =
      (L2RadicalEquiv n hn (Multiplicative.ofAdd
        (FiniteModel.action n (planeSL2Equiv n (L2Restriction n hn g)) X.toAdd))).val :=
  congrArg Subtype.val (L2RadicalEquiv_conj n hn g X)

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
