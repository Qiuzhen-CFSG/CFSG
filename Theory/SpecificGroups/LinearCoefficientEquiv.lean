module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Coefficient equivalences for special and projective special linear groups

A ring equivalence acts entrywise on special linear matrices. The inverse
coefficient map supplies the inverse group map. Since group isomorphisms
preserve centers, the equivalence descends to the projective quotients.
This works in every finite dimension and transports concrete finite-field
models without changing their mathematical group.

Source: the defining matrix and central-quotient constructions of SL and PSL.
-/

/-- Entrywise coefficient transport on special linear groups. -/
public noncomputable def Matrix.SpecialLinearGroup.ringEquiv
    {ι R S : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup ι R ≃* Matrix.SpecialLinearGroup ι S :=
  { Matrix.SpecialLinearGroup.map e.toRingHom with
    invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
    left_inv := by intro g; ext i j; exact e.symm_apply_apply (g i j)
    right_inv := by intro g; ext i j; exact e.apply_symm_apply (g i j) }

/-- Coefficient transport descends to the projective special linear quotient. -/
public noncomputable def Matrix.ProjectiveSpecialLinearGroup.ringEquiv
    {ι R S : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.ProjectiveSpecialLinearGroup ι R ≃* Matrix.ProjectiveSpecialLinearGroup ι S := by
  let eSL : Matrix.SpecialLinearGroup ι R ≃* Matrix.SpecialLinearGroup ι S :=
    Matrix.SpecialLinearGroup.ringEquiv e
  apply QuotientGroup.congr _ _ eSL
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Subgroup.centerCongr eSL ⟨x, hx⟩).property
  · intro hy
    exact ⟨eSL.symm y, (Subgroup.centerCongr eSL.symm ⟨y, hy⟩).property,
      eSL.apply_symm_apply y⟩
