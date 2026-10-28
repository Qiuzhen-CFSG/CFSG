module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.Scalars
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Determinants of the literal complementary block extension

The determinant of an orthogonal block sum is the product of its two
determinants, unchanged by the published coordinate conjugation. Extension
by the identity therefore preserves the complementary determinant. Every
full-group commutator has determinant one. These statements supply the
determinant half of the required restriction of Omega membership.

Negation has determinant one on every complementary minus space, whose
dimension is even. Its Omega membership still requires the spinor invariant.
The easy direction of block Omega membership uses functoriality of the
commutator subgroup and needs no field-cardinality restriction.
Sources: GLS3 §2.7; Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
open TheoremDRootNormalizer.HigherRanks
universe u
variable {F : Type u} [Field F]

/-- The determinant homomorphism kills the full orthogonal commutator. -/
theorem omega_det_eq_one {V : Type u} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (g : quadraticIsometrySubgroup Q)
    (hg : g ∈ commutator (quadraticIsometrySubgroup Q)) : LinearEquiv.det g.val = 1 := by
  exact Abelianization.commutator_subset_ker
    (LinearEquiv.det.comp (quadraticIsometrySubgroup Q).subtype) hg

/-- The actual coordinate block map multiplies the two determinants. -/
theorem blockHom_det (r : ℕ) (a : F)
    (g : O 2 F × Minus.Orthogonal F (Minus.Space F r) (Minus.form F r a)) :
    LinearEquiv.det (blockHom r a g).val =
      LinearEquiv.det g.1.val * LinearEquiv.det g.2.val := by
  have hc := LinearEquiv.det_conj (LinearEquiv.prodCongr g.1.val g.2.val)
    (splitCoordinates (F := F) r).symm
  change LinearEquiv.det (blockHom r a g).val = _ at hc
  rw [hc]
  apply Units.ext
  simp only [Units.val_mul, LinearEquiv.coe_det]
  exact LinearMap.det_prodMap g.1.val.toLinearMap g.2.val.toLinearMap

/-- Identity extension preserves the determinant of the full complementary isometry. -/
theorem fullBlockHom_complement_det [Finite F] (r : ℕ)
    (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    LinearEquiv.det (fullBlockHom r (1, u)).val = LinearEquiv.det u.val := by
  change LinearEquiv.det (blockHom r (Minus.parameter F)
    ((elementarySubgroup (formD 2 F)).subtype (fourRight 1), u)).val = _
  rw [map_one, map_one, blockHom_det]
  simp

/-- Ambient Omega membership forces determinant one on the literal complement. -/
theorem complement_det_eq_one_of_fullBlock_mem_omega [Finite F] (r : ℕ)
    (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1)))
    (hu : fullBlockHom r (1, u) ∈
      Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3))) :
    LinearEquiv.det u.val = 1 := by
  rw [← fullBlockHom_complement_det r u]
  exact omega_det_eq_one _ _ hu

/-- Complementary Omega membership implies ambient Omega membership under the published block map. -/
theorem fullBlock_mem_omega_of_complement_mem [Finite F] (r : ℕ)
    (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1)))
    (hu : u ∈ Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    fullBlockHom r (1, u) ∈
      Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)) := by
  let f := (fullBlockHom (F := F) r).comp (MonoidHom.inr _ _)
  have hm := Subgroup.mem_map_of_mem f hu
  rw [map_commutator_eq] at hm
  exact Subgroup.commutator_mono le_top le_top hm

/-- Complementary negation has determinant one because its dimension is even. -/
theorem negativeComplement_det [Finite F] (r : ℕ) :
    LinearEquiv.det (negativeComplement (F := F) r).val = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have he : (negativeComplement (F := F) r).val.toLinearMap =
      (-1 : F) • (1 : Module.End F (Minus.Space F r)) := by
    apply LinearMap.ext
    intro x
    change -x = (-1 : F) • x
    simp
  rw [he]
  rw [LinearMap.det_smul, Minus.space_finrank, map_one, mul_one]
  simp [pow_add, pow_mul]

end ClassicalOrthogonal.Fundamental.MinusCentralizer
