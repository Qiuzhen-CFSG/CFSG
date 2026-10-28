module

public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The augmentation of a group algebra

This module begins the algebraic foundation for modular character blocks.  The
augmentation of `R[G]` sends every group basis element to one and therefore
gives the action of `R[G]` on the trivial module.  It is the sum of the
coefficients and commutes with changing the coefficient ring. Coefficient
extension also preserves central elements, since it preserves their
commutation with all group basis elements. Over a field,
an idempotent acts on the trivial module either as zero or as the identity,
because its augmentation is an idempotent in that field.

Consequently, once blocks are represented by primitive central idempotents,
the principal block is the component whose augmentation is one.  This is the
block-theoretic meaning used in ABG Chapter III §§5–7 when the principal
2-block is distinguished by the principal character; it is independent of the
later quasi-dihedral character identities.
-/

public section

noncomputable section

open scoped MonoidAlgebra

universe u v

attribute [local instance] Fintype.ofFinite

/-- The augmentation of a group algebra, sending every group element to one. -/
noncomputable def groupAlgebraAugmentation
    (R : Type u) (G : Type v) [CommSemiring R] [Monoid G] :
    MonoidAlgebra R G →ₐ[R] R :=
  MonoidAlgebra.lift R R G (1 : G →* R)

@[simp]
theorem groupAlgebraAugmentation_single
    (R : Type u) (G : Type v) [CommSemiring R] [Monoid G] (g : G) (a : R) :
    groupAlgebraAugmentation R G (MonoidAlgebra.single g a) = a := by
  simp [groupAlgebraAugmentation]

theorem groupAlgebraAugmentation_apply
    (R : Type u) (G : Type v) [CommSemiring R] [Monoid G] [Finite G]
    (a : MonoidAlgebra R G) :
    groupAlgebraAugmentation R G a = ∑ g : G, a.coeff g := by
  classical
  rw [groupAlgebraAugmentation, MonoidAlgebra.lift_apply]
  simp only [MonoidHom.one_apply, smul_eq_mul, mul_one]
  exact Finsupp.sum_fintype a.coeff (fun _ r => r) (by simp)

/-- Augmentation commutes with changing the coefficient ring. -/
theorem groupAlgebraAugmentation_mapRingHom
    {R : Type u} {S : Type*} {G : Type v}
    [CommSemiring R] [CommSemiring S] [Monoid G]
    (f : R →+* S) (a : MonoidAlgebra R G) :
    groupAlgebraAugmentation S G (MonoidAlgebra.mapRingHom G f a) =
      f (groupAlgebraAugmentation R G a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single g r => simp

/-- An idempotent acts on the trivial module either as zero or as the identity. -/
theorem groupAlgebraAugmentation_eq_zero_or_one_of_isIdempotent
    (F : Type u) (G : Type v) [Field F] [Group G]
    (e : MonoidAlgebra F G) (he : IsIdempotentElem e) :
    groupAlgebraAugmentation F G e = 0 ∨ groupAlgebraAugmentation F G e = 1 := by
  exact IsIdempotentElem.iff_eq_zero_or_one.mp (he.map (groupAlgebraAugmentation F G))

/-- Coefficient extension preserves centrality in a group algebra. -/
theorem groupAlgebra_mapRingHom_mem_center
    {R S G : Type*} [CommRing R] [CommRing S] [Group G]
    (f : R →+* S) (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) :
    MonoidAlgebra.mapRingHom G f e ∈ Set.center (MonoidAlgebra S G) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      have hcomm := Semigroup.mem_center_iff.mp he
        (MonoidAlgebra.single g (1 : R))
      have hmap := congrArg (MonoidAlgebra.mapRingHom G f) hcomm
      have hcommOne :
          (MonoidAlgebra.single g (1 : S)) *
              MonoidAlgebra.mapRingHom G f e =
            MonoidAlgebra.mapRingHom G f e *
              MonoidAlgebra.single g (1 : S) := by
        simpa using hmap
      rw [show (MonoidAlgebra.single g r : MonoidAlgebra S G) =
          r • MonoidAlgebra.single g 1 by simp]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      exact congrArg (fun x : MonoidAlgebra S G => r • x) hcommOne
