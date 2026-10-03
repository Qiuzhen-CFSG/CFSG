module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Group Algebra Local Trace

Finite projective representations over local group algebras have trace zero
at nonidentity elements. The proof computes the diagonal in the canonical
group-algebra basis, transports it along a finite free-module basis, and uses
freeness of finite projective modules over local rings. We also establish that
the group algebra of an order-two commutative group is local whenever the
coefficient ring is local and two is a nonunit: the augmentation determines
units by an explicit two-coefficient inverse calculation.

These algebraic inputs feed the involution support theorem for central
idempotents.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CentralIdempotentSupport.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

open Module CategoryTheory

namespace ModularBlock.CentralIdempotentSupport

universe u v w

attribute [local instance] Fintype.ofFinite

/-- The group algebra of a two-element commutative group over a local ring in
which `2` is a nonunit is local.  This is the integral `C₂`-locality input
used below. -/
theorem isLocalRing_monoidAlgebra_of_card_two
    {R C : Type*} [CommRing R] [IsLocalRing R] [CommGroup C]
    (h2 : ¬ IsUnit (2 : R))
    (hC : Nat.card C = 2) :
    IsLocalRing (MonoidAlgebra R C) := by
  classical
  obtain ⟨c, hc, hc_unique⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hC
  have hall (x : C) : x = 1 ∨ x = c := by
    by_cases hx : x = 1
    · exact Or.inl hx
    · exact Or.inr (hc_unique x hx)
  have hc2 : c * c = 1 := by
    rcases hall (c * c) with h | h
    · exact h
    · exfalso
      apply hc
      apply mul_left_cancel (a := c)
      simpa using h
  have isUnit_pair (a b : R) (hab : IsUnit (a + b)) :
      IsUnit (MonoidAlgebra.single (1 : C) a +
        MonoidAlgebra.single c b) := by
    have h2b : ¬ IsUnit (2 * b) := by
      intro h
      exact h2 (isUnit_of_mul_isUnit_left h)
    have hamb : IsUnit (a - b) := by
      by_contra h
      have hn := IsLocalRing.nonunits_add h h2b
      apply hn
      have heq : a - b + 2 * b = a + b := by ring
      rw [heq]
      exact hab
    have hdet : IsUnit (a ^ 2 - b ^ 2) := by
      rw [sq_sub_sq]
      exact hab.mul hamb
    let x : MonoidAlgebra R C :=
      MonoidAlgebra.single (1 : C) a + MonoidAlgebra.single c b
    let y : MonoidAlgebra R C :=
      MonoidAlgebra.single (1 : C) a - MonoidAlgebra.single c b
    have hxy : x * y =
        algebraMap R (MonoidAlgebra R C) (a ^ 2 - b ^ 2) := by
      dsimp [x, y]
      rw [add_mul, mul_sub, mul_sub, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.single_mul_single]
      simp [hc2]
      ext z
      change
        (Finsupp.single (1 : C) (a * a) z -
            Finsupp.single c (a * b) z) +
          (Finsupp.single c (b * a) z -
            Finsupp.single (1 : C) (b * b) z) =
          Finsupp.single (1 : C) (a ^ 2) z -
            Finsupp.single (1 : C) (b ^ 2) z
      rcases hall z with rfl | rfl
      · simp [hc]
        ring
      · simp [hc]
        ring
    apply isUnit_of_mul_isUnit_left (y := y)
    rw [hxy]
    exact hdet.map (algebraMap R (MonoidAlgebra R C))
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  let a := f.coeff 1
  let b := f.coeff c
  have hf : f = MonoidAlgebra.single (1 : C) a +
      MonoidAlgebra.single c b := by
    ext x
    rcases hall x with rfl | rfl <;> simp [a, b, hc]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (a + b) with hab | hab
  · rw [hf]
    exact Or.inl (isUnit_pair a b hab)
  · right
    rw [hf]
    have hrewrite :
        (1 - (MonoidAlgebra.single (1 : C) a +
          MonoidAlgebra.single c b) : MonoidAlgebra R C) =
        MonoidAlgebra.single (1 : C) (1 - a) +
          MonoidAlgebra.single c (-b) := by
      ext x
      change
        (MonoidAlgebra.single (1 : C) 1).coeff x -
            ((MonoidAlgebra.single (1 : C) a).coeff x +
              (MonoidAlgebra.single c b).coeff x) =
          (MonoidAlgebra.single (1 : C) (1 - a)).coeff x +
            (MonoidAlgebra.single c (-b)).coeff x
      rcases hall x with rfl | rfl
      · simp [hc]
      · simp [hc]
    rw [hrewrite]
    apply isUnit_pair
    convert hab using 1
    ring

/-- Left multiplication by a nonidentity group element has trace zero on the
group algebra. -/
theorem trace_mulLeft_of_ne_one
    {R : Type u} {C : Type v} [CommRing R] [CommGroup C] [Finite C]
    (g : C) (hg : g ≠ 1) :
    LinearMap.trace R (MonoidAlgebra R C)
        (LinearMap.mulLeft R (MonoidAlgebra.of R C g)) = 0 := by
  classical
  let b : Basis C R (MonoidAlgebra R C) := MonoidAlgebra.basis _ _
  rw [LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  apply Finset.sum_eq_zero
  intro i _hi
  change Algebra.leftMulMatrix b (MonoidAlgebra.of R C g) i i = 0
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change (MonoidAlgebra.single g 1 * MonoidAlgebra.single i 1 :
      MonoidAlgebra R C).coeff i = 0
  simp [hg]

/-- A nonidentity element has trace zero on every finite free module over its
group algebra.  This is the algebraic form of "a free character vanishes away
from the identity". -/
theorem trace_lsmul_of_free_groupAlgebra
    {R : Type u} {C : Type v} {M : Type w}
    [CommRing R] [CommGroup C] [Finite C]
    [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R C) M]
    [IsScalarTower R (MonoidAlgebra R C) M]
    [Module.Free (MonoidAlgebra R C) M]
    [Module.Finite (MonoidAlgebra R C) M]
    (g : C) (hg : g ≠ 1) :
    LinearMap.trace R M
        ((LinearMap.lsmul (MonoidAlgebra R C) M
          (MonoidAlgebra.of R C g)).restrictScalars R) = 0 := by
  classical
  let bR : Basis C R (MonoidAlgebra R C) := MonoidAlgebra.basis _ _
  let bM := Module.Free.chooseBasis (MonoidAlgebra R C) M
  rw [LinearMap.trace_eq_matrix_trace R (bR.smulTower' bM), Matrix.trace]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ _hij
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply,
    Basis.smulTower'_repr, Basis.smulTower'_apply,
    LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply, if_pos, smul_eq_mul, mul_one]
  change bR.repr
      ((MonoidAlgebra.of R C g) * bR j) j = 0
  change (MonoidAlgebra.single g 1 * MonoidAlgebra.single j 1 :
      MonoidAlgebra R C).coeff j = 0
  simp [hg]

/-- Representation-theoretic form of `trace_lsmul_of_free_groupAlgebra`. -/
theorem trace_representation_of_free_asModule
    {R : Type u} {C : Type v} {V : Type w}
    [CommRing R] [CommGroup C] [Finite C]
    [AddCommGroup V] [Module R V]
    (rho : Representation R C V)
    [Module.Free (MonoidAlgebra R C) rho.asModule]
    [Module.Finite (MonoidAlgebra R C) rho.asModule]
    (g : C) (hg : g ≠ 1) :
    LinearMap.trace R V (rho g) = 0 := by
  let f : rho.asModule →ₗ[R] rho.asModule :=
    (LinearMap.lsmul (MonoidAlgebra R C) rho.asModule
      (MonoidAlgebra.of R C g)).restrictScalars R
  have hf : rho.asModuleEquiv.conj f = rho g := by
    ext x
    simp [f, LinearEquiv.conj_apply_apply]
    rfl
  have h := trace_lsmul_of_free_groupAlgebra
    (R := R) (C := C) (M := rho.asModule) g hg
  calc
    LinearMap.trace R V (rho g) =
        LinearMap.trace R V (rho.asModuleEquiv.conj f) := by rw [hf]
    _ = LinearMap.trace R rho.asModule f := LinearMap.trace_conj' f rho.asModuleEquiv
    _ = 0 := h

/-- Over a local group algebra, finite projective representations vanish on
nonidentity elements.  The only input beyond projectivity is the standard
fact that finite flat modules over local rings are free. -/
theorem trace_representation_of_projective_asModule
    {R : Type u} {C : Type v} {V : Type w}
    [CommRing R] [CommGroup C] [Finite C]
    [AddCommGroup V] [Module R V]
    (rho : Representation R C V)
    [IsLocalRing (MonoidAlgebra R C)]
    [Module.Projective (MonoidAlgebra R C) rho.asModule]
    [Module.Finite (MonoidAlgebra R C) rho.asModule]
    (g : C) (hg : g ≠ 1) :
    LinearMap.trace R V (rho g) = 0 := by
  let : Module.Free (MonoidAlgebra R C) rho.asModule :=
    Module.free_of_flat_of_isLocalRing
  exact trace_representation_of_free_asModule rho g hg

end ModularBlock.CentralIdempotentSupport

