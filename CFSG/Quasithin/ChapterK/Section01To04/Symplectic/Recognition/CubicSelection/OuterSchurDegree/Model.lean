module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.Reduction

/-!
# The actual Schur-linear operator and its tensor-swap realization

An ambient actor commuting with every component intertwiner acts linearly on
that component's original Schur-field module. Extend this very operator to
its algebraic closure; its restriction to the component, square, and
conjugation equations are preserved. A tensor-swap realization specifies an
actual linear equivalence and the actions of the outer actor and every
commuting inner involution. It contains no fixed-space or degree estimate.

Constructing this realization from periodic symplectic tensor support and
computing its common fixed spaces are separate mathematical obligations.
Source: Guralnick--Malle, Classification of 2F-modules II, Section 3.5 and
Proposition 6.2(2--3), manuscript pp.20,39--40; Aschbacher--Smith K.3.4,
printed pp.456--457.
-/

@[expose] public section

open Representation Representation.FrobeniusTensor
open scoped MonoidAlgebra TensorProduct

namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)]

/-- The literal ambient map, linear over the original component Schur field. -/
noncomputable def schurActor (t : G) (ht : IsSchurLinear ρ L t) :
    Module.End (SchurField (ρ.comp L.subtype)) (Representation.asModule (ρ.comp L.subtype)) where
  toFun v := (Representation.asModuleEquiv (ρ.comp L.subtype)).symm
    (ρ t ((Representation.asModuleEquiv (ρ.comp L.subtype)) v))
  map_add' x y := by simp
  map_smul' c v := by
    let f := (IntertwiningMap.equivAlgEnd (ρ.comp L.subtype)).symm c
    have hh := LinearMap.congr_fun (ht f) ((Representation.asModuleEquiv (ρ.comp L.subtype)) v)
    exact hh

/-- Scalar extension of the actual Schur-linear ambient map. -/
noncomputable def absoluteActor (t : G) (ht : IsSchurLinear ρ L t) :
    Module.End (Closure (ρ.comp L.subtype)) (AbsoluteSpace (ρ.comp L.subtype)) :=
  (schurActor ρ L t ht).baseChange (Closure (ρ.comp L.subtype))

omit [FiniteDimensional (ZMod 2) V] [IsIrreducible (ρ.comp L.subtype)] in
/-- On component elements this is the existing endomorphism-field action. -/
theorem schurActor_of_mem (u : L) :
    schurActor ρ L u (isSchurLinear_of_mem ρ L u.property) =
      endFieldRep (ρ.comp L.subtype) u := by
  ext v
  rfl

/-- On component elements this is the existing absolute representation. -/
theorem absoluteActor_of_mem (u : L) :
    absoluteActor ρ L u (isSchurLinear_of_mem ρ L u.property) =
      absoluteRep (ρ.comp L.subtype) u := by
  change (schurActor ρ L u _).baseChange _ = _
  rw [schurActor_of_mem]
  rfl

omit [FiniteDimensional (ZMod 2) V] [IsIrreducible (ρ.comp L.subtype)] in
/-- The original involution equation survives passage to the Schur field. -/
theorem schurActor_square (t : G) (ht : IsSchurLinear ρ L t) (ht2 : t ^ 2 = 1) :
    schurActor ρ L t ht ^ 2 = 1 := by
  ext v
  apply (Representation.asModuleEquiv (ρ.comp L.subtype)).injective
  change ρ t (ρ t (Representation.asModuleEquiv (ρ.comp L.subtype) v)) =
    Representation.asModuleEquiv (ρ.comp L.subtype) v
  rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ht2, map_one]
  rfl

/-- The original involution equation survives absolute scalar extension. -/
theorem absoluteActor_square (t : G) (ht : IsSchurLinear ρ L t) (ht2 : t ^ 2 = 1) :
    absoluteActor ρ L t ht ^ 2 = 1 := by
  rw [absoluteActor, pow_two, ← LinearMap.baseChange_mul, ← pow_two,
    schurActor_square ρ L t ht ht2, LinearMap.baseChange_one]

omit [FiniteDimensional (ZMod 2) V] [IsIrreducible (ρ.comp L.subtype)] in
/-- The Schur-linear operator induces the literal conjugation action on L. -/
theorem schurActor_intertwines [L.Normal] (t : G) (ht : IsSchurLinear ρ L t) (u : L) :
    schurActor ρ L t ht * endFieldRep (ρ.comp L.subtype) u =
      endFieldRep (ρ.comp L.subtype) (MulAut.conjNormal t u) * schurActor ρ L t ht := by
  ext v
  apply (Representation.asModuleEquiv (ρ.comp L.subtype)).injective
  change ρ t (ρ u (Representation.asModuleEquiv (ρ.comp L.subtype) v)) =
    ρ (t * u * t⁻¹) (ρ t (Representation.asModuleEquiv (ρ.comp L.subtype) v))
  simp only [map_mul, Module.End.mul_apply]
  simp

/-- The absolute operator retains that same conjugation action. -/
theorem absoluteActor_intertwines [L.Normal]
    (t : G) (ht : IsSchurLinear ρ L t) (u : L) :
    absoluteActor ρ L t ht * absoluteRep (ρ.comp L.subtype) u =
      absoluteRep (ρ.comp L.subtype) (MulAut.conjNormal t u) * absoluteActor ρ L t ht := by
  change LinearMap.baseChange _ _ * LinearMap.baseChange _ _ =
    LinearMap.baseChange _ _ * LinearMap.baseChange _ _
  rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, schurActor_intertwines]

/-- A genuine tensor-square realization, with the outer involution acting by
interchange. A nontrivial commuting inner involution acts diagonally by a
nonidentity involution on a half tensor. No numerical conclusion is assumed. -/
structure TensorSwapRealization (t : G) (ht : IsSchurLinear ρ L t) where
  size : ℕ
  four_le : 4 ≤ size
  equivalence : AbsoluteSpace (ρ.comp L.subtype) ≃ₗ[Closure (ρ.comp L.subtype)]
    ((Fin size → Closure (ρ.comp L.subtype)) ⊗[Closure (ρ.comp L.subtype)]
      (Fin size → Closure (ρ.comp L.subtype)))
  outer_action : ∀ v, equivalence (absoluteActor ρ L t ht v) =
    TensorProduct.comm _ _ _ (equivalence v)
  inner_action : ∀ (u : L), u ^ 2 = 1 → Commute t (u : G) →
    ∃ f : Module.End (Closure (ρ.comp L.subtype)) (Fin size → Closure (ρ.comp L.subtype)),
      f ^ 2 = 1 ∧ (u ≠ 1 → f ≠ 1) ∧
      ∀ v, equivalence (absoluteRep (ρ.comp L.subtype) u v) =
        TensorProduct.map f f (equivalence v)

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur

