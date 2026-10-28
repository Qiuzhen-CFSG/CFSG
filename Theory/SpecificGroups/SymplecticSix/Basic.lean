module

public import Theory.Representation.SymplecticNatural
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Symplectic six-space and its full subspace stabilizers

The natural action is that of the actual matrices in `Matrix.symplecticGroup
(Fin 3) F`, with the alternating form having positive pairing from the first
hyperbolic half to the second. A full subspace stabilizer consists of matrices
preserving that subspace. Finite dimension makes forward invariance sufficient.

This extends the existing four-space construction without changing its API.
These definitions support the local calculations for Aschbacher–Smith,
Theorem 0.1.2(2), printed p.4 (Theorem 0.1.1(2), printed p.482),
`refs/quasithin.pdf`. No local rank or two-core assertion is built into them.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticSix

abbrev Vector (F : Type*) := (Fin 3 ⊕ Fin 3) → F
abbrev Sp (F : Type*) [CommRing F] := Matrix.symplecticGroup (Fin 3) F

/-- The actual central quotient of the matrix group. -/
abbrev PSp (F : Type*) [Field F] := Sp F ⧸ Subgroup.center (Sp F)

variable (F : Type*) [Field F]

/-- The standard alternating form, with positive eᵢ,fᵢ pairing. -/
def form : LinearMap.BilinForm F (Vector F) := (-Matrix.J (Fin 3) F).toBilin'

variable {F} in
theorem form_apply (x y : Vector F) :
    form F x y = ∑ i : Fin 3, (x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i)) := by
  simp [form, Matrix.toBilin'_apply, Matrix.J, Matrix.fromBlocks, Matrix.one_apply,
    Fintype.sum_sum_type, sub_eq_add_neg, Finset.sum_add_distrib, add_comm]

variable {F} in
def e (i : Fin 3) : Vector F := Pi.single (.inl i) 1

variable {F} in
@[simp] theorem form_e_right (x : Vector F) (i : Fin 3) :
    form F x (e i) = -x (.inr i) := by
  simp [form_apply, e, Pi.single_apply]

variable {F} in
/-- The invertible natural matrix representation. -/
def toLinear : Sp F →* (Vector F ≃ₗ[F] Vector F) where
  toFun g := LinearEquiv.ofBijective (Representation.symplecticNatural 3 g)
    ((Representation.symplecticNatural 3).apply_bijective g)
  map_one' := by ext x : 1; exact congrArg (fun f => f x) (Representation.symplecticNatural 3).map_one
  map_mul' g h := by ext x : 1; exact congrArg (fun f => f x) ((Representation.symplecticNatural 3).map_mul g h)

variable {F} in
@[simp] theorem toLinear_apply (g : Sp F) (x : Vector F) : toLinear g x = g • x := rfl

variable {F} in
theorem smul_eq_mulVec (g : Sp F) (x : Vector F) : g • x = g.val *ᵥ x := rfl

variable {F} in
/-- The carrier preserves the displayed form by its defining matrix equation. -/
theorem preserves_form (g : Sp F) (x y : Vector F) :
    form F (g • x) (g • y) = form F x y := by
  have hg := SymplecticGroup.mem_iff'.mp g.property
  have hm : g.valᵀ * (-Matrix.J (Fin 3) F) * g.val = -Matrix.J (Fin 3) F := by
    simp [hg]
  have h := Matrix.toBilin'_comp (-Matrix.J (Fin 3) F) g.val g.val
  rw [hm] at h
  exact congrArg (fun B : LinearMap.BilinForm F (Vector F) => B x y) h

variable {F}

/-- Setwise subspace stabilizer under the actual matrix action. -/
def stabilizer (W : Submodule F (Vector F)) : Subgroup (Sp F) :=
  (MulAction.stabilizer (Vector F ≃ₗ[F] Vector F) W).comap toLinear

/-- In finite dimension it suffices to check forward invariance. -/
theorem mem_stabilizer_iff (W : Submodule F (Vector F)) (g : Sp F) :
    g ∈ stabilizer W ↔ ∀ x ∈ W, g • x ∈ W := by
  change W.map (toLinear g).toLinearMap = W ↔ _
  constructor
  · intro h x hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro h
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro y ⟨x, hx, rfl⟩
      exact h x hx
    · exact (toLinear g).finrank_map_eq W


end Theory.SpecificGroups.SymplecticSix
