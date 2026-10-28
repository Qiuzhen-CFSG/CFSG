module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.Model
public import Theory.Representation.ScalarDescent
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Descent of literal single and common fixed spaces

The common fixed equations are the kernel of a product of two linear maps.
Tensor-product distribution over products and flat kernel base change preserve
this kernel's dimension. Restricting the explicit Schur-linear operators back
to the binary field identifies the original kernels through `asModuleEquiv`.
The dimension tower therefore multiplies both fixed and moved dimensions by
the degree of the original component Schur field.

These are the scalar-descent steps for the tensor estimates in
Guralnick--Malle, Classification of 2F-modules II, Section 3.5 and Proposition
6.2, and Aschbacher--Smith K.3.4, pp.456--457. Schur-linearity is retained
explicitly for each ambient operator.
-/

@[expose] public section

open scoped TensorProduct
open Module Representation Representation.FrobeniusTensor
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur
namespace FixedSpace
section Linear
variable {F E W X : Type*} [Field F] [Field E] [Algebra F E]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  [AddCommGroup X] [Module F X]

/-- Field extension preserves the dimension of a kernel. -/
theorem finrank_ker_baseChange (f : W →ₗ[F] X) :
    finrank E (f.baseChange E).ker = finrank F f.ker := by
  rw [← (LinearMap.kerBaseChangeEquiv (E := E) f).finrank_eq]
  exact Module.finrank_baseChange

/-- Field extension preserves the intersection of two kernel equations. -/
theorem finrank_inf_ker_baseChange (f g : Module.End F W) :
    finrank E ↥((f.baseChange E).ker ⊓ (g.baseChange E).ker) =
      finrank F ↥(f.ker ⊓ g.ker) := by
  have h : (TensorProduct.prodRight F E E W W).toLinearMap.comp
      ((f.prod g).baseChange E) = (f.baseChange E).prod (g.baseChange E) := by
    ext a <;> simp
  rw [← LinearMap.ker_prod, ← h, LinearEquiv.ker_comp,
    finrank_ker_baseChange, LinearMap.ker_prod]

/-- Scalar extension preserves the common fixed dimension of two operators. -/
theorem finrank_commonFixed_baseChange (f g : Module.End F W) :
    finrank E ↥((f.baseChange E - 1).ker ⊓ (g.baseChange E - 1).ker) =
      finrank F ↥((f - 1).ker ⊓ (g - 1).ker) := by
  have h := finrank_inf_ker_baseChange (E := E) (f - 1) (g - 1)
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_sub,
    LinearMap.baseChange_one] at h
  exact h

omit [FiniteDimensional F W] in
private theorem finrank_inf_self (S : Submodule F W) :
    finrank F ↥(S ⊓ S) = finrank F S := by rw [inf_idem]

/-- An actual intertwining equivalence transports both fixed equations. -/
noncomputable def commonFixedEquiv (e : W ≃ₗ[F] X)
    (f g : Module.End F W) (f' g' : Module.End F X)
    (hf : ∀ v, e (f v) = f' (e v)) (hg : ∀ v, e (g v) = g' (e v)) :
    ↥((f - 1).ker ⊓ (g - 1).ker) ≃ₗ[F] ↥((f' - 1).ker ⊓ (g' - 1).ker) := by
  have h : ((f' - 1).ker ⊓ (g' - 1).ker).comap e.toLinearMap =
      (f - 1).ker ⊓ (g - 1).ker := by
    ext v
    simp only [Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker,
      LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe,
      sub_eq_zero, ← hf, ← hg, e.injective.eq_iff]
  exact (LinearEquiv.ofEq _ _ h.symm).trans (e.ofSubmodule' _)

/-- An intertwining equivalence preserves the moved dimension. -/
theorem finrank_range_sub_one_equiv [FiniteDimensional F X] (e : W ≃ₗ[F] X)
    (f : Module.End F W) (f' : Module.End F X)
    (hf : ∀ v, e (f v) = f' (e v)) :
    finrank F (f - 1).range = finrank F (f' - 1).range := by
  have hk := (commonFixedEquiv e f f f' f' hf hf).finrank_eq
  rw [finrank_inf_self, finrank_inf_self] at hk
  have hW := (f - 1).finrank_range_add_finrank_ker
  have hX := (f' - 1).finrank_range_add_finrank_ker
  have he := e.finrank_eq
  omega
end Linear

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)]

/-- The literal binary common fixed dimension is the original Schur degree times its absolute dimension. -/
theorem binary_commonFixed_finrank (t s : G)
    (ht : IsSchurLinear ρ L t) (hs : IsSchurLinear ρ L s) :
    finrank (ZMod 2) ↥((ρ t - 1).ker ⊓ (ρ s - 1).ker) =
      finrank (ZMod 2) (FrobeniusTensor.SchurField (ρ.comp L.subtype)) *
        finrank (Closure (ρ.comp L.subtype))
          ↥((absoluteActor ρ L t ht - 1).ker ⊓ (absoluteActor ρ L s hs - 1).ker) := by
  let f := schurActor ρ L t ht
  let g := schurActor ρ L s hs
  let e := commonFixedEquiv (Representation.asModuleEquiv (ρ.comp L.subtype))
    (f.restrictScalars (ZMod 2)) (g.restrictScalars (ZMod 2)) (ρ t) (ρ s)
    (fun v => by simp [f, schurActor]) (fun v => by simp [g, schurActor])
  have he := e.finrank_eq
  change finrank (ZMod 2) ↥((f - 1).ker ⊓ (g - 1).ker) = _ at he
  rw [← he, ← Module.finrank_mul_finrank (ZMod 2) (FrobeniusTensor.SchurField (ρ.comp L.subtype))
    ↥((f - 1).ker ⊓ (g - 1).ker)]
  congr 1
  exact (finrank_commonFixed_baseChange (E := Closure (ρ.comp L.subtype)) f g).symm

/-- The literal binary moved dimension is the original Schur degree times its absolute dimension. -/
theorem binary_range_finrank (t : G) (ht : IsSchurLinear ρ L t) :
    finrank (ZMod 2) (ρ t - 1).range =
      finrank (ZMod 2) (FrobeniusTensor.SchurField (ρ.comp L.subtype)) *
        finrank (Closure (ρ.comp L.subtype)) (absoluteActor ρ L t ht - 1).range := by
  have hk := binary_commonFixed_finrank ρ L t t ht ht
  rw [finrank_inf_self, finrank_inf_self] at hk
  have hb := (ρ t - 1).finrank_range_add_finrank_ker
  have ha := (absoluteActor ρ L t ht - 1).finrank_range_add_finrank_ker
  have hd := binary_finrank_eq (ρ.comp L.subtype)
  have has := congrArg (fun m => finrank (ZMod 2) (FrobeniusTensor.SchurField (ρ.comp L.subtype)) * m) ha
  rw [Nat.mul_add] at has
  omega
end FixedSpace
end CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur
