module

public import Theory.Character.ModularBlock.PrimitiveCentralIdempotent
public import Theory.Character.ModularBlock.Basic
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Galois descent of central-idempotent factors

Over a finite field extension, Galois automorphisms act coefficientwise on
the group algebra. A fixed element descends because every coefficient is
fixed and hence belongs to the base field. Injectivity of scalar extension
then descends centrality, idempotence, and the factor relation. Source
primitivity identifies any such nonzero factor with the source idempotent.

This is the descent step in finite-field preservation of augmentation-one
primitivity. Ported from the GaloisHelpers and Descent sections of
`c3503435:glauberman_zStar/Submission/ZStar/FiniteFieldPrimitivity.lean`.
The Galois action is exposed for coefficient and orbit calculations.
-/

public section
noncomputable section
namespace ModularBlock.FiniteFieldPrimitivity
attribute [local instance] Fintype.ofFinite
open scoped BigOperators

section GaloisHelpers

variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K]
variable (H : Type*) [Group H]

@[expose] noncomputable def conjugate
    (σ : K ≃ₐ[k] K) (x : MonoidAlgebra K H) : MonoidAlgebra K H :=
  MonoidAlgebra.mapRingEquiv H σ.toRingEquiv x

@[simp] theorem conjugate_apply (σ : K ≃ₐ[k] K)
    (x : MonoidAlgebra K H) (h : H) :
    (conjugate k K H σ x).coeff h = σ (x.coeff h) := by
  simp [conjugate]

@[simp] theorem conjugate_zero (σ : K ≃ₐ[k] K) :
    conjugate k K H σ (0 : MonoidAlgebra K H) = 0 := by
  simp [conjugate]

@[simp] theorem conjugate_one (σ : K ≃ₐ[k] K) :
    conjugate k K H σ (1 : MonoidAlgebra K H) = 1 := by
  simp [conjugate]

@[simp] theorem conjugate_add (σ : K ≃ₐ[k] K)
    (x y : MonoidAlgebra K H) :
    conjugate k K H σ (x + y) = conjugate k K H σ x + conjugate k K H σ y := by
  simp [conjugate]

@[simp] theorem conjugate_sub (σ : K ≃ₐ[k] K)
    (x y : MonoidAlgebra K H) :
    conjugate k K H σ (x - y) = conjugate k K H σ x - conjugate k K H σ y := by
  simp [conjugate]

@[simp] theorem conjugate_mul (σ : K ≃ₐ[k] K)
    (x y : MonoidAlgebra K H) :
    conjugate k K H σ (x * y) = conjugate k K H σ x * conjugate k K H σ y := by
  simp [conjugate]

@[simp] theorem conjugate_conjugate (τ σ : K ≃ₐ[k] K)
    (x : MonoidAlgebra K H) :
    conjugate k K H τ (conjugate k K H σ x) =
      conjugate k K H (τ * σ) x := by
  ext h
  simp [conjugate, AlgEquiv.mul_apply]

theorem conjugate_algebraMap
    (σ : K ≃ₐ[k] K) (x : MonoidAlgebra k H) :
    conjugate k K H σ
        (MonoidAlgebra.mapRingHom H (algebraMap k K) x) =
      MonoidAlgebra.mapRingHom H (algebraMap k K) x := by
  ext h
  simp [conjugate]

theorem conjugate_mapRingHom
    (σ : K ≃ₐ[k] K) (x : MonoidAlgebra K H) :
    conjugate k K H σ x =
      MonoidAlgebra.mapRingHom H σ.toRingEquiv.toRingHom x := rfl

theorem conjugate_mem_center
    (σ : K ≃ₐ[k] K) (x : MonoidAlgebra K H)
    (hx : x ∈ Set.center (MonoidAlgebra K H)) :
    conjugate k K H σ x ∈ Set.center (MonoidAlgebra K H) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  let E := MonoidAlgebra.mapRingEquiv H σ.toRingEquiv
  have h := Semigroup.mem_center_iff.mp hx
    (E.symm a)
  calc
    a * conjugate k K H σ x = E (E.symm a) * E x := by
      rw [E.apply_symm_apply]
      rfl
    _ = E (E.symm a * x) := (E.map_mul _ _).symm
    _ = E (x * E.symm a) := congrArg E h
    _ = E x * E (E.symm a) := E.map_mul _ _
    _ = conjugate k K H σ x * a := by rw [E.apply_symm_apply]; rfl

theorem conjugate_isIdempotent
    (σ : K ≃ₐ[k] K) (x : MonoidAlgebra K H)
    (hx : IsIdempotentElem x) :
    IsIdempotentElem (conjugate k K H σ x) := by
  let E := MonoidAlgebra.mapRingEquiv H σ.toRingEquiv
  change E x * E x = E x
  rw [← E.map_mul, hx]

theorem conjugate_factor
    (σ : K ≃ₐ[k] K) (e f : MonoidAlgebra K H)
    (hefixed : conjugate k K H σ e = e)
    (hfactor : f * e = f) :
    conjugate k K H σ f * e = conjugate k K H σ f := by
  rw [← hefixed, ← conjugate_mul]
  exact congrArg (conjugate k K H σ) hfactor

variable [Finite K]

theorem exists_preimage_of_galois_fixed
    (y : MonoidAlgebra K H)
    (hy : ∀ σ : K ≃ₐ[k] K, conjugate k K H σ y = y) :
    ∃ x : MonoidAlgebra k H,
      MonoidAlgebra.mapRingHom H (algebraMap k K) x = y := by
  classical
  have hcoeff : ∀ h : H, y.coeff h ∈ Set.range (algebraMap k K) := by
    intro h
    apply (IsGalois.mem_range_algebraMap_iff_fixed
      (F := k) (E := K) (y.coeff h)).2
    intro σ
    have hs := congrArg (fun a : MonoidAlgebra K H => a.coeff h) (hy σ)
    simpa [conjugate_apply] using hs
  have hyRange :
      y ∈ Set.range
        (MonoidAlgebra.map (M := H) (algebraMap k K).toAddMonoidHom) := by
    rw [MonoidAlgebra.range_map]
    exact hcoeff
  rcases hyRange with ⟨x, hx⟩
  exact ⟨x, hx⟩

end GaloisHelpers

section Descent

variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K]
variable (H : Type*) [Group H]

private theorem mapGroupAlgebra_injective :
    Function.Injective
      (MonoidAlgebra.mapRingHom H (algebraMap k K)) := by
  exact MonoidAlgebra.map_injective (algebraMap k K).toAddMonoidHom
    (algebraMap k K).injective

variable [Finite K]

theorem fixed_central_idempotent_factor_eq_map_of_source_primitive
    (e : MonoidAlgebra k H)
    (hprimitive : IsCentrallyPrimitive e)
    (y : MonoidAlgebra K H)
    (hyfixed : ∀ σ : K ≃ₐ[k] K, conjugate k K H σ y = y)
    (hycenter : y ∈ Set.center (MonoidAlgebra K H))
    (hyidem : IsIdempotentElem y)
    (hyfactor :
      y * MonoidAlgebra.mapRingHom H (algebraMap k K) e = y)
    (hyne : y ≠ 0) :
    y = MonoidAlgebra.mapRingHom H (algebraMap k K) e := by
  obtain ⟨x, hxmap⟩ :=
    exists_preimage_of_galois_fixed k K H y hyfixed
  have hmapinj := mapGroupAlgebra_injective k K H
  have hxcenter : x ∈ Set.center (MonoidAlgebra k H) := by
    apply (Semigroup.mem_center_iff).2
    intro a
    apply hmapinj
    rw [map_mul, map_mul, hxmap]
    exact Semigroup.mem_center_iff.mp hycenter
      (MonoidAlgebra.mapRingHom H (algebraMap k K) a)
  have hxidem : IsIdempotentElem x := by
    apply hmapinj
    rw [map_mul, hxmap, hyidem]
  have hxfactor : x * e = x := by
    apply hmapinj
    rw [map_mul, hxmap, hyfactor]
  have hxne : x ≠ 0 := by
    intro hxzero
    apply hyne
    rw [← hxmap, hxzero, map_zero]
  have hxeq : x = e :=
    hprimitive.2.2.2 x hxcenter hxidem hxfactor hxne
  rw [← hxmap, hxeq]

end Descent


end ModularBlock.FiniteFieldPrimitivity

