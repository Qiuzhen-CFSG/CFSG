module
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Projection

/-!
# The canonical complement of a projective injective simple type

Intersect the kernels of all maps to the simple type. Its full isotypic
component is a finite sum of injective copies, hence splits. Projectivity
rules out a quotient of that type in any complement: a lifted copy would
lie in both complementary submodules. Thus every complement equals the
kernel intersection, proving that the complement is canonical without
assuming the ambient module semisimple.

Consumer: the deleted A₅ whole-layer decomposition in Aschbacher--Smith
5.1.14(4) and 5.1.19, printed pp.638,643--644.
-/

@[expose] public noncomputable section
namespace Module
universe u v w
variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  {E : Type w} [AddCommGroup E] [Module R E]

/-- Vectors killed by every homomorphism to the specified module. -/
def typeReject (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (E : Type w) [AddCommGroup E] [Module R E] : Submodule R M :=
  ⨅ f : M →ₗ[R] E, LinearMap.ker f

@[simp] theorem mem_typeReject (x : M) :
    x ∈ typeReject R M E ↔ ∀ f : M →ₗ[R] E, f x = 0 := by
  simp [typeReject]

private theorem range_le_type [IsSimpleModule R E] (f : E →ₗ[R] M) :
    LinearMap.range f ≤ isotypicComponent R M E := by
  rcases f.injective_or_eq_zero with hi | hz
  · exact le_sSup ⟨(LinearEquiv.ofInjective f hi).symm⟩
  · simp [hz]

/-- A projective, injective simple type splits off canonically. -/
theorem isCompl_isotypic_typeReject [IsSimpleModule R E]
    [Small.{w} R] [Injective R E] [Projective R E]
    [Module.Finite R (isotypicComponent R M E)] :
    IsCompl (isotypicComponent R M E) (typeReject R M E) := by
  let S := isotypicComponent R M E
  obtain ⟨n, ⟨e⟩⟩ := (IsIsotypicOfType.isotypicComponent R M E).linearEquiv_fun
  obtain ⟨r₀, hr₀⟩ := Module.Injective.extension_property R (Fin n → E) S M
    S.subtype Subtype.val_injective e.toLinearMap
  let r : M →ₗ[R] S := e.symm.toLinearMap.comp r₀
  have hr : ∀ x : S, r x = x := by
    intro x
    change e.symm (r₀ (S.subtype x)) = x
    rw [show r₀ (S.subtype x) = e x from LinearMap.congr_fun hr₀ x]
    exact e.symm_apply_apply x
  have hc := LinearMap.isCompl_of_proj hr
  let U := LinearMap.ker r
  have hzero (f : U →ₗ[R] E) : f = 0 := by
    by_contra hf
    have hs : Function.Surjective f := f.surjective_or_eq_zero.resolve_right hf
    obtain ⟨j, hj⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
    have hle := range_le_type (U.subtype.comp j)
    have hjzero (x : E) : j x = 0 := by
      apply Subtype.ext
      exact hc.disjoint.le_bot ⟨hle ⟨x, rfl⟩, (j x).property⟩
    let : Nontrivial E := IsSimpleModule.nontrivial R E
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    apply hx
    have h := LinearMap.congr_fun hj x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, hjzero, map_zero] using h.symm
  have hU : U = typeReject R M E := by
    apply le_antisymm
    · intro x hx
      rw [mem_typeReject]
      intro f
      have hz := LinearMap.congr_fun (hzero (f.comp U.subtype)) ⟨x,hx⟩
      exact hz
    · intro x hx
      change e.symm (r₀ x) = 0
      rw [mem_typeReject] at hx
      have he : r₀ x = 0 := by
        funext i
        exact hx ((LinearMap.proj i).comp r₀)
      rw [he, map_zero]
  rwa [← hU]
end Module
