import Submission.ZStar.HigmanScratch

/-!
# Higman's criterion on an equivariant idempotent range

This file separates the relative-trace argument from any particular
realization of the summand as a group-algebra ideal.  An equivariant
idempotent makes its range an `R[P]`-submodule.  A corner endomorphism on the
ambient module restricts to that range, where the ambient relative-trace
identity becomes the identity map.
-/

noncomputable section

open scoped BigOperators
open Module

namespace Submission.ZStar
namespace HigmanRange

universe u v w

attribute [local instance] Fintype.ofFinite

/-- An ambient relative trace equal to an equivariant idempotent proves that
the idempotent range is projective.  The equation `E a E = a` is the usual
corner condition; in particular it makes the image of `a` lie in the range
of `E`. -/
theorem projective_range_of_relative_trace
    {R : Type u} {P : Type v} {M : Type w}
    [CommRing R] [Group P] [Finite P]
    [AddCommGroup M] [Module R M]
    [Module (MonoidAlgebra R P) M]
    [IsScalarTower R (MonoidAlgebra R P) M]
    (E : M →ₗ[MonoidAlgebra R P] M)
    (hE : IsIdempotentElem E)
    (a : M →ₗ[R] M)
    (hcorner :
      (E.restrictScalars R).comp
          (a.comp (E.restrictScalars R)) = a)
    (htrace : ∑ g : P, a.conjugate g = E.restrictScalars R)
    [Module.Free R (LinearMap.range E)] :
    Module.Projective (MonoidAlgebra R P) (LinearMap.range E) := by
  let aRange : LinearMap.range E →ₗ[R] LinearMap.range E :=
    { toFun := fun x =>
        ⟨a x, by
          refine ⟨a (E x), ?_⟩
          exact LinearMap.congr_fun hcorner x⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact a.map_add x y
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact a.map_smul r x }
  have hEcomp : E.comp E = E := by
    exact hE
  have htraceRange :
      ∑ g : P, aRange.conjugate g = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx : E (x : M) = x := by
      rcases x.property with ⟨y, hy⟩
      calc
        E (x : M) = E (E y) := by rw [hy]
        _ = E y := LinearMap.congr_fun hEcomp y
        _ = x := hy
    calc
      (((∑ g : P, aRange.conjugate g) x : LinearMap.range E) : M) =
          (∑ g : P, a.conjugate g) (x : M) := by
            simp only [LinearMap.sum_apply, LinearMap.conjugate_apply]
            change E.range.subtype
                (∑ g : P, MonoidAlgebra.single g⁻¹ (1 : R) •
                  aRange (MonoidAlgebra.single g (1 : R) • x)) = _
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro g hg
            rw [map_smul]
            rfl
      _ = E (x : M) := LinearMap.congr_fun htrace x
      _ = x := hx
  exact HigmanScratch.projective_of_relative_trace_id aRange htraceRange

end HigmanRange
end Submission.ZStar
