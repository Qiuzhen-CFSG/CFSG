module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Natural.Coordinates
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# The actual invariant form on a pair of natural tensor slices

The trace-determinant self-duality turns an invariant bilinear form on the
natural SL₂(4) module into a commuting endomorphism. The scalar-centralizer
theorem identifies that endomorphism with multiplication by a field element.
Applying this to two tensor slices identifies the supplied form, preserving
the literal component marking. No coordinate form is assumed in the input.

Source: Aschbacher–Smith, 14.4.10, printed p.1010, with the canonical
commutator form of 12.8.8(2), printed p.851.
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
open Representation.SL2FourNatural

private theorem invariant_scalar (B : LinearMap.BilinForm Bit Vector)
    (hB : ∀ (g : Special) (u v : Vector), B (action g u) (action g v) = B u v) :
    ∃ c : Field, ∀ u v, B u v = binaryPairing (c • u) v := by
  let T : Vector →ₗ[Bit] Vector := selfDual.symm.toLinearMap.comp B
  have hT (g : Special) (u : Vector) : T (action g u) = action g (T u) := by
    apply selfDual.injective
    apply LinearMap.ext
    intro v
    simp only [T]
    rw [selfDual_equivariant]
    simp only [LinearMap.comp_apply]
    change selfDual (selfDual.symm (B (action g u))) v =
      selfDual (selfDual.symm (B u)) (action g⁻¹ v)
    rw [selfDual.apply_symm_apply, selfDual.apply_symm_apply]
    convert hB g u (action g⁻¹ v) using 1; simp
  let f : Vector →+ Vector :=
    { toFun := T
      map_zero' := by simp
      map_add' := by intro u v; simp [T] }
  obtain ⟨c, hc⟩ := Representation.SL2NaturalOffenders.centralizer_scalar f (by
    intro g v
    change T (action g v) = action g (T v)
    simpa only [action_apply] using hT g v)
  refine ⟨c, ?_⟩
  intro u v
  calc
    B u v = selfDual (T u) v := by simp [T]
    _ = selfDual (c • u) v := by
      have hcu := hc u
      change T u = c • u at hcu
      rw [hcu]
    _ = binaryPairing (c • u) v := rfl

variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module Bit V] {σ : Representation Bit D V}

/-- The supplied form on any two natural tensor slices is a scalar trace-determinant
pairing in the actual point/root coordinates. -/
theorem PointRootCoordinates.form_scalar (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) (n m : Small) :
    ∃ c : Field, ∀ u v : Vector,
      d.form (n ⊗ₜ[Bit] p.vector.symm u) (m ⊗ₜ[Bit] p.vector.symm v) =
        binaryPairing (c • u) v := by
  let left : Vector →ₗ[Bit] IntersectionSpace V :=
    (TensorProduct.mk Bit Small V n).comp p.vector.symm.toLinearMap
  let right : Vector →ₗ[Bit] IntersectionSpace V :=
    (TensorProduct.mk Bit Small V m).comp p.vector.symm.toLinearMap
  apply invariant_scalar (d.form.compl₁₂ left right)
  intro a u v
  change d.form (n ⊗ₜ[Bit] p.vector.symm (action a u))
    (m ⊗ₜ[Bit] p.vector.symm (action a v)) =
      d.form (n ⊗ₜ[Bit] p.vector.symm u) (m ⊗ₜ[Bit] p.vector.symm v)
  have he (q : Small) (w : Vector) :
      sourceTensorAction σ (componentActor hAD p.group a) (q ⊗ₜ[Bit] p.vector.symm w) =
        q ⊗ₜ[Bit] p.vector.symm (action a w) := by
    rw [tensor_tmul, p.component_equivariant]
    change smallAction 1 q ⊗ₜ[Bit] p.vector.symm (action a w) = _
    rw [map_one, Module.End.one_apply]
  simpa only [he] using d.form_invariant (componentActor hAD p.group a)
    (n ⊗ₜ[Bit] p.vector.symm u) (m ⊗ₜ[Bit] p.vector.symm v)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
end
