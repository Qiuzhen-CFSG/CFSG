module
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.TypeTags.Hom
/-!
# A literal subgroup projection from embedded additive coordinates

An injective multiplicative embedding with prescribed range transports a
linear quotient to that exact ambient subgroup. Its evaluation on embedded
vectors remains explicit, preserving the original kernel and action diagram.
-/

public section
noncomputable section
namespace Representation.SymplecticFourOrthogonalCover
variable {G : Type*} [Group G] (U : Subgroup G)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Transport a linear projection to the literal image subgroup. -/
theorem exists_embedded_projection
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (p : W →ₗ[ZMod 2] V) :
    ∃ π : U →* Multiplicative V, ∀ w : W,
      π ⟨j (Multiplicative.ofAdd w),by rw [←hjr]; exact ⟨_,rfl⟩⟩ = Multiplicative.ofAdd (p w) := by
  let e : Multiplicative W ≃* U :=
    (MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hjr)
  let π : U →* Multiplicative V := p.toAddMonoidHom.toMultiplicative.comp e.symm.toMonoidHom
  refine ⟨π,fun w => ?_⟩
  have he : (⟨j (Multiplicative.ofAdd w),by rw [←hjr]; exact ⟨_,rfl⟩⟩ : U) =
      e (Multiplicative.ofAdd w) := rfl
  rw [he]
  change Multiplicative.ofAdd (p ((e.symm (e (Multiplicative.ofAdd w))).toAdd)) = _
  rw [e.symm_apply_apply,toAdd_ofAdd]
end Representation.SymplecticFourOrthogonalCover
