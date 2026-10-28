module
public import Theory.Representation.SymplecticFourOrthogonalCover.EmbeddedProjection
public import Mathlib.RepresentationTheory.Basic
/-!
# Equivariant projection onto the literal embedded subgroup

Transport a surjective linear quotient through an injective embedding, retaining
its value on every embedded vector. The original conjugation identity upstairs
then gives the actual subgroup conjugation formula downstairs. This supports
both ambient semilinear and inner natural actions with the same projection.
-/

public section
noncomputable section
open Subgroup Representation
namespace Representation.SymplecticFourOrthogonalCover

theorem exists_equivariant_embedded_projection
    {G D W V : Type*} [Group G] [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup V] [Module (ZMod 2) V]
    (U A : Subgroup G) (hn : A ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) D W) (τ : Representation (ZMod 2) D V)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (p : W →ₗ[ZMod 2] V) (hp : Function.Surjective p)
    (hproj : ∀ d w, p (σ d w)=τ d (p w))
    (δ : A →* D)
    (hconj : ∀ (a : A) w,
      j (Multiplicative.ofAdd (σ (δ a) w))=a.val*j (Multiplicative.ofAdd w)*a.val⁻¹) :
    ∃ π : U →* Multiplicative V, Function.Surjective π ∧
      (∀ w : W, π ⟨j (Multiplicative.ofAdd w),by rw [←hjr]; exact ⟨_,rfl⟩⟩ =
        Multiplicative.ofAdd (p w)) ∧
      (∀ (a : A) (u : U),
        π ⟨a.val*u.val*a.val⁻¹,(mem_normalizer_iff.mp (hn a.property) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (τ (δ a) (π u).toAdd)) := by
  obtain ⟨π,hπ⟩ := exists_embedded_projection U j hj hjr p
  refine ⟨π,?_,hπ,?_⟩
  · intro v
    obtain ⟨w,hw⟩ := hp v.toAdd
    refine ⟨⟨j (Multiplicative.ofAdd w),by rw [←hjr]; exact ⟨_,rfl⟩⟩,?_⟩
    rw [hπ,hw,ofAdd_toAdd]
  · intro a u
    have hu : u.val ∈ j.range := by rw [hjr]; exact u.property
    obtain ⟨w,hw⟩ := hu
    have he : u=⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
    subst u
    have hπw : π ⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ = Multiplicative.ofAdd (p w.toAdd) := hπ w.toAdd
    rw [hπw]
    have hh := hconj a w.toAdd
    have hz : (⟨a.val*j w*a.val⁻¹,(mem_normalizer_iff.mp (hn a.property) (j w)).mp
          (by rw [←hjr]; exact ⟨w,rfl⟩)⟩ : U) =
        ⟨j (Multiplicative.ofAdd (σ (δ a) w.toAdd)),by rw [←hjr]; exact ⟨_,rfl⟩⟩ :=
      Subtype.ext hh.symm
    rw [hz,hπ,toAdd_ofAdd]
    exact congrArg Multiplicative.ofAdd (hproj (δ a) w.toAdd)
end Representation.SymplecticFourOrthogonalCover
