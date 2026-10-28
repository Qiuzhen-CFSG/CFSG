module
public import Theory.Representation.SymplecticFourOrthogonalCover.Universal
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer.Commutant
public import Theory.Representation.NormalPSubgroupKernel

/-!
# Full-actor fixed lifts in the symplectic orthogonal cover

Every natural vector has a unique singular lift in the five-dimensional
orthogonal cover. The scalar commutant and quadratic polar form show that
all compatible normalizing actors preserve singularity. Twisted universality
and uniqueness of maps over the original projection therefore transport
fixed vectors through every central quotient, including nonsplit kernels
and actors inducing field automorphisms.

The application in `SylowFixed` constructs a noncentral vector fixed by the
original Sylow subgroup. This supplies the missing fixed-intersection step
in Aschbacher--Smith 11.2.2, printed p.767, using I.2.3, printed p.413.
The argument adapts the existing `SL2OrthogonalCover.FullFixed` proof to
the genuine derived Sp4 action; no model lift is assumed.
-/

public noncomputable section
open Matrix ClassicalOrthogonal Representation
open Representation.OneCohomology Representation.OneCohomology.CentralCoverOriginalAction
open Representation.SymplecticFourOrthogonalCover
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.FullFixed
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
/-- Singular representatives over the same natural vector agree. -/
theorem singular_unique (u v : Space (K := F))
    (hp : projection u = projection v) (hu : formB 2 F u = 0)
    (hv : formB 2 F v = 0) : u = v := by
  have hfirst : u.1 = v.1 := hp
  apply Prod.ext hfirst
  apply CharTwo.sq_injective
  rw [formB_apply] at hu hv
  rw [hfirst] at hu
  exact add_left_cancel (hu.trans hv.symm)

omit [Algebra (ZMod 2) F] in
/-- The finite characteristic-two field supplies a singular representative. -/
theorem exists_singular (v : Natural (K := F)) :
    ∃ u : Space (K := F), projection u = v ∧ formB 2 F u = 0 := by
  obtain ⟨c,hc⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F))
    (formD 2 F v)
  change c ^ 2 = formD 2 F v at hc
  refine ⟨(v,c),rfl,?_⟩
  rw [formB_apply]
  change formD 2 F v + c ^ 2 = 0
  rw [hc,CharTwo.add_self_eq_zero]

/-- Compatible binary normalizers preserve the actual singular set. -/
theorem normalizer_preserves_singular
    (a : MulAut (L (K := F))) (e : Natural (K := F) ≃ₗ[ZMod 2] Natural (K := F))
    (E : Space (K := F) ≃ₗ[ZMod 2] Space (K := F))
    (he : ∀ l v, e (symplecticDerivedNatural 2 l v) = symplecticDerivedNatural 2 (a l) (e v))
    (hE : ∀ l u, E (action l u) = action (a l) (E u))
    (hover : ∀ u, projection (E u) = e (projection u)) :
    ∀ u, formB 2 F (E u) = 0 ↔ formB 2 F u = 0 := by
  apply lift_preserves_singular (symplecticDerivedNatural (k := F) 2)
    (action (K := F)) projection binaryProjection_isCover
    (fun f hf => SymplecticConjugatePair.Ambient.Normalizer.Commutant.natural_centralizer_scalar f hf)
    (formD 2 F).polarBilin ?_ polar_invariant (formB 2 F) action_preserves
    ?_ a e E he hE hover
  · exact ⟨fun v hv => polarD_separating v hv,
      fun v hv => polarD_separating v (fun w => by
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
        exact hv w)⟩
  · intro u v
    simp only [polarB_apply, CharTwo.two_eq_zero, zero_mul, add_zero]
    rfl

variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A vector fixed by the full normalizing actor lifts to a fixed vector. -/
theorem fixed_lift
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (τ : Representation (ZMod 2) A W) (η : Representation (ZMod 2) A (Natural (K := F)))
    (a : A → MulAut (L (K := F)))
    (hτ : ∀ g l w, τ g (σ l w) = σ (a g l) (τ g w))
    (hη : ∀ g l v, η g (binaryNatural l v) = binaryNatural (a g l) (η g v))
    (hover : ∀ g w, p (τ g w) = η g (p w))
    (v : Natural (K := F)) (hv : ∀ g, η g v = v) :
    ∃ w : W, p w = v ∧ ∀ g, τ g w = w := by
  have hmodel := binaryProjection_isCover (K := F)
  have hd := (binary_kernel_finrank (K := F)).trans binary_dual_H1_finrank.symm
  obtain ⟨f,_,hf⟩ := exists_cover_quotient p hp
  obtain ⟨u,hu,hsing⟩ := exists_singular v
  refine ⟨f u,(hf u).trans hu,fun g => ?_⟩
  obtain ⟨E,hE,hproj⟩ := exists_lift (binaryProjection (K := F)) hmodel hd
    (a g) (actorEquiv η g) (hη g)
  have hsingE := normalizer_preserves_singular (a g) (actorEquiv η g) E
    (hη g) hE hproj u
  have hEu : E u = u := singular_unique (E u) u
    (by change binaryProjection (E u) = binaryProjection u; rw [hproj]; exact hu ▸ hv g)
    (hsingE.mpr hsing) hsing
  have heq : f.toLinearMap.comp E.toLinearMap = (τ g).comp f.toLinearMap := by
    apply lift_unique (binaryAction (K := F)) (σ.comp (a g).toMonoidHom)
      hmodel.2.2 p.toLinearMap (fun w hw l => hp.2.1 hw (a g l))
    · intro l x
      change f (E (binaryAction l x)) = σ (a g l) (f (E x))
      rw [hE,f.isIntertwining]
    · intro l x
      change τ g (f (binaryAction l x)) = σ (a g l) (τ g (f x))
      rw [f.isIntertwining,hτ]
    · intro x
      change p (f (E x)) = p (τ g (f x))
      rw [hf,hproj,hover,hf]
      rfl
  have he := LinearMap.congr_fun heq u
  change f (E u) = τ g (f u) at he
  rw [hEu] at he
  exact he.symm

/-- A normalizing two-group fixes a vector outside the actual central kernel. -/
theorem exists_fixed_noncentral [Finite A]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (τ : Representation (ZMod 2) A W) (η : Representation (ZMod 2) A (Natural (K := F)))
    (a : A → MulAut (L (K := F)))
    (hτ : ∀ g l w, τ g (σ l w) = σ (a g l) (τ g w))
    (hη : ∀ g l v, η g (binaryNatural l v) = binaryNatural (a g l) (η g v))
    (hover : ∀ g w, p (τ g w) = η g (p w)) (hA : IsPGroup 2 A) :
    ∃ w : W, p w ≠ 0 ∧ ∀ g, τ g w = w := by
  obtain ⟨v,hv,hfix⟩ := pGroup_fix_nonzero_vector
    (by rw [ringChar.eq (ZMod 2) 2]; decide)
    (by simpa only [ringChar.eq (ZMod 2) 2] using hA) η
  obtain ⟨w,hw,hfixed⟩ := fixed_lift σ p hp τ η a hτ hη hover v hfix
  exact ⟨w,hw ▸ hv,hfixed⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.FullFixed

