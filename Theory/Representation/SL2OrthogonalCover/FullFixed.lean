module
public import Theory.Representation.SL2OrthogonalCover.FullFixed.Geometry

/-!
# Full-actor fixed-point lifting for natural SL₂ covers

A fixed natural vector has a unique singular lift in the universal orthogonal
cover. Twisted universality lifts each original normalizing actor; uniqueness
makes the quotient to the given central cover equivariant. This proves fixation
by the whole actor, even when its action on the SL₂-central kernel is nontrivial.
For a two-group, a nonzero fixed natural vector therefore gives a fixed vector
outside the actual kernel. No splitting or Sylow enlargement is assumed.

Source: Aschbacher–Smith I.1.5 and I.2.3(2), printed pp.408,413.
-/
@[expose] public section
noncomputable section

namespace Representation.SL2OrthogonalCover.FullFixed
open Representation.OneCohomology Representation.OneCohomology.CentralCoverOriginalAction
variable {F A W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group A] [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- Every vector fixed by the entire original actor lifts through the genuine
natural SL₂ central cover. Its central kernel need only be SL₂-fixed. -/
theorem fixed_lift (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (σ : Representation (ZMod 2) (SL F) W)
    (p : σ.IntertwiningMap (binaryNatural (F := F))) (hp : IsCover p)
    (τ : Representation (ZMod 2) A W) (η : Representation (ZMod 2) A (Plane F))
    (a : A → MulAut (SL F))
    (hτ : ∀ g l w, τ g (σ l w) = σ (a g l) (τ g w))
    (hη : ∀ g l v, η g (natural l v) = natural (a g l) (η g v))
    (hover : ∀ g w, p (τ g w) = η g (p w))
    (v : Plane F) (hv : ∀ g, η g v = v) :
    ∃ w : W, p w = v ∧ ∀ g, τ g w = w := by
  have hmodel := binaryProjection_isCover (card_gt_two n hn hF)
  have hd : Module.finrank (ZMod 2) (binaryProjection (F := F)).toLinearMap.ker =
      Module.finrank (ZMod 2) (H1 (binaryNatural (F := F)).dual) := by
    rw [binary_kernel_finrank n hF, binary_dual_H1_finrank n hn hF]
  obtain ⟨f, _, hf⟩ := exists_quotient_of_finrank_ker_eq
    (binaryProjection (F := F)) hmodel hd p hp
  obtain ⟨u, hu, hsing⟩ := exists_singular v
  refine ⟨f u, (hf u).trans hu, fun g => ?_⟩
  obtain ⟨E, hE, hproj⟩ := exists_lift (binaryProjection (F := F)) hmodel hd
    (a g) (actorEquiv η g) (hη g)
  have hsingE := normalizer_preserves_singular (card_gt_two n hn hF)
    (a g) (actorEquiv η g) E (hη g) hE hproj u
  have hEu : E u = u := singular_unique (E u) u
    (by change binaryProjection (E u) = binaryProjection u; rw [hproj]; exact hu ▸ hv g)
    (hsingE.mpr hsing) hsing
  have heq : f.toLinearMap.comp E.toLinearMap = (τ g).comp f.toLinearMap := by
    apply lift_unique (binaryAction (F := F)) (σ.comp (a g).toMonoidHom)
      hmodel.2.2 p.toLinearMap
      (fun w hw l => hp.2.1 hw (a g l))
    · intro l x
      change f (E (binaryAction l x)) = σ (a g l) (f (E x))
      rw [hE, f.isIntertwining]
    · intro l x
      change τ g (f (binaryAction l x)) = σ (a g l) (τ g (f x))
      rw [f.isIntertwining, hτ]
    · intro x
      change p (f (E x)) = p (τ g (f x))
      rw [hf, hproj, hover, hf]
      rfl
  have he := LinearMap.congr_fun heq u
  change f (E u) = τ g (f u) at he
  rw [hEu] at he
  exact he.symm

/-- The full two-group has a fixed vector outside the actual central kernel. -/
theorem exists_fixed_noncentral [Finite A]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (σ : Representation (ZMod 2) (SL F) W)
    (p : σ.IntertwiningMap (binaryNatural (F := F))) (hp : IsCover p)
    (τ : Representation (ZMod 2) A W) (η : Representation (ZMod 2) A (Plane F))
    (a : A → MulAut (SL F))
    (hτ : ∀ g l w, τ g (σ l w) = σ (a g l) (τ g w))
    (hη : ∀ g l v, η g (natural l v) = natural (a g l) (η g v))
    (hover : ∀ g w, p (τ g w) = η g (p w)) (hA : IsPGroup 2 A) :
    ∃ w : W, p w ≠ 0 ∧ ∀ g, τ g w = w := by
  obtain ⟨v, hv, hfix⟩ := pGroup_fix_nonzero_vector
    (by rw [ringChar.eq (ZMod 2) 2]; decide)
    (by simpa only [ringChar.eq (ZMod 2) 2] using hA) η
  obtain ⟨w, hw, hfixed⟩ := fixed_lift n hn hF σ p hp τ η a hτ hη hover v hfix
  exact ⟨w, hw ▸ hv, hfixed⟩
end Representation.SL2OrthogonalCover.FullFixed
