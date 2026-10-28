module
public import Theory.Representation.SL2OrthogonalCover.FullFixed.Geometry

/-!
# Fixed vectors in arbitrary natural central covers

The universal orthogonal cover has a unique singular lift of every natural
vector. Compatible normalizers preserve that lift; cover-map uniqueness then
transports it to every fully moved central quotient. The central kernel is
allowed to move. This is the natural-module fixed-span step in Aschbacher–Smith
10.2.9, printed p.751, using I.2.3.
-/

public noncomputable section
open Representation Representation.OneCohomology
open Representation.OneCohomology.CentralCoverOriginalAction
namespace Representation.SL2OrthogonalCover.FullFixed
variable {F W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- A compatible normalizer fixes the singular lift of every fixed quotient
vector, even when its central covering kernel is not fixed pointwise. -/
theorem fixed_lift_of_cover
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    {σ : Representation (ZMod 2) (SL F) W}
    (q : σ.IntertwiningMap (binaryNatural (F := F))) (hq : IsCover q)
    {P : Type*} [Group P]
    (a : P →* MulAut (SL F)) (η : Representation (ZMod 2) P (Plane F))
    (τ : Representation (ZMod 2) P W)
    (ha : ∀ g l v, η g (binaryNatural l v) = binaryNatural (a g l) (η g v))
    (ht : ∀ g l w, τ g (σ l w) = σ (a g l) (τ g w))
    (hqt : ∀ g w, q (τ g w) = η g (q w))
    {v : Plane F} (hv : ∀ g, η g v = v) :
    ∃ w : W, q w = v ∧ ∀ g, τ g w = w := by
  have hd : Module.finrank (ZMod 2) (binaryProjection (F := F)).toLinearMap.ker =
      Module.finrank (ZMod 2) (H1 (binaryNatural (F := F)).dual) := by
    rw [binary_kernel_finrank n hF, binary_dual_H1_finrank n hn hF]
  have hp := binaryProjection_isCover (card_gt_two n hn hF)
  obtain ⟨f,_,hfp⟩ := exists_quotient_of_finrank_ker_eq
    (binaryProjection (F := F)) hp hd q hq
  obtain ⟨u,hu,huz⟩ := exists_singular v
  refine ⟨f u, (hfp u).trans hu, fun g => ?_⟩
  obtain ⟨E,hE,hEp⟩ := exists_lift (binaryProjection (F := F)) hp hd
    (a g) (actorEquiv η g) (ha g)
  have hEu : E u = u := singular_unique (E u) u
    (by change binaryProjection (E u) = binaryProjection u
        rw [hEp]; change η g (projection u) = projection u; rw [hu,hv])
    ((normalizer_preserves_singular (card_gt_two n hn hF) (a g)
      (actorEquiv η g) E (ha g) hE hEp u).mpr huz) huz
  have he : f.toLinearMap.comp E.toLinearMap = (τ g).comp f.toLinearMap := by
    apply lift_unique (binaryAction (F := F)) (σ.comp (a g).toMonoidHom)
      hp.2.2 q.toLinearMap (fun w hw l => hq.2.1 hw (a g l))
    · intro l w
      change f (E (binaryAction l w)) = σ (a g l) (f (E w))
      rw [hE,f.isIntertwining]
    · intro l w
      change τ g (f (binaryAction l w)) = σ (a g l) (τ g (f w))
      rw [f.isIntertwining,ht]
    · intro w
      change q (f (E w)) = q (τ g (f w))
      rw [hfp,hqt,hfp,hEp]
      rfl
  have hh := LinearMap.congr_fun he u
  change f (E u) = τ g (f u) at hh
  exact hh.symm.trans (congrArg f hEu)
end Representation.SL2OrthogonalCover.FullFixed

