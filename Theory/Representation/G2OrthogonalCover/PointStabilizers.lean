module
public import Theory.Representation.G2OrthogonalCover.Universal
public import Theory.Representation.G2OrthogonalCover.BinaryFusion
public import Theory.Representation.CentralCoverOriginalAction

/-!
# Point stabilizers through a binary G₂ central cover

A central cover of the derived natural module is a quotient of the binary
seven-dimensional trace-zero module. Uniqueness on its commutator-generated
source makes the quotient map equivariant for the original whole actor.
Two lifts of the same natural vector have different octonion norms, so an
automorphism fixing that vector fixes both lifts. This treats the natural
and Weyl alternatives with their actual action and covering map.

Source: Aschbacher–Smith, I.2.3 and 13.8.27, printed pp.413,963.
The octonion model retains the attribution in LICENSES/ATLAS.txt.
-/

public section

open Representation Representation.OneCohomology Subgroup
open Representation.OneCohomology.CentralCoverOriginalAction
namespace Atlas.G2.Natural.OrthogonalCover
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A vector and its natural image have the same original actor stabilizer. -/
theorem binary_cover_point_fixed_iff
    (L : Subgroup D) [L.Normal]
    (e : L ≃* commutator (Model (ZMod 2)))
    (f : D →* Model (ZMod 2))
    (hf : ∀ a : L, f a = (e a : Model (ZMod 2)))
    (ρ : Representation (ZMod 2) D W)
    (p : W →ₗ[ZMod 2] Space (ZMod 2))
    (hp : Function.Surjective p)
    (hk : p.ker ≤ fixed (ρ.comp L.subtype))
    (hfull : Coinvariants.ker (ρ.comp L.subtype) = ⊤)
    (he : ∀ a w, p (ρ a w) = Natural.action (ZMod 2) (f a) (p w))
    (a : D) (w : W) :
    ρ a w = w ↔ Natural.action (ZMod 2) (f a) (p w) = p w := by
  constructor
  · intro h
    rw [← he, h]
  · intro h
    let α : Representation (ZMod 2) (commutator (Model (ZMod 2))) W :=
      (ρ.comp L.subtype).comp e.symm.toMonoidHom
    let P : Representation.IntertwiningMap α (binaryNatural (ZMod 2)) :=
      p.intertwiningMap_of_isIntertwiningMap _ _ (by
        intro g v
        change p (ρ (e.symm g) v) = Natural.action (ZMod 2) g (p v)
        rw [he, hf, e.apply_symm_apply])
    have hP : IsCover P := by
      refine ⟨hp, ?_, ?_⟩
      · intro v hv g
        exact hk hv (e.symm g)
      · exact (commutator_comp_equiv (ρ.comp L.subtype) e.symm).trans hfull
    obtain ⟨q, hq, hover⟩ := exists_quotient (ZMod 2) P hP
    let ζ := (traceZeroAction (ZMod 2)).comp f
    let η := (Natural.action (ZMod 2)).comp f
    have hζ : ζ.comp L.subtype = (OrthogonalCover.action (ZMod 2)).comp e.toMonoidHom := by
      apply MonoidHom.ext
      intro b
      apply LinearMap.ext
      intro v
      change traceZeroAction (ZMod 2) (f b) v = traceZeroAction (ZMod 2) (e b) v
      rw [hf]
    have hgen : Coinvariants.ker (ζ.comp L.subtype) = ⊤ := by
      rw [hζ, commutator_comp_equiv, commutator_eq_top]
    have hqL (b : L) (v) : q (ζ b v) = ρ b (q v) := by
      have hh := LinearMap.congr_fun (q.isIntertwining' (e b)) v
      change q (traceZeroAction (ZMod 2) (e b) v) = ρ (e.symm (e b)) (q v) at hh
      simpa only [ζ, MonoidHom.comp_apply, hf, e.symm_apply_apply] using hh
    have hwhole := quotient_original_equivariant L (η := η) (ζ := ζ) (τ := ρ)
      (mk (ZMod 2)) p q.toLinearMap (fun _ _ => rfl) he hk hgen hqL hover
    obtain ⟨v, rfl⟩ := hq w
    have hv : mk (ZMod 2) (traceZeroAction (ZMod 2) (f a) v) = mk (ZMod 2) v := by
      change Natural.action (ZMod 2) (f a) (mk (ZMod 2) v) = mk (ZMod 2) v
      have hover' (u) : p (q u) = mk (ZMod 2) u := hover u
      simpa only [hover'] using h
    have hnorm : form (ZMod 2) (traceZeroAction (ZMod 2) (f a) v) = form (ZMod 2) v :=
      SplitOctonion.automorphism_norm (f a) v.val
    have hfix : traceZeroAction (ZMod 2) (f a) v = v := by
      rcases (binary_mk_eq_iff _ _).mp hv with hv | hv
      · exact hv
      · rw [hv, binary_form_add_identity] at hnorm
        exact False.elim (one_ne_zero (add_left_cancel (hnorm.trans (add_zero _).symm)))
    exact (hwhole a v).symm.trans (congrArg q hfix)

end Atlas.G2.Natural.OrthogonalCover
