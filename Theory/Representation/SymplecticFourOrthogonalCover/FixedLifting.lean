module

public import Theory.Representation.SymplecticFourOrthogonalCover.Universal
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Geometry

/-!
# Fixed vectors in every binary symplectic central cover

The universal odd-orthogonal cover fixes every lift of a fixed natural vector:
the quadratic correction vanishes on such a vector. Every finite-dimensional
binary cover is a quotient over the original natural projection, so the same
fixed-point lifting holds on all central factors. In particular a displacement
that lies in the full fixed space must be zero; no complement to that fixed
space is asserted.

Source: MS93 (1.5)(ii), used in the last paragraph of (3.4), printed p.869;
the universal-cover theorem is Aschbacher–Smith I.2.3(1).
-/

public section
namespace Representation.SymplecticFourOrthogonalCover
open Matrix Representation.OneCohomology
variable {K : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := K)) W}

theorem cover_fixed_of_projection_fixed
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (g : L (K := K)) (w : W) (hw : binaryNatural g (p w) = p w) :
    σ g w = w := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  obtain ⟨v,rfl⟩ := hf w
  rw [hpf] at hw
  have hv : g.val.val *ᵥ v.1 = v.1 := hw
  have he : binaryAction g v = v := by
    change action g v = v
    rw [action_apply, SylowFlag.correction_eq_zero_of_fixed g.val v.1 hv, hv, add_zero]
  rw [← f.isIntertwining, he]

theorem cover_fixed_preimage
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (A : Subgroup (L (K := K))) :
    fixed (σ.comp A.subtype) =
      (fixed (binaryNatural.comp A.subtype)).comap p.toLinearMap := by
  ext w
  constructor
  · intro hw g
    change binaryNatural g.val (p w) = p w
    rw [← p.isIntertwining]
    exact congrArg p (hw g)
  · intro hw g
    exact cover_fixed_of_projection_fixed p hp g.val w (hw g)

theorem cover_displacement_fixed
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (g : L (K := K)) (w : W) (hw : σ g w - w ∈ fixed σ) :
    σ g w = w := by
  apply cover_fixed_of_projection_fixed p hp g w
  rw [cover_fixed_kernel p hp] at hw
  change p (σ g w - w) = 0 at hw
  rw [map_sub, p.isIntertwining, sub_eq_zero] at hw
  exact hw

end Representation.SymplecticFourOrthogonalCover
