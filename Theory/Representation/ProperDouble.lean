module
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Proper submodules of a homogeneous double

Coordinate projections show that a nonzero proper submodule of two copies
of a simple module is one copy with the original actor marking. A nonzero
projection is surjective; a nonzero kernel would supply the second copy and
make the embedding onto. This is the linear one-copy step in the original
fixed-layer argument, Aschbacher–Smith13.7.16(2), printed p.944.
-/

public section
namespace Representation
variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- A nonzero proper submodule of two copies of a simple module is one copy. -/
theorem equiv_of_injective_map_to_proper_double [IsIrreducible σ]
    (i : ρ.IntertwiningMap (σ.prod σ)) (hi : Function.Injective i)
    (hne : i ≠ 0) (hproper : ¬ Function.Surjective i) : Nonempty (ρ.Equiv σ) := by
  let f := (IntertwiningMap.fst k σ σ).comp i
  let g := (IntertwiningMap.snd k σ σ).comp i
  have hpair (v : V) : i v = (f v,g v) := rfl
  by_cases hf : f = 0
  · have hg : g ≠ 0 := by
      intro hg
      apply hne
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      apply Prod.ext
      · change f v = 0
        exact congrArg (fun t : ρ.IntertwiningMap σ => t v) hf
      · change g v = 0
        exact congrArg (fun t : ρ.IntertwiningMap σ => t v) hg
    have hgi : Function.Injective g := by
      intro v w he
      apply hi
      apply Prod.ext
      · exact (congrArg (fun t : ρ.IntertwiningMap σ => t v) hf).trans
          (congrArg (fun t : ρ.IntertwiningMap σ => t w) hf).symm
      · exact he
    exact ⟨g.ofBijective ⟨hgi,(IsIrreducible.surjective_or_eq_zero g).resolve_right hg⟩⟩
  · have hfs : Function.Surjective f :=
      (IsIrreducible.surjective_or_eq_zero f).resolve_right hf
    let q : f.ker.toRepresentation.IntertwiningMap σ :=
      (g.toLinearMap.comp f.ker.toSubmodule.subtype).intertwiningMap_of_isIntertwiningMap _ _
        (by intro a v; exact LinearMap.congr_fun (g.isIntertwining' a) v.val)
    have hq : q = 0 := by
      by_contra hq
      have hqs := (IsIrreducible.surjective_or_eq_zero q).resolve_right hq
      apply hproper
      rintro ⟨v,w⟩
      obtain ⟨x,hx⟩ := hfs v
      obtain ⟨y,hy⟩ := hqs (w-g x)
      refine ⟨x+y.val,?_⟩
      rw [map_add,hpair,hpair]
      apply Prod.ext
      · change f x + f y.val = v
        rw [hx,show f y.val = 0 from y.property,add_zero]
      · change g x + g y.val = w
        change g y.val = w-g x at hy
        rw [hy,add_sub_cancel]
    have hfi : Function.Injective f := by
      apply (LinearMap.ker_eq_bot).mp
      apply bot_unique
      intro v hv
      apply hi
      apply Prod.ext
      · change f v = f 0
        change f v = 0 at hv
        simpa only [map_zero] using hv
      · change g v = g 0
        have he := congrArg (fun t : f.ker.toRepresentation.IntertwiningMap σ =>
          t ⟨v,hv⟩) hq
        change g v = 0 at he
        simpa only [map_zero] using he
    exact ⟨f.ofBijective ⟨hfi,hfs⟩⟩
end Representation
