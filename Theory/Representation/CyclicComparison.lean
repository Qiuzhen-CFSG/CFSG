module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Cyclic comparison through a kernel fixed modulo relations

Evaluate the regular representation on a marked orbit. If a second equivariant
map kills the model map's kernel, it descends to the model's image. When that
image and the target are simple, a nonzero descended map is an isomorphism;
its inverse followed by inclusion embeds the target in the model.

It suffices that every displacement of a kernel vector lies in a relation
space killed by the second map. Its kernel image is then fixed, and simplicity
together with a moved vector forces that image to vanish. The relation space
need not be the whole kernel, and the model need not itself be simple.

This elementary comparison is used for the binary SL₄ mixed tensor in
Aschbacher–Smith K.3.2, printed pp.454–455, and the graph-support argument of
Guralnick–Malle, Classification of 2F-modules II, author manuscript, 4.8(3).
The concrete kernel and simplicity calculations are separate obligations.
-/

@[expose] public section

namespace Representation
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
/-- Evaluation of the left regular representation on the orbit of a marked vector. -/
noncomputable def cyclicOrbitMap (σ : Representation k G V) (v : V) :
    IntertwiningMap (Representation.leftRegular k G) σ where
  toLinearMap := σ.asAlgebraHom.toLinearMap.flip v
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change σ.asAlgebraHom (Representation.leftRegular k G g x) v =
      σ g (σ.asAlgebraHom x v)
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | single h a =>
      rw [Representation.ofMulAction_single]
      simp [Representation.asAlgebraHom_single, smul_eq_mul, map_mul]

/-- A basis element evaluates to the corresponding scalar multiple of the orbit vector. -/
@[simp] theorem cyclicOrbitMap_single (σ : Representation k G V) (v : V) (g : G) (a : k) :
    cyclicOrbitMap σ v (MonoidAlgebra.single g a) = a • σ g v := by
  change σ.asAlgebraHom (MonoidAlgebra.single g a) v = _
  simp [Representation.asAlgebraHom_single]

/-- Every invariant subspace containing the seed contains the entire cyclic image. -/
theorem cyclicOrbitMap_range_le (σ : Representation k G V) (S : Subrepresentation σ)
    {v : V} (hv : v ∈ S) : (cyclicOrbitMap σ v).range ≤ S := by
  rintro _ ⟨x, rfl⟩
  change cyclicOrbitMap σ v x ∈ S.toSubmodule
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simpa using S.toSubmodule.add_mem ha hb
  | single g a =>
    rw [cyclicOrbitMap_single]
    exact S.toSubmodule.smul_mem a (S.apply_mem_toSubmodule g hv)

end Representation

open Representation
namespace Representation.IntertwiningMap
variable {k G X Y V : Type*} [Field k] [Monoid G]
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
  [AddCommGroup V] [Module k V]
  {τ : Representation k G X} {ρ : Representation k G Y} {σ : Representation k G V}

/-- A simple representation with a moved vector has no nonzero invariant vectors. -/
theorem fixed_eq_zero_of_irreducible_moving [IsIrreducible σ]
    (hm : ∃ (g : G) (v : V), σ g v ≠ v)
    {w : V} (hw : ∀ g, σ g w = w) : w = 0 := by
  by_contra hn
  let f : IntertwiningMap (Representation.trivial k G k) σ :=
    (LinearMap.toSpanSingleton k V w).intertwiningMap_of_isIntertwiningMap _ _
      (fun g a => by simp [hw])
  have hf : f ≠ 0 := by
    intro h
    have hh := DFunLike.congr_fun h 1
    exact hn (by simpa [f, LinearMap.toSpanSingleton_apply] using hh)
  have hsur := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  obtain ⟨g, v, hv⟩ := hm
  obtain ⟨a, rfl⟩ := hsur v
  apply hv
  simpa using (LinearMap.congr_fun (f.isIntertwining' g) a).symm

set_option backward.isDefEq.respectTransparency false in
/-- Descend an equivariant map to the image of another map which has smaller kernel. -/
noncomputable def descendRange (p : IntertwiningMap τ ρ) (q : IntertwiningMap τ σ)
    (hk : p.toLinearMap.ker ≤ q.toLinearMap.ker) :
    IntertwiningMap p.range.toRepresentation σ := by
  let F : p.toLinearMap.range →ₗ[k] V :=
    (p.toLinearMap.ker.liftQ q.toLinearMap hk).comp
      p.toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hF (x : X) : F ⟨p x, ⟨x, rfl⟩⟩ = q x := by
    change (p.toLinearMap.ker.liftQ q.toLinearMap hk)
      (p.toLinearMap.quotKerEquivRange.symm ⟨p.toLinearMap x, _⟩) = q.toLinearMap x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  refine ⟨F, ?_⟩
  intro g
  ext ⟨y, x, rfl⟩
  change F ⟨ρ g (p x), _⟩ = σ g (F ⟨p x, _⟩)
  simp_rw [← p.isIntertwining, hF]
  exact LinearMap.congr_fun (q.isIntertwining' g) x

set_option backward.isDefEq.respectTransparency false in
/-- The descended map agrees with the original map on every represented vector. -/
@[simp] theorem descendRange_apply (p : IntertwiningMap τ ρ) (q : IntertwiningMap τ σ)
    (hk : p.toLinearMap.ker ≤ q.toLinearMap.ker) (x : X) :
    descendRange p q hk ⟨p x, ⟨x, rfl⟩⟩ = q x := by
  change (p.toLinearMap.ker.liftQ q.toLinearMap hk)
    (p.toLinearMap.quotKerEquivRange.symm ⟨p.toLinearMap x, _⟩) = q.toLinearMap x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- A nonzero map to a simple target reverses through a simple model image. -/
theorem exists_nonzero_reverse_of_simple_range
    [IsIrreducible σ] (p : IntertwiningMap τ ρ) (q : IntertwiningMap τ σ)
    (hq : q ≠ 0) (hp : IsIrreducible p.range.toRepresentation)
    (hk : p.toLinearMap.ker ≤ q.toLinearMap.ker) :
    ∃ f : IntertwiningMap σ ρ, f ≠ 0 := by
  let : IsIrreducible p.range.toRepresentation := hp
  let d := descendRange p q hk
  have hd : d ≠ 0 := by
    intro h
    apply hq
    ext x
    have hh := DFunLike.congr_fun h ⟨p x, ⟨x, rfl⟩⟩
    simpa [d] using hh
  let e := d.ofBijective ((IsIrreducible.bijective_or_eq_zero d).resolve_right hd)
  let incl : IntertwiningMap p.range.toRepresentation ρ :=
    ⟨p.range.toSubmodule.subtype, fun _ => rfl⟩
  refine ⟨incl.comp e.symm.toIntertwiningMap, ?_⟩
  intro hz
  apply hd
  ext y
  have hy := DFunLike.congr_fun hz (e y)
  have he : e.symm (e y) = y := e.toLinearEquiv.symm_apply_apply y
  change (e.symm (e y) : Y) = 0 at hy
  rw [he] at hy
  have hy0 : y = 0 := Subtype.ext hy
  simp [hy0]

/-- Kernel displacements killed by a nontrivial simple target suffice for comparison. -/
theorem exists_nonzero_reverse_of_kernel_displacements
    [IsIrreducible σ] (p : IntertwiningMap τ ρ) (q : IntertwiningMap τ σ)
    (hq : q ≠ 0) (hp : IsIrreducible p.range.toRepresentation)
    (hm : ∃ (g : G) (v : V), σ g v ≠ v)
    (R : Submodule k X) (hR : R ≤ q.toLinearMap.ker)
    (hdisp : ∀ x, p x = 0 → ∀ g, τ g x - x ∈ R) :
    ∃ f : IntertwiningMap σ ρ, f ≠ 0 := by
  apply exists_nonzero_reverse_of_simple_range p q hq hp
  intro x hx
  change q x = 0
  apply fixed_eq_zero_of_irreducible_moving hm
  intro g
  have hh := hR (hdisp x hx g)
  change q (τ g x - x) = 0 at hh
  simpa only [map_sub, q.isIntertwining, sub_eq_zero] using hh
end Representation.IntertwiningMap
