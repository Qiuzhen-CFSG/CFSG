module

public import Theory.Representation.SymplecticFourOrthogonalCover.Universal
public import Mathlib.Algebra.Algebra.ZMod

/-!
# I.2.3: the universal orthogonal cover for Sp₄(F)′

The direct quadratic lift of the genuine derived symplectic action is a
five-dimensional nondegenerate orthogonal space. Its fixed space is its
one-dimensional polar radical and the kernel of its natural projection.
Restriction to the binary field gives the universal L-cover, equivariantly
and over the original projection. Every binary L-cover is its quotient.

These theorems include F₂. They concern the universal L-cover; the original
ambient G-action and the remaining Sylow/root geometry are separate steps
of the parent I.2.3 assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma I.2.3(1),
printed p.413/PDF p.424, using Remark I.1.5 and Lemma I.1.6, printed p.408.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterI.ModuleCovers.SymplecticFour
open Representation Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open ClassicalOrthogonal
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The actual five-dimensional orthogonal universal binary L-cover, including
Sp₄(2)′, with compatibility over the given natural projection. -/
theorem universal_orthogonal :
    Module.finrank F (Space (K := F)) = 5 ∧
      (formB 2 F).Nondegenerate ∧
      (∀ g v, formB 2 F (action g v) = formB 2 F v) ∧
      fixed (action (K := F)) = (formB 2 F).polarBilin.ker ∧
      Module.finrank F (formB 2 F).polarBilin.ker = 1 ∧
      ∃ e : Module.Dual (ZMod 2) (cocycles (binaryNatural (K := F)).dual) ≃ₗ[ZMod 2] Space (K := F),
        (∀ g u, e ((universalAction (binaryNatural (K := F)).dual).dual g u) = action g (e u)) ∧
        ∀ u, projection (e u) = universalCoverProjection (binaryNatural (K := F)) u := by
  refine ⟨space_finrank, quadratic_nondegenerate, action_preserves, ?_, ?_, universal_equiv⟩
  · exact fixed_radical.trans radical_eq_polar_ker
  · rw [← radical_eq_polar_ker]
    exact radical_finrank

/-- The concrete orthogonal model maps onto every binary L-cover over its
original natural projection; no F-module structure on that cover is assumed. -/
theorem arbitrary_cover_quotient
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p) :
    ∃ f : (binaryAction (K := F)).IntertwiningMap σ, Function.Surjective f ∧
      ∀ v, p (f v) = projection v :=
  exists_cover_quotient p hp

end CFSG.Quasithin.ChapterI.ModuleCovers.SymplecticFour
