module
public import Mathlib.RepresentationTheory.Basic
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Irreducible
public import Theory.Representation.BinaryAlternatingFiveBorel
/-!
# Inner changes of the five-point action marking

Conjugating the group marking and applying the same element on the natural
module preserves equivariance. This retains the original constituent while
marking its projected A₄ as the fixed point stabilizer.
Source application: Aschbacher–Smith, 13.6.15, printed p.930.
-/

@[expose] public section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
noncomputable def ActionEquiv.innerMarking {ρ : Representation (ZMod 2) D W}
    (e : ActionEquiv ρ (alternatingNatural 5)) (g : alternatingGroup (Fin 5)) :
    ActionEquiv ρ (alternatingNatural 5) where
  groupEquiv := e.groupEquiv.trans (MulAut.conj g)
  linearEquiv := e.linearEquiv.trans (LinearEquiv.ofBijective (alternatingNatural 5 g) (Representation.apply_bijective (alternatingNatural 5) g))
  intertwines d w := by
    change alternatingNatural 5 g (e.linearEquiv (ρ d w)) =
      alternatingNatural 5 (g*e.groupEquiv d*g⁻¹) (alternatingNatural 5 g (e.linearEquiv w))
    rw [e.intertwines]
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
end CFSG.Quasithin.ChapterB.QuasisimpleSource
