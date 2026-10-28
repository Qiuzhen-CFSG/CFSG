module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.FixedSpace
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Matrix actions used by the remaining generation-one models

The representation is the actual action on column vectors, restricted to a
matrix subgroup and then to binary scalars. A nonidentity scalar has no nonzero
fixed vector. These helpers support the concrete calculations for 15.3.65,
Aschbacher–Smith, printed p.1152.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.RemainingModels

def matrixNatural {F : Type*} [Field F] [Algebra (ZMod 2) F]
    {n : ℕ} (H : Subgroup (GL (Fin n) F)) :
    Representation (ZMod 2) H (Fin n → F) :=
  restrictScalars ((generalLinearNatural n).comp H.subtype)

theorem matrixNatural_apply {F : Type*} [Field F] [Algebra (ZMod 2) F]
    {n : ℕ} (H : Subgroup (GL (Fin n) F)) (g : H) (v : Fin n → F) :
    matrixNatural H g v = (g.val : Matrix (Fin n) (Fin n) F).mulVec v := rfl

theorem zero_of_scalar_fixed {F : Type*} [Field F]
    {a x : F} (ha : a ≠ 1) (h : a * x = x) : x = 0 := by
  have he : (a - 1) * x = 0 := by simpa [sub_mul] using sub_eq_zero.mpr h
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ha)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.RemainingModels
