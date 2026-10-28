module
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Two

/-!
# Adjacent transpositions on the six-dimensional natural S₈ module

Coordinates are the classes of e_i+e_6, for 0≤i<6, in the even-coordinate
subspace of F₂⁸ modulo the all-one vector. Each adjacent transposition acts
by the displayed six binary row masks. The off-diagonal blocks of a
self-extension satisfy the linear parts of the Coxeter relations.
Source: Aschbacher–Smith 14.7.51, printed p.1065, refs/quasithin.pdf.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
abbrev V := Fin 6 → ZMod 2
abbrev Mat := Matrix (Fin 6) (Fin 6) (ZMod 2)

/-- Row masks, with column zero in the least significant bit. -/
def rows : Fin 7 → Fin 6 → BitVec 6 :=
  ![![2,1,4,8,16,32], ![1,4,2,8,16,32], ![1,2,8,4,16,32],
    ![1,2,4,16,8,32], ![1,2,4,8,32,16], ![1,2,4,8,16,63],
    ![62,61,59,55,47,31]]

/-- The actual seven adjacent-transposition matrices. -/
def A (i : Fin 7) : Mat := fun r c => if (rows i r).getLsbD c.val then 1 else 0

/-- Linear square, disjoint-commutation, and adjacent-braid relations on the
upper-right blocks of arbitrary self-extension generators. -/
structure Relations (B : Fin 7 → Mat) : Prop where
  square : ∀ i, A i * B i + B i * A i = 0
  commute : ∀ i j, i.val + 1 < j.val →
    A i * B j + B i * A j = A j * B i + B j * A i
  braid : ∀ i j, j.val = i.val + 1 →
    A i * A j * B i + A i * B j * A i + B i * A j * A i =
      A j * A i * B j + A j * B i * A j + B j * A i * A j
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
