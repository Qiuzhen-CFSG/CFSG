module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Fusion.Finite
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Matrix certificates for the fixed Sylow coordinates

The 32 monomial matrices realize the torus and signed transposition. Their
multiplication and inverse-transpose formulas certify the coordinate law.
The eight determinant-one witnesses conjugate the full listed actors to
one of the two specified representatives. `Fusion.Carrier` transports these
matrix equations into the literal graph extension.

Source: the fixed-Sylow branch of Aschbacher--Smith E.1.14(7), p.214;
the witness search is recorded in `OuterReselection/FusionWitnesses.g`.
All certificates use kernel reduction on small finite tuples.
-/

public section
open scoped MatrixGroups Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection.Fusion
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

@[expose] def u : (ZMod 5)ˣ := ⟨2,3,by decide,by decide⟩
@[expose] def diagonalMatrix (d : D) : Matrix (Fin 3) (Fin 3) (ZMod 5) :=
  Matrix.diagonal ![(u ^ d.1.val : (ZMod 5)ˣ),
    (((u ^ d.1.val) * (u ^ d.2.val))⁻¹ : (ZMod 5)ˣ), (u ^ d.2.val : (ZMod 5)ˣ)]
theorem diagonal_det : ∀ d, (diagonalMatrix d).det = 1 := by decide +kernel
@[expose] def diagonal (d : D) : SL(3, ZMod 5) := ⟨diagonalMatrix d, diagonal_det d⟩
@[expose] def swap : SL(3, ZMod 5) := ⟨!![4,0,0;0,0,4;0,4,0], by decide +kernel⟩
@[expose] def mat (l : L) : SL(3, ZMod 5) :=
  diagonal l.1 * (if l.2 then swap else 1)

theorem mat_inj : Function.Injective mat := by decide +kernel
theorem mat_mul : ∀ a b : L,
    mat (a.1 + sw a.2 b.1, a.2 ^^ b.2) = mat a * mat b := by decide +kernel
theorem mat_graph : ∀ a : L,
    mat (-a.1, a.2) = (Matrix.SpecialLinearGroup.transpose (mat a))⁻¹ := by decide +kernel
theorem mat_one : mat ((0,0),false) = 1 := by decide +kernel

/-- The left-conjugating special-linear matrices from the diagnostic. -/
@[expose] def witnessMatrix : Fin 8 → Matrix (Fin 3) (Fin 3) (ZMod 5) :=
  ![!![0,4,4;3,0,0;0,4,1], !![0,4,3;0,4,2;1,0,0],
    !![0,0,1;0,4,0;1,0,0], !![4,0,0;0,0,4;0,4,0],
    1, 1, !![0,1,1;0,1,4;2,0,0], !![0,4,3;0,4,2;1,0,0]]
theorem witness_det : ∀ i, (witnessMatrix i).det = 1 := by decide +kernel
@[expose] def witness (i : Fin 8) : SL(3, ZMod 5) := ⟨witnessMatrix i, witness_det i⟩
@[expose] def target (i : Fin 8) : Fin 8 := if i = 0 ∨ i = 1 ∨ i = 5 then 5 else 4

/-- The explicitly tabulated image of each listed coordinate. -/
@[expose] def witnessAction : Fin 8 → C → C :=
  ![(fun a => if a = (((0,0),false),false) then (((0,0),false),false) else
      if a = (((0,2),false),false) then (((2,2),false),false) else
      if a = (((0,2),true),false) then (((0,2),false),false) else
      if a = (((0,0),true),false) then (((2,0),false),false) else
      if a = (((2,1),false),true) then (((2,2),false),true) else
      if a = (((2,3),false),true) then (((0,0),false),true) else
      if a = (((2,1),true),true) then (((0,2),false),true) else
      if a = (((2,3),true),true) then (((2,0),false),true) else ce),
    (fun a => if a = (((0,0),false),false) then (((0,0),false),false) else
      if a = (((0,2),false),false) then (((2,0),false),false) else
      if a = (((0,3),true),false) then (((2,2),false),false) else
      if a = (((0,1),true),false) then (((0,2),false),false) else
      if a = (((0,3),false),true) then (((2,0),false),true) else
      if a = (((0,1),false),true) then (((0,0),false),true) else
      if a = (((0,2),true),true) then (((2,2),false),true) else
      if a = (((0,0),true),true) then (((0,2),false),true) else ce),
    (fun a => if a = (((0,0),false),false) then (((0,0),false),false) else
      if a = (((2,2),false),false) then (((2,2),false),false) else
      if a = (((2,0),false),false) then (((0,2),false),false) else
      if a = (((0,2),false),false) then (((2,0),false),false) else
      if a = (((0,3),false),true) then (((3,0),false),true) else
      if a = (((2,1),false),true) then (((1,2),false),true) else
      if a = (((2,3),false),true) then (((3,2),false),true) else
      if a = (((0,1),false),true) then (((1,0),false),true) else ce),
    (fun a => if a = (((0,0),false),false) then (((0,0),false),false) else
      if a = (((2,2),false),false) then (((2,0),false),false) else
      if a = (((2,0),false),false) then (((2,2),false),false) else
      if a = (((0,2),false),false) then (((0,2),false),false) else
      if a = (((3,3),false),true) then (((3,2),false),true) else
      if a = (((1,1),false),true) then (((1,2),false),true) else
      if a = (((1,3),false),true) then (((1,0),false),true) else
      if a = (((3,1),false),true) then (((3,0),false),true) else ce),
    (fun a => if a = (((0,0),false),false) then (((0,0),false),false) else
      if a = (((2,2),false),false) then (((2,2),false),false) else
      if a = (((2,0),false),false) then (((2,0),false),false) else
      if a = (((0,2),false),false) then (((0,2),false),false) else
      if a = (((1,0),false),true) then (((1,0),false),true) else
      if a = (((3,2),false),true) then (((3,2),false),true) else
      if a = (((3,0),false),true) then (((3,0),false),true) else
      if a = (((1,2),false),true) then (((1,2),false),true) else ce),
    (fun a => if a = (((0,0),false),false) then (((0,0),false),false) else
      if a = (((2,2),false),false) then (((2,2),false),false) else
      if a = (((2,0),false),false) then (((2,0),false),false) else
      if a = (((0,2),false),false) then (((0,2),false),false) else
      if a = (((0,0),false),true) then (((0,0),false),true) else
      if a = (((2,2),false),true) then (((2,2),false),true) else
      if a = (((2,0),false),true) then (((2,0),false),true) else
      if a = (((0,2),false),true) then (((0,2),false),true) else ce),
    (fun a => if a = (((0,0),false),false) then (((0,0),false),false) else
      if a = (((0,2),false),false) then (((2,0),false),false) else
      if a = (((0,2),true),false) then (((0,2),false),false) else
      if a = (((0,0),true),false) then (((2,2),false),false) else
      if a = (((0,0),false),true) then (((1,2),false),true) else
      if a = (((0,2),false),true) then (((3,2),false),true) else
      if a = (((0,2),true),true) then (((1,0),false),true) else
      if a = (((0,0),true),true) then (((3,0),false),true) else ce),
    (fun a => if a = (((0,0),false),false) then (((0,0),false),false) else
      if a = (((0,2),false),false) then (((2,0),false),false) else
      if a = (((0,3),true),false) then (((2,2),false),false) else
      if a = (((0,1),true),false) then (((0,2),false),false) else
      if a = (((2,2),false),true) then (((1,2),false),true) else
      if a = (((2,0),false),true) then (((3,2),false),true) else
      if a = (((2,1),true),true) then (((1,0),false),true) else
      if a = (((2,3),true),true) then (((3,0),false),true) else ce)]
theorem witness_action_certificate : ∀ i a, a ∈ codes i →
    witnessAction i a ∈ codes (target i) ∧ (witnessAction i a).2 = a.2 ∧
    witness i * mat a.1 *
      (if a.2 then Matrix.SpecialLinearGroup.transpose (witness i) else (witness i)⁻¹) =
      mat (witnessAction i a).1 := by decide +kernel

/-- Every listed element has the certified matrix image in its target list. -/
theorem witness_certificate (i : Fin 8) (a : C) (ha : a ∈ codes i) :
    ∃ b ∈ codes (target i), b.2 = a.2 ∧ witness i * mat a.1 *
      (if a.2 then Matrix.SpecialLinearGroup.transpose (witness i) else (witness i)⁻¹) =
      mat b.1 := ⟨witnessAction i a, witness_action_certificate i a ha⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection.Fusion
