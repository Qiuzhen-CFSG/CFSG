module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
A compact kernel-checked certificate excludes order seven in the four-
dimensional binary symplectic group. Row pairing constraints enumerate only the
symplectic candidates; the relation between the fourth power and inverse cube
supplies the order-seven test. The exposed finite matrix operations are
intentionally computational inputs to the certificate consumer.
-/

public section

open Matrix

namespace BinarySymplecticSeven

abbrev Mat := Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def J4 : Mat := !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]

@[expose] def row (code : Fin 16) : Fin 4 → ZMod 2 :=
  ![(code.val % 2 : ℕ), (code.val / 2 % 2 : ℕ),
    (code.val / 4 % 2 : ℕ), (code.val / 8 % 2 : ℕ)]

@[expose] def decode (aa bb cc dd : Fin 16) : Mat :=
  ![row aa, row bb, row cc, row dd]

@[expose] def pairing (left right : Fin 4 → ZMod 2) : ZMod 2 :=
  left 0 * right 1 + left 1 * right 0 + left 2 * right 3 + left 3 * right 2

@[expose] def fastMul (left right : Mat) : Mat := fun ii jj =>
  left ii 0 * right 0 jj + left ii 1 * right 1 jj +
    left ii 2 * right 2 jj + left ii 3 * right 3 jj

@[expose] def fourth (actor : Mat) : Mat := fastMul (fastMul actor actor) (fastMul actor actor)

@[expose] def swap : Fin 4 → Fin 4 := ![1, 0, 3, 2]

@[expose] def inverseCube (actor : Mat) : Mat :=
  fun ii jj => fastMul (fastMul actor actor) actor (swap jj) (swap ii)

@[expose] def entriesEqual (left right : Mat) : Prop := ∀ ii jj, left ii jj = right ii jj

instance (left right : Mat) : Decidable (entriesEqual left right) := by
  unfold entriesEqual
  exact @Nat.decidableForallFin 4 _ (fun ii =>
    @Nat.decidableForallFin 4 _ (fun jj => inferInstance))

@[expose] def finalCheck (aa bb cc dd : Fin 16) : Prop :=
  entriesEqual (fourth (decode aa bb cc dd)) (inverseCube (decode aa bb cc dd)) →
    entriesEqual (decode aa bb cc dd) 1

instance (aa bb cc dd : Fin 16) : Decidable (finalCheck aa bb cc dd) := by
  unfold finalCheck
  infer_instance

@[expose] def fourthRow (aa bb cc : Fin 16) : Prop :=
  ∀ dd : Fin 16, pairing (row aa) (row dd) = 0 →
    pairing (row bb) (row dd) = 0 → pairing (row cc) (row dd) = 1 →
    finalCheck aa bb cc dd

instance (aa bb cc : Fin 16) : Decidable (fourthRow aa bb cc) := by
  unfold fourthRow
  infer_instance

@[expose] def thirdRow (aa bb : Fin 16) : Prop :=
  ∀ cc : Fin 16, pairing (row aa) (row cc) = 0 →
    pairing (row bb) (row cc) = 0 → fourthRow aa bb cc

instance (aa bb : Fin 16) : Decidable (thirdRow aa bb) := by
  unfold thirdRow
  infer_instance

@[expose] def secondRow (aa : Fin 16) : Prop :=
  ∀ bb : Fin 16, pairing (row aa) (row bb) = 1 → thirdRow aa bb

instance (aa : Fin 16) : Decidable (secondRow aa) := by
  unfold secondRow
  infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem certificate : ∀ aa bb : Fin 16,
    pairing (row aa) (row bb) = 1 → ∀ cc : Fin 16,
    pairing (row aa) (row cc) = 0 → pairing (row bb) (row cc) = 0 →
    ∀ dd : Fin 16, pairing (row aa) (row dd) = 0 →
    pairing (row bb) (row dd) = 0 → pairing (row cc) (row dd) = 1 →
    (∀ ii jj, fourth (decode aa bb cc dd) ii jj =
      inverseCube (decode aa bb cc dd) ii jj) →
    ∀ ii jj, decode aa bb cc dd ii jj = (1 : Mat) ii jj := by
  change ∀ aa, secondRow aa
  decide

end BinarySymplecticSeven
