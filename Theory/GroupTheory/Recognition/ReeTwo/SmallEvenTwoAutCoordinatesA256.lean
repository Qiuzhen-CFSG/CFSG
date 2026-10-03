module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates
public import Theory.SpecificGroups.ReeTwo.SmallEvenAutProfilesA
public import Theory.SpecificGroups.ReeTwo.EvenCoordinates
/-!
# Coordinates for the order-256 small even candidates

Rows 0 through 10 correspond to candidates 7 through 17. Eight free bits
specify affine carriers in the even Sylow coordinates. Multiplication closure,
explicit words for the eight leading triples, and five tail-root witnesses
identify each carrier with the exact candidate. The resulting equivalences
prove order 256 and make intrinsic counts accessible to finite computation.
The quotient coordinate functions are surjective and use the ordered bases
documented in `SmallEvenAutProfilesA`. Multiplicativity, the Frattini kernel,
and the intrinsic counts remain separate certificates.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified root model.
All finite word identities below are checked by Lean kernel reduction.
-/

open ReeTwo ReeTwo.SylowModel
open ReeTwo.SmallEvenAutProfilesA
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace ReeTwo.SylowModel

public abbrev A256Bits := Fin 8 → ZMod 2

/-- The affine embedding of eight bits in the even Sylow coordinates. -/
@[expose] public def a256Pair (i : Fin 11) (v : A256Bits) : EvenPair :=
  (![
    (⟨v 0, 0, v 1, v 2, v 1, v 3, v 4, v 5, v 6, v 7⟩, v 1 + v 2),
    (⟨v 0, 0, v 1, v 2, v 1, v 3, v 4, v 5, v 6, v 7⟩, 0),
    (⟨v 0, 0, v 1, v 2, v 2, v 3, v 4, v 5, v 6, v 7⟩, 0),
    (⟨v 0, 0, v 1, 0, v 2, v 3, v 4, v 5, v 6, v 7⟩, 0),
    (⟨v 0, 0, 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7⟩, 0),
    (⟨0, v 0, 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7⟩, 0),
    (⟨0, v 0, 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7⟩, v 0),
    (⟨v 0, v 1, v 2, v 2, v 1 + v 2, v 3, v 4, v 5, v 6, v 7⟩, 0),
    (⟨v 0, v 1, v 1, v 1, v 2, v 3, v 4, v 5, v 6, v 7⟩, 0),
    (⟨v 0, v 1, v 2, v 2, 0, v 3, v 4, v 5, v 6, v 7⟩, 0),
    (⟨v 0, v 1, 0, 0, v 2, v 3, v 4, v 5, v 6, v 7⟩, 0)]) i

/-- Read the eight free coordinates of a row. -/
@[expose] public def a256Read (i : Fin 11) (x : EvenPair) : A256Bits :=
  let b := x.1
  (![
    ![b.b0, b.b2, b.b3, b.b5, b.b6, b.b7, b.b8, b.b9],
    ![b.b0, b.b2, b.b3, b.b5, b.b6, b.b7, b.b8, b.b9],
    ![b.b0, b.b2, b.b3, b.b5, b.b6, b.b7, b.b8, b.b9],
    ![b.b0, b.b2, b.b4, b.b5, b.b6, b.b7, b.b8, b.b9],
    ![b.b0, b.b3, b.b4, b.b5, b.b6, b.b7, b.b8, b.b9],
    ![b.b1, b.b3, b.b4, b.b5, b.b6, b.b7, b.b8, b.b9],
    ![b.b1, b.b3, b.b4, b.b5, b.b6, b.b7, b.b8, b.b9],
    ![b.b0, b.b1, b.b2, b.b5, b.b6, b.b7, b.b8, b.b9],
    ![b.b0, b.b1, b.b4, b.b5, b.b6, b.b7, b.b8, b.b9],
    ![b.b0, b.b1, b.b2, b.b5, b.b6, b.b7, b.b8, b.b9],
    ![b.b0, b.b1, b.b4, b.b5, b.b6, b.b7, b.b8, b.b9]]) i

@[expose] public def a256GeneratorPair (i : Fin 11) : Fin 8 → EvenPair :=
  (![
    ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)],
    ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)],
    ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)],
    ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)],
    ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)],
    ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)],
    ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)],
    ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)],
    ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)],
    ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)],
    ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]]) i

@[expose] public def a256WordBits (i : Fin 11) (v : A256Bits) : A256Bits :=
  (![
    ![v 0 + v 1 + v 2, v 1 + v 2, v 3 + v 4, v 1 + v 2 + v 3, v 1 + v 3, v 1 + v 1 * v 2 + v 3 + v 1 * v 3 + v 2 * v 3 + v 4 + v 1 * v 4 + v 2 * v 4 + v 6, v 2 + v 1 * v 2 + v 3 + v 1 * v 3 + v 4 + v 5, v 1 + v 1 * v 3 + v 4 + v 1 * v 4 + v 5 + v 6 + v 7],
    ![v 0 + v 1 + v 2, v 1 + v 2, v 3 + v 4, v 1 + v 2 + v 3, v 1 + v 3, v 1 + v 1 * v 2 + v 3 + v 4 + v 6, v 1 + v 1 * v 2 + v 3 + v 2 * v 3 + v 4 + v 5, v 1 + v 2 * v 3 + v 4 + v 2 * v 4 + v 5 + v 6 + v 7],
    ![v 0 + v 1 + v 2, v 1 + v 2, v 1 + v 4, v 1 + v 2 + v 3, v 1 + v 3, v 2 + v 1 * v 2 + v 3 + v 2 * v 3 + v 4 + v 5, v 2 + v 1 * v 2 + v 2 * v 3 + v 5 + v 6, v 4 + v 2 * v 4 + v 5 + v 6 + v 7],
    ![v 0 + v 1, v 1, v 1 + v 2, v 1 + v 3, v 3 + v 4, v 1 + v 2 + v 4 + v 5, v 2 + v 6, v 1 * v 2 + v 3 + v 5 + v 6 + v 7],
    ![v 0 + v 1, v 1, v 2, v 1 + v 3, v 3 + v 4, v 2 + v 4 + v 5, v 2 + v 6, v 1 * v 2 + v 3 + v 5 + v 6 + v 7],
    ![v 0 + v 1, v 0, v 2, v 0 + v 3, v 0 + v 4, v 0 + v 2 + v 5, v 0 + v 0 * v 1 + v 2 + v 3 + v 4 + v 6, v 0 + v 0 * v 2 + v 7],
    ![v 0 + v 1, v 0, v 2 + v 3, v 0 + v 3, v 0 + v 4, v 0 + v 2 + v 3 + v 0 * v 3 + v 5, v 0 * v 1 + v 2 + v 0 * v 3 + v 4 + v 0 * v 4 + v 6, v 0 * v 1 + v 2 + v 0 * v 2 + v 3 + v 4 + v 0 * v 4 + v 6 + v 7],
    ![v 0 + v 1, v 1, v 1 + v 2, v 3, v 1 + v 4, v 2 + v 1 * v 2 + v 3 + v 5, v 1 * v 2 + v 3 + v 6, v 2 + v 1 * v 2 + v 5 + v 7],
    ![v 0 + v 1, v 1, v 2, v 3, v 1 + v 4, v 2 + v 3 + v 5, v 1 + v 2 + v 3 + v 6, v 2 + v 5 + v 7],
    ![v 0 + v 1, v 1, v 1 + v 2, v 3, v 1 + v 4, v 1 + v 1 * v 2 + v 3 + v 5, v 1 + v 2 + v 1 * v 2 + v 3 + v 6, v 1 + v 1 * v 2 + v 5 + v 7],
    ![v 0 + v 1, v 1, v 1 + v 2, v 3, v 1 + v 4, v 1 + v 2 + v 3 + v 5, v 1 + v 2 + v 3 + v 6, v 1 + v 2 + v 5 + v 7]]) i

/-- The four proposed quotient coordinates in the profile basis. -/
@[expose] public def a256Coordinates (i : Fin 11) (v : A256Bits) : FourQuotient :=
  Multiplicative.ofAdd ((![
    ![v 0 + v 1 + v 2, v 1 + v 2, v 3 + v 4, v 1 + v 2 + v 3],
    ![v 0 + v 1 + v 2, v 1 + v 2, v 3 + v 4, v 2],
    ![v 0 + v 1 + v 2, v 1 + v 2, v 1 + v 4, v 2],
    ![v 0 + v 1, v 1, v 1 + v 2, v 1 + v 2 + v 4 + v 5],
    ![v 0 + v 1, v 1, v 2, v 1 + v 2 + v 3 + v 4 + v 5],
    ![v 0 + v 1, v 0, v 2, v 0 + v 4],
    ![v 0 + v 1, v 0, v 2 + v 3, v 0 + v 4],
    ![v 0 + v 1, v 1, v 1 + v 2, v 1 * v 2 + v 3 + v 6],
    ![v 0 + v 1, v 1, v 2, v 1 + v 2 + v 3 + v 6],
    ![v 0 + v 1, v 1, v 1 + v 2, v 2 + v 5 + v 6],
    ![v 0 + v 1, v 1, v 1 + v 2, v 1 + v 4 + v 5 + v 6]]) i)

public theorem a256Read_pair (i : Fin 11) (v : A256Bits) : a256Read i (a256Pair i v) = v := by
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

public theorem a256Pair_mul (i : Fin 11) (v w : A256Bits) :
    a256Pair i (a256Read i (evenPairMul (a256Pair i v) (a256Pair i w))) =
      evenPairMul (a256Pair i v) (a256Pair i w) := by
  fin_cases i <;> dsimp [a256Pair, a256Read, evenPairMul]
  all_goals try split_ifs
  all_goals apply Prod.ext
  all_goals first | apply Core.ext | skip
  all_goals first | rfl | skip
  all_goals simp only [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
    Core.mul, evenCoreAction]
  all_goals try ring_nf
  all_goals try reduce_mod_char



@[expose] public def a256Index (i : Fin 11) : Fin 59 := ⟨i.val + 7, by omega⟩
@[expose] public def a256Row (i : Fin 11) : Fin 16 := ⟨i.val + 5, by omega⟩

@[expose] public def a256RootGenerator (i : Fin 11) : Fin 8 → SylowModel :=
  (![
    ![root 0, rootOne ^ 2 * root 0 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9],
    ![root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9],
    ![root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9],
    ![root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9],
    ![root 0, root 0 * root 3 * root 5 * root 6 * root 7, root 4 * root 7 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9],
    ![root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9],
    ![root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9],
    ![root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 7, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9],
    ![root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 4 * root 7 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9],
    ![root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9],
    ![root 0, root 0 * root 1 * root 4 * root 6, root 4 * root 7 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9]]) i

public theorem a256GeneratorPair_eq : ∀ (i : Fin 11) (j : Fin 8),
    evenPairElement (a256GeneratorPair i j) = a256RootGenerator i j := by
  decide +kernel


public theorem a256RootGenerator_mem (i : Fin 11) (j : Fin 8) :
    a256RootGenerator i j ∈ smallEvenCandidate (a256Index i) := by
  fin_cases i <;> fin_cases j <;> apply Subgroup.subset_closure
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))


public abbrev A256Tuple := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2

@[expose] public def a256BitsEquiv : A256Tuple ≃ A256Bits where
  toFun w := ![w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1,
    w.2.2.2.2.2.1, w.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2]
  invFun v := (v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7)
  left_inv _ := rfl
  right_inv v := by funext j; fin_cases j <;> rfl

@[expose] public def a256Word (i : Fin 11) (v : A256Bits) : List EvenPair :=
  (List.finRange 8).map (fun j =>
    if a256WordBits i v j = 0 then (1, 0) else a256GeneratorPair i j)


public theorem a256Word_mem (i : Fin 11) (v : A256Bits) :
    evenPairElement (evenPairProd (a256Word i v)) ∈ smallEvenCandidate (a256Index i) := by
  rw [evenPairElement_prod]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
  split_ifs
  · exact Subgroup.one_mem _
  · rw [a256GeneratorPair_eq]
    exact a256RootGenerator_mem i j

public theorem a256Head_check : ∀ (i : Fin 11) (a b c : ZMod 2),
    evenPairProd (a256Word i ![a, b, c, 0, 0, 0, 0, 0]) =
      a256Pair i ![a, b, c, 0, 0, 0, 0, 0] := by decide +kernel


@[expose] public def a256TailPair (j : Fin 5) : EvenPair := (Core.root ⟨j.val + 5, by omega⟩, 0)

public theorem a256Tail_check : ∀ (i : Fin 11) (j : Fin 5),
    evenPairProd (a256Word i (fun k => if k.val = j.val + 3 then 1 else 0)) =
      a256TailPair j := by decide +kernel


private theorem a256Tail_mem (i : Fin 11) (j : Fin 5) :
    root ⟨j.val + 5, by omega⟩ ∈ smallEvenCandidate (a256Index i) := by
  have h := a256Word_mem i (fun k => if k.val = j.val + 3 then 1 else 0)
  rw [a256Tail_check] at h
  exact h


private theorem a256CoreTail_mem (i : Fin 11) (x : Core)
    (h0 : x.b0 = 0) (h1 : x.b1 = 0) (h2 : x.b2 = 0)
    (h3 : x.b3 = 0) (h4 : x.b4 = 0) :
    (SemidirectProduct.inl x : SylowModel) ∈ smallEvenCandidate (a256Index i) := by
  have hn := congrArg (SemidirectProduct.inl : Core →* SylowModel) (Core.normal_form x)
  simp only [map_mul, map_pow, h0, h1, h2, h3, h4, ZMod.val_zero, pow_zero, one_mul] at hn
  rw [← hn]
  repeat apply Subgroup.mul_mem
  · exact Subgroup.pow_mem _ (a256Tail_mem i 0) _
  · exact Subgroup.pow_mem _ (a256Tail_mem i 1) _
  · exact Subgroup.pow_mem _ (a256Tail_mem i 2) _
  · exact Subgroup.pow_mem _ (a256Tail_mem i 3) _
  · exact Subgroup.pow_mem _ (a256Tail_mem i 4) _


private theorem a256EvenAction_two (x : Core) : evenCoreAction (evenCoreAction x) = x := by
  apply Core.ext <;> simp only [evenCoreAction] <;> ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
  all_goals ring_nf
  all_goals reduce_mod_char



private def a256Head (v : A256Bits) : A256Bits := ![v 0, v 1, v 2, 0, 0, 0, 0, 0]

private def a256Tail (v : A256Bits) : Core := ⟨0, 0, 0, 0, 0, v 3, v 4, v 5, v 6, v 7⟩

private def a256TwistedTail (i : Fin 11) (v : A256Bits) : Core :=
  if (a256Pair i (a256Head v)).2 = 0 then a256Tail v else evenCoreAction (a256Tail v)

private theorem a256Head_tail (i : Fin 11) (v : A256Bits) :
    evenPairMul (a256Pair i (a256Head v)) (a256TwistedTail i v, 0) = a256Pair i v := by
  unfold evenPairMul a256TwistedTail
  split_ifs <;> simp only [a256EvenAction_two]
  all_goals fin_cases i
  all_goals apply Prod.ext
  all_goals first | apply Core.ext | skip
  all_goals dsimp [a256Pair, a256Head, a256Tail]
  all_goals simp only [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
    Core.mul, zero_mul, mul_zero, zero_add, add_zero]


private theorem a256TwistedTail_mem (i : Fin 11) (v : A256Bits) :
    (SemidirectProduct.inl (a256TwistedTail i v) : SylowModel) ∈
      smallEvenCandidate (a256Index i) := by
  apply a256CoreTail_mem
  all_goals unfold a256TwistedTail
  all_goals split_ifs <;> simp [a256Tail, evenCoreAction]


public theorem a256Pair_mem (i : Fin 11) (v : A256Bits) :
    evenPairElement (a256Pair i v) ∈ smallEvenCandidate (a256Index i) := by
  rw [← a256Head_tail, evenPairElement_mul]
  apply Subgroup.mul_mem
  · have h := a256Word_mem i (a256Head v)
    rw [a256Head, a256Head_check] at h
    exact h
  · exact a256TwistedTail_mem i v


public theorem a256Pair_zero : ∀ i : Fin 11, a256Pair i 0 = (1, 0) := by decide +kernel

private def a256Monoid (i : Fin 11) : Submonoid SylowModel where
  carrier := Set.range (fun v => evenPairElement (a256Pair i v))
  one_mem' := ⟨0, by change evenPairElement (a256Pair i 0) = 1; rw [a256Pair_zero]; rfl⟩
  mul_mem' := by
    rintro x y ⟨v, rfl⟩ ⟨w, rfl⟩
    refine ⟨a256Read i (evenPairMul (a256Pair i v) (a256Pair i w)), ?_⟩
    change evenPairElement (a256Pair i _) = _
    rw [a256Pair_mul, evenPairElement_mul]

private def a256Subgroup (i : Fin 11) : Subgroup SylowModel :=
  { a256Monoid i with
    inv_mem' := by
      intro x hx
      have hp : x ^ 4096 = 1 := by simpa only [card] using (pow_card_eq_one' (x := x))
      have hi : x ^ 4095 = x⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ]
        exact hp
      rw [← hi]
      exact (a256Monoid i).pow_mem hx 4095 }

public theorem a256Candidate_eq_closure (i : Fin 11) :
    smallEvenCandidate (a256Index i) = Subgroup.closure (Set.range (a256RootGenerator i)) := by
  have range8 (v : Fin 8 → SylowModel) :
      Set.range v = {v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7} := by
    ext x
    simp [Fin.exists_fin_succ, eq_comm]
  rw [range8]
  fin_cases i <;> rfl



private theorem a256GeneratorPair_restore : ∀ (i : Fin 11) (j : Fin 8),
    a256Pair i (a256Read i (a256GeneratorPair i j)) = a256GeneratorPair i j := by
  decide +kernel

private theorem a256Candidate_le (i : Fin 11) :
    smallEvenCandidate (a256Index i) ≤ a256Subgroup i := by
  rw [a256Candidate_eq_closure]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  refine ⟨a256Read i (a256GeneratorPair i j), ?_⟩
  change evenPairElement (a256Pair i _) = _
  rw [a256GeneratorPair_restore, a256GeneratorPair_eq]


@[expose] public def a256AmbientRead (i : Fin 11) (x : SylowModel) : A256Bits :=
  a256Read i (x.left, 0)

public theorem a256AmbientRead_pair (i : Fin 11) (v : A256Bits) :
    a256AmbientRead i (evenPairElement (a256Pair i v)) = v := by
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

@[expose] public def a256Element (i : Fin 11) (v : A256Bits) : smallEvenCandidate (a256Index i) :=
  ⟨evenPairElement (a256Pair i v), a256Pair_mem i v⟩

/-- Eight independent bits parametrize exactly the original candidate. -/
@[expose] public def a256Equiv (i : Fin 11) : A256Bits ≃ smallEvenCandidate (a256Index i) where
  toFun := a256Element i
  invFun x := a256AmbientRead i x.val
  left_inv := a256AmbientRead_pair i
  right_inv x := by
    apply Subtype.ext
    obtain ⟨v, hv⟩ := a256Candidate_le i x.property
    change evenPairElement (a256Pair i (a256AmbientRead i x.val)) = x.val
    rw [← hv, a256AmbientRead_pair]


/-- Each of the eleven exact generator closures has order 256. -/
public theorem a256Candidate_card (i : Fin 11) : Nat.card (smallEvenCandidate (a256Index i)) = 256 := by
  rw [← Nat.card_congr (a256Equiv i), Nat.card_fun]
  simp


/-- The quotient coordinate function on the original candidate. -/
@[expose] public def a256Map (i : Fin 11) (x : smallEvenCandidate (a256Index i)) : FourQuotient :=
  a256Coordinates i ((a256Equiv i).symm x)


@[expose] public def a256Section (i : Fin 11) (v : FourQuotient) : A256Bits :=
  (![
    ![v.toAdd 0 + v.toAdd 1, v.toAdd 1, 0, v.toAdd 1 + v.toAdd 3, v.toAdd 1 + v.toAdd 2 + v.toAdd 3, 0, 0, 0],
    ![v.toAdd 0 + v.toAdd 1, v.toAdd 1 + v.toAdd 3, v.toAdd 3, v.toAdd 2, 0, 0, 0, 0],
    ![v.toAdd 0 + v.toAdd 1, v.toAdd 1 + v.toAdd 3, v.toAdd 3, 0, v.toAdd 1 + v.toAdd 2 + v.toAdd 3, 0, 0, 0],
    ![v.toAdd 0 + v.toAdd 1, v.toAdd 1, v.toAdd 1 + v.toAdd 2, 0, v.toAdd 2 + v.toAdd 3, 0, 0, 0],
    ![v.toAdd 0 + v.toAdd 1, v.toAdd 1, v.toAdd 2, v.toAdd 1 + v.toAdd 2 + v.toAdd 3, 0, 0, 0, 0],
    ![v.toAdd 1, v.toAdd 0 + v.toAdd 1, v.toAdd 2, 0, v.toAdd 1 + v.toAdd 3, 0, 0, 0],
    ![v.toAdd 1, v.toAdd 0 + v.toAdd 1, v.toAdd 2, 0, v.toAdd 1 + v.toAdd 3, 0, 0, 0],
    ![v.toAdd 0 + v.toAdd 1, v.toAdd 1, v.toAdd 1 + v.toAdd 2, v.toAdd 1 + v.toAdd 1 * v.toAdd 2 + v.toAdd 3, 0, 0, 0, 0],
    ![v.toAdd 0 + v.toAdd 1, v.toAdd 1, v.toAdd 2, v.toAdd 1 + v.toAdd 2 + v.toAdd 3, 0, 0, 0, 0],
    ![v.toAdd 0 + v.toAdd 1, v.toAdd 1, v.toAdd 1 + v.toAdd 2, 0, 0, v.toAdd 1 + v.toAdd 2 + v.toAdd 3, 0, 0],
    ![v.toAdd 0 + v.toAdd 1, v.toAdd 1, v.toAdd 1 + v.toAdd 2, 0, v.toAdd 1 + v.toAdd 3, 0, 0, 0]]) i

public theorem a256Coordinates_section : ∀ (i : Fin 11) (v : FourQuotient),
    a256Coordinates i (a256Section i v) = v := by decide +kernel

/-- All sixteen values occur on each exact candidate. -/
public theorem a256Map_surjective (i : Fin 11) : Function.Surjective (a256Map i) := by
  intro v
  refine ⟨a256Equiv i (a256Section i v), ?_⟩
  change a256Coordinates i ((a256Equiv i).symm (a256Equiv i (a256Section i v))) = v
  rw [Equiv.symm_apply_apply, a256Coordinates_section]


/-- Multiplication on the candidate, evaluated in the polynomial coordinates. -/
public theorem a256Element_mul (i : Fin 11) (v w : A256Bits) :
    a256Element i v * a256Element i w =
      a256Element i (a256Read i (evenPairMul (a256Pair i v) (a256Pair i w))) := by
  apply Subtype.ext
  change evenPairElement (a256Pair i v) * evenPairElement (a256Pair i w) = _
  change evenPairElement (a256Pair i v) * evenPairElement (a256Pair i w) =
    evenPairElement (a256Pair i _)
  rw [← evenPairElement_mul, a256Pair_mul]

public theorem a256Index_eq (i : Fin 11) : a256Index i = fourIndex (a256Row i) := by
  fin_cases i <;> rfl

/-- The actual intrinsic fiber counts of the fixed coordinate function. -/
@[expose] public noncomputable def a256CoordinateProfile (i : Fin 11) (v : FourQuotient) : ℕ × ℕ :=
  (Nat.card {x : smallEvenCandidate (a256Index i) // a256Map i x = v ∧
      MulAut.orderCentralizerTest (fourTests (a256Row i) 0) x},
    Nat.card {x : smallEvenCandidate (a256Index i) // a256Map i x = v ∧
      MulAut.orderCentralizerTest (fourTests (a256Row i) 1) x})

end ReeTwo.SylowModel
