module

public import Theory.GroupAction.BinaryQuadraticPairing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# The binary model for the five-four action

We realize the even subsets of the five-element affine line by their first
four characteristic values; the fifth value is the parity of the first four.
Translation by one and multiplication by two give the five-four action.
The pairing is intersection parity, including the fifth coordinate.

An equivariant map is determined by its values at one four-element subset and
one two-element subset. A kernel-checked table enumerates the resulting 256
possibilities. Self-orthogonality, one seven-term relation, and a nonidentity
zero imply orthogonality to a preimage under the involution displacement.

Source: the binary action underlying Parrott, *A characterization of the Tits'
simple group* (1972), pp.673–674 and p.678 preceding equation (2).
-/

set_option synthInstance.maxSize 4096

namespace Theory.GroupAction.FiveFourBinaryModel

/-- Four binary coordinates for the even subsets of a five-element set. -/
public abbrev Space := Multiplicative (Fin 4 → ZMod 2)

/-- The omitted fifth coordinate. -/
@[expose] public def parity (v : Space) : ZMod 2 := v.toAdd 0 + v.toAdd 1 + v.toAdd 2 + v.toAdd 3

/-- Translation by one on the five underlying points. -/
@[expose] public def translate (v : Space) : Space := Multiplicative.ofAdd
  ![parity v, v.toAdd 0, v.toAdd 1, v.toAdd 2]

/-- Multiplication by two on the five underlying points. -/
@[expose] public def turn (v : Space) : Space := Multiplicative.ofAdd
  ![v.toAdd 0, v.toAdd 3, v.toAdd 1, parity v]

/-- Parity of intersection of two even subsets. -/
@[expose] public def pairing (v w : Space) : Multiplicative (ZMod 2) := Multiplicative.ofAdd
  (v.toAdd 0 * w.toAdd 0 + v.toAdd 1 * w.toAdd 1 +
   v.toAdd 2 * w.toAdd 2 + v.toAdd 3 * w.toAdd 3 + parity v * parity w)

/-- The model intersection pairing is nondegenerate on either side. -/
public theorem pairing_nondegenerate :
    (∀ x : Space, (∀ y, pairing x y = 1) → x = 1) ∧
    (∀ y : Space, (∀ x, pairing x y = 1) → y = 1) := by decide +kernel


/-- The two coordinate permutations preserve intersection parity. -/
public theorem pairing_invariant :
    (∀ x y, pairing (translate x) (translate y) = pairing x y) ∧
    (∀ x y, pairing (turn x) (turn y) = pairing x y) := by decide +kernel


/-- Intersection parity is multiplicative in both entries. -/
public theorem pairing_mul :
    (∀ x y z, pairing (x * y) z = pairing x z * pairing y z) ∧
    (∀ x y z, pairing x (y * z) = pairing x y * pairing x z) := by decide +kernel

private def vec (n : Fin 16) : Space :=
  Multiplicative.ofAdd fun i => if (BitVec.ofFin n).getLsb i then 1 else 0

private theorem vec_bijective : Function.Bijective vec := by decide +kernel

private def table (a b : Space) : Fin 16 → Space :=
  ![1, b, translate (turn b), translate b, translate^[4] (turn b),
    translate^[2] (turn b), translate^[2] b, a, translate^[4] b, turn b,
    translate^[3] (turn b), translate^[4] a, translate^[3] b,
    translate^[3] a, translate^[2] a, translate a]

private theorem table_identity : ∀ n, table (vec 7) (vec 1) n = vec n := by decide +kernel

private theorem table_natural (q : Space → Space) (h1 : q 1 = 1)
    (ht : ∀ x, q (translate x) = translate (q x))
    (hs : ∀ x, q (turn x) = turn (q x)) (n : Fin 16) :
    q (table (vec 7) (vec 1) n) = table (q (vec 7)) (q (vec 1)) n := by
  fin_cases n <;> simp [table, h1, ht, hs]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
private theorem candidates : ∀ a b : Space,
    (∀ n, pairing (vec n) (table a b n) = 1) →
    (table a b 7 * table a b 3 * table a b 5 * table a b 6 *
      table a b 1 * table a b 2 * table a b 4 = 1) →
    (∃ n, vec n ≠ 1 ∧ table a b n = 1) →
    (∀ n m, table a b n = turn (turn (vec m)) * vec m →
      table a b n ≠ 1 → pairing (vec n) (vec m) = 1) := by decide +kernel

/-- The orthogonality assertion in the fixed binary model. -/
public theorem square_displacement_orthogonality
    (q : Space → Space) (h1 : q 1 = 1)
    (ht : ∀ x, q (translate x) = translate (q x))
    (hs : ∀ x, q (turn x) = turn (q x))
    (hq : ∀ a b c, q (a * b * c) * q (a * b) * q (a * c) *
      q (b * c) * q a * q b * q c = 1)
    (hself : ∀ x, pairing x (q x) = 1)
    (hzero : ∃ x, x ≠ 1 ∧ q x = 1)
    (v w : Space) (hdisp : q v = turn (turn w) * w) (hne : q v ≠ 1) :
    pairing v w = 1 := by
  have htable (n) : table (q (vec 7)) (q (vec 1)) n = q (vec n) := by
    rw [← table_identity n]
    exact (table_natural q h1 ht hs n).symm
  have hquad :
      table (q (vec 7)) (q (vec 1)) 7 * table (q (vec 7)) (q (vec 1)) 3 *
        table (q (vec 7)) (q (vec 1)) 5 * table (q (vec 7)) (q (vec 1)) 6 *
        table (q (vec 7)) (q (vec 1)) 1 * table (q (vec 7)) (q (vec 1)) 2 *
        table (q (vec 7)) (q (vec 1)) 4 = 1 := by
    simp only [htable]
    have h12 : vec 1 * vec 2 = vec 3 := by decide +kernel
    have h14 : vec 1 * vec 4 = vec 5 := by decide +kernel
    have h24 : vec 2 * vec 4 = vec 6 := by decide +kernel
    have h34 : vec 3 * vec 4 = vec 7 := by decide +kernel
    simpa only [h12, h34, h14, h24] using hq (vec 1) (vec 2) (vec 4)
  have hz : ∃ n, vec n ≠ 1 ∧ table (q (vec 7)) (q (vec 1)) n = 1 := by
    obtain ⟨x, hx, hxq⟩ := hzero
    obtain ⟨n, rfl⟩ := vec_bijective.2 x
    exact ⟨n, hx, (htable n).trans hxq⟩
  obtain ⟨n, rfl⟩ := vec_bijective.2 v
  obtain ⟨m, rfl⟩ := vec_bijective.2 w
  exact candidates (q (vec 7)) (q (vec 1))
    (fun i => by rw [htable]; exact hself _) hquad hz n m
    ((htable n).trans hdisp) (by rwa [htable])

/-- Compatible coordinates for a dual pair of actions, with the supplied
actor's square represented by the model involution. No square-map conditions
are imposed by this structure. -/
public structure Coordinates {A V W : Type*} [Group A] [Group V] [Group W]
    (d : BinaryQuadraticPairing A V W) (g : A) where
  left : V ≃* Space
  right : W ≃* Space
  translationActor : A
  turnActor : A
  left_translate : ∀ v, left (d.leftAction translationActor v) = translate (left v)
  right_translate : ∀ w, right (d.rightAction translationActor w) = translate (right w)
  left_turn : ∀ v, left (d.leftAction turnActor v) = turn (left v)
  right_turn : ∀ w, right (d.rightAction turnActor w) = turn (right w)
  right_square : ∀ w, right (d.rightAction (g ^ 2) w) = turn (turn (right w))
  pairing_eq : ∀ v w, d.pairing v w = pairing (left v) (right w)

end Theory.GroupAction.FiveFourBinaryModel
