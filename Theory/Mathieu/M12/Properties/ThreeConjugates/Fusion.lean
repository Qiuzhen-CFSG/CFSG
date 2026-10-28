module
public import Theory.Mathieu.M12.Properties.ThreeConjugates.Transport
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.Overlap

/-!
# Exhaustion of involutions in the concrete M₁₂-extension Sylow subgroup

The existing central-product and swap coordinates cover the actual common
Sylow subgroup of order 128. A finite table conjugates every nonidentity
square-one coordinate to one of the three certified generating representatives.
Lookup permutations speed up reduction; their equality with the original
ATLAS permutations is separately kernel-checked. No computed class size or
order is used. The reproducible untrusted search is in `source/generate.py`.

This supplies the finite input for the three-conjugate degree-window argument
used in Aschbacher–Smith Chapter K, printed pp.451 and 457. The Sylow marking
is the existing one from the outer parabolic model, not an abstract substitute.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ThreeConjugates
open M12ExceptionalExtension SecondCoordinates QuaternionSwapModel
set_option maxRecDepth 4096

/-- Redundant coordinates avoid choosing representatives of the central quotient. -/
abbrev Coordinates := QuaternionGroup 2 × QuaternionGroup 2 × Bool × Bool

def coordinateValue (c : Coordinates) : Carrier :=
  leftMap c.1 * rightMap c.2.1 * (if c.2.2.1 then SecondCoordinates.swap else 1) *
    (if c.2.2.2 then extra else 1)

theorem coordinates_cover (x : overlap) : ∃ c : Coordinates, coordinateValue c = x := by
  obtain ⟨⟨q,b⟩, hq⟩ := overlapElement_surjective innerModel x
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter q
  refine ⟨(w.left 1, w.left turn, decide (w.right ≠ 1), b), ?_⟩
  have hx := congrArg Subtype.val hq
  change rawValue w * (if b then extra else 1) = (x : Carrier) at hx
  rw [← hx]
  simp only [coordinateValue, rawValue, decide_eq_true_eq]
  split_ifs <;> simp_all

def quaternionIndex : QuaternionGroup 2 → Nat
  | .a n => n.val
  | .xa n => n.val + 4

def coordinateIndex (c : Coordinates) : Nat :=
  quaternionIndex c.1 + 8 * quaternionIndex c.2.1 +
    (if c.2.2.1 then 64 else 0) + (if c.2.2.2 then 128 else 0)

def fusionTable : Array (Fin 3 × List (Fin 3)) := #[
  (0, []),
  (0, []),
  (0, [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (1, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0]),
  (0, []),
  (1, [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]),
  (1, [1, 1, 0, 1, 0, 1]),
  (0, [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]),
  (1, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]),
  (0, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]),
  (0, [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (1, [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]),
  (0, []),
  (1, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0]),
  (1, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]),
  (0, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]),
  (1, [1, 1, 0, 1, 0, 1]),
  (0, [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]),
  (0, []),
  (1, [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]),
  (0, []),
  (1, [1, 1, 0, 1, 0, 1, 0, 1, 0]),
  (0, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1]),
  (1, [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]),
  (0, [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]),
  (1, [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1]),
  (0, []),
  (0, [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]),
  (0, []),
  (0, [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0]),
  (1, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]),
  (1, [1, 1, 0, 1, 1, 0, 1]),
  (1, [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]),
  (1, [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]),
  (0, []),
  (1, [1, 1, 0, 1, 0, 1, 0, 1, 0]),
  (0, []),
  (1, [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]),
  (0, [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]),
  (1, [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1]),
  (0, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1]),
  (1, [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]),
  (0, []),
  (0, [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0]),
  (0, []),
  (0, [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]),
  (1, [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]),
  (1, [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]),
  (1, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]),
  (1, [1, 1, 0, 1, 1, 0, 1]),
  (2, [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]),
  (0, []),
  (2, [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (2, [1, 1, 0, 1, 1, 0, 1]),
  (0, []),
  (2, [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (2, [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]),
  (0, []),
  (2, [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (2, [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]),
  (0, []),
  (2, [1, 1, 0, 1, 1, 0, 1]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (2, [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]),
  (0, []),
  (2, [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (2, [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1]),
  (0, []),
  (2, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (2, [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]),
  (0, []),
  (2, [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (2, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0]),
  (0, []),
  (2, [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1]),
  (0, [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]),
  (0, []),
  (0, [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]),
  (0, []),
  (0, [1, 0, 1, 0, 1, 1]),
  (0, []),
  (0, [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]),
  (0, []),
  (0, [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]),
  (0, []),
  (0, [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]),
  (0, []),
  (0, [1, 0, 1, 0, 1, 1]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1]),
  (0, []),
  (0, [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]),
  (0, []),
  (0, [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]),
  (0, []),
  (0, [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]),
  (0, []),
  (0, [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1]),
  (0, []),
  (0, [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]),
  (0, []),
  (0, [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, []),
  (0, [])]

def fusionRepresentative (c : Coordinates) : Fin 3 := (fusionTable[coordinateIndex c]!).1
def fusionConjugator (c : Coordinates) : Carrier :=
  word outerGenerators (fusionTable[coordinateIndex c]!).2


private def fastA : Equiv.Perm (Fin 24) where
  toFun := ![22, 4, 17, 15, 1, 18, 19, 12, 10, 21, 8, 13, 7, 11, 16, 3, 14, 2, 5, 6, 23, 9, 0, 20]
  invFun := ![22, 4, 17, 15, 1, 18, 19, 12, 10, 21, 8, 13, 7, 11, 16, 3, 14, 2, 5, 6, 23, 9, 0, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def fastB : Equiv.Perm (Fin 24) where
  toFun := ![20, 1, 18, 19, 11, 10, 6, 22, 8, 9, 16, 21, 12, 7, 3, 15, 5, 0, 23, 14, 17, 4, 13, 2]
  invFun := ![17, 1, 23, 14, 21, 16, 6, 13, 8, 9, 5, 4, 12, 22, 19, 15, 10, 20, 2, 3, 0, 11, 7, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def fastLI : Equiv.Perm (Fin 24) where
  toFun := ![16, 13, 7, 3, 21, 10, 15, 23, 8, 9, 17, 6, 11, 14, 18, 12, 0, 20, 1, 19, 5, 4, 2, 22]
  invFun := ![16, 18, 22, 3, 21, 20, 11, 2, 8, 9, 5, 12, 15, 1, 13, 6, 0, 10, 14, 19, 17, 4, 23, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def fastLJ : Equiv.Perm (Fin 24) where
  toFun := ![4, 2, 14, 3, 0, 11, 10, 13, 8, 9, 12, 17, 20, 22, 23, 5, 21, 15, 7, 19, 6, 16, 18, 1]
  invFun := ![4, 23, 1, 3, 0, 15, 20, 18, 8, 9, 6, 5, 10, 7, 2, 17, 21, 11, 22, 19, 12, 16, 13, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def fastRI : Equiv.Perm (Fin 24) where
  toFun := ![0, 7, 13, 8, 4, 6, 17, 14, 3, 19, 15, 10, 5, 23, 22, 20, 16, 12, 2, 9, 11, 21, 1, 18]
  invFun := ![0, 22, 18, 8, 4, 12, 5, 1, 3, 19, 11, 20, 17, 2, 7, 10, 16, 6, 23, 9, 15, 21, 14, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def fastRJ : Equiv.Perm (Fin 24) where
  toFun := ![0, 2, 14, 9, 4, 15, 10, 18, 19, 3, 12, 5, 20, 7, 23, 17, 16, 11, 22, 8, 6, 21, 13, 1]
  invFun := ![0, 23, 1, 9, 4, 11, 20, 13, 19, 3, 6, 17, 10, 22, 2, 5, 16, 15, 7, 8, 12, 21, 18, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def fastSwap : Equiv.Perm (Fin 24) where
  toFun := ![9, 6, 10, 4, 3, 18, 1, 15, 21, 0, 2, 22, 14, 17, 12, 7, 19, 13, 5, 16, 23, 8, 11, 20]
  invFun := ![9, 6, 10, 4, 3, 18, 1, 15, 21, 0, 2, 22, 14, 17, 12, 7, 19, 13, 5, 16, 23, 8, 11, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def fastExtra : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 23, 3, 4, 11, 12, 18, 19, 9, 10, 5, 6, 22, 14, 17, 21, 15, 7, 8, 20, 16, 13, 2]
  invFun := ![0, 1, 23, 3, 4, 11, 12, 18, 19, 9, 10, 5, 6, 22, 14, 17, 21, 15, 7, 8, 20, 16, 13, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def fastOuterGenerators : Fin 3 → Equiv.Perm (Fin 24) :=
  ![fastA, fastB, fastB⁻¹]

private theorem outerGenerators_coe : ∀ i : Fin 3,
    (outerGenerators i : Equiv.Perm (Fin 24)) = fastOuterGenerators i := by
  decide +kernel

private theorem outer_word_coe (w : List (Fin 3)) :
    ((word outerGenerators w : Carrier) : Equiv.Perm (Fin 24)) =
      word fastOuterGenerators w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (outerGenerators i : Equiv.Perm (Fin 24)) *
      ((word outerGenerators w : Carrier) : Equiv.Perm (Fin 24)) =
        fastOuterGenerators i * word fastOuterGenerators w
    rw [outerGenerators_coe, ih]

private def fastQuaternion (i j : Equiv.Perm (Fin 24)) : QuaternionGroup 2 →
    Equiv.Perm (Fin 24)
  | .a n => i ^ n.val
  | .xa n => j * i ^ n.val

private theorem fastLI_eq : fastLI = leftIPerm := by decide +kernel
private theorem fastLJ_eq : fastLJ = leftJPerm := by decide +kernel
private theorem fastRI_eq : fastRI = rightIPerm := by decide +kernel
private theorem fastRJ_eq : fastRJ = rightJPerm := by decide +kernel
private theorem fastSwap_eq : fastSwap = swapPerm := by decide +kernel
private theorem fastExtra_eq : fastExtra = extraPerm := by decide +kernel

private theorem leftMap_coe (q : QuaternionGroup 2) :
    (leftMap q : Equiv.Perm (Fin 24)) = fastQuaternion fastLI fastLJ q := by
  cases q with
  | a n =>
    change leftIPerm ^ n.val = fastLI ^ n.val
    rw [fastLI_eq]
  | xa n =>
    change leftJPerm * leftIPerm ^ n.val = fastLJ * fastLI ^ n.val
    rw [fastLI_eq, fastLJ_eq]

private theorem rightMap_coe (q : QuaternionGroup 2) :
    (rightMap q : Equiv.Perm (Fin 24)) = fastQuaternion fastRI fastRJ q := by
  cases q with
  | a n =>
    change rightIPerm ^ n.val = fastRI ^ n.val
    rw [fastRI_eq]
  | xa n =>
    change rightJPerm * rightIPerm ^ n.val = fastRJ * fastRI ^ n.val
    rw [fastRI_eq, fastRJ_eq]

private def coordinatePerm (c : Coordinates) : Equiv.Perm (Fin 24) :=
  fastQuaternion fastLI fastLJ c.1 * fastQuaternion fastRI fastRJ c.2.1 *
    (if c.2.2.1 then fastSwap else 1) * (if c.2.2.2 then fastExtra else 1)

private theorem coordinateValue_coe (c : Coordinates) :
    (coordinateValue c : Equiv.Perm (Fin 24)) = coordinatePerm c := by
  rcases c with ⟨q, r, b, d⟩
  cases b <;> cases d <;>
    change (leftMap q : Equiv.Perm (Fin 24)) *
      (rightMap r : Equiv.Perm (Fin 24)) * _ * _ =
        fastQuaternion fastLI fastLJ q * fastQuaternion fastRI fastRJ r * _ * _
  all_goals rw [leftMap_coe, rightMap_coe]
  all_goals simp only [fastSwap_eq, fastExtra_eq]
  all_goals rfl

private def fastFusionConjugator (c : Coordinates) : Equiv.Perm (Fin 24) :=
  word fastOuterGenerators (fusionTable[coordinateIndex c]!).2

private theorem finite_fusion_check : ∀ c : Coordinates,
    coordinatePerm c ^ 2 = 1 → coordinatePerm c ≠ 1 →
      fastFusionConjugator c * representativePerm (fusionRepresentative c) *
        (fastFusionConjugator c)⁻¹ = coordinatePerm c := by
  decide +kernel

/-- Every nonidentity square-one coordinate is conjugate to its certified
representative, with a literal word in the extension generators. -/
theorem fusion_check (c : Coordinates)
    (hc2 : coordinateValue c ^ 2 = 1) (hc : coordinateValue c ≠ 1) :
    fusionConjugator c * representative (fusionRepresentative c) *
      (fusionConjugator c)⁻¹ = coordinateValue c := by
  have hc2' : coordinatePerm c ^ 2 = 1 := by
    rw [← coordinateValue_coe]
    exact congrArg (fun x : Carrier => (x : Equiv.Perm (Fin 24))) hc2
  have hc' : coordinatePerm c ≠ 1 := by
    intro h
    apply hc
    apply Subtype.ext
    exact (coordinateValue_coe c).trans h
  apply Subtype.ext
  change ((word outerGenerators (fusionTable[coordinateIndex c]!).2 : Carrier) :
      Equiv.Perm (Fin 24)) * representativePerm (fusionRepresentative c) *
    ((word outerGenerators (fusionTable[coordinateIndex c]!).2 : Carrier) :
      Equiv.Perm (Fin 24))⁻¹ = (coordinateValue c : Equiv.Perm (Fin 24))
  rw [outer_word_coe, coordinateValue_coe]
  exact finite_fusion_check c hc2' hc'

/-- All involutions in the existing order-128 Sylow model satisfy the literal
three-conjugate containment with inner conjugators. -/
theorem sylow_generates (x : overlap) (hx : (x : Carrier) ≠ 1)
    (hx2 : (x : Carrier) ^ 2 = 1) : Generates (x : Carrier) := by
  obtain ⟨c, hc⟩ := coordinates_cover x
  have hc2 : coordinateValue c ^ 2 = 1 := hc ▸ hx2
  have hc1 : coordinateValue c ≠ 1 := hc ▸ hx
  rw [← hc, ← fusion_check c hc2 hc1]
  exact generates_conjugate (representative_generates _) _

end Sporadic.Mathieu.M12ThreeConjugates
