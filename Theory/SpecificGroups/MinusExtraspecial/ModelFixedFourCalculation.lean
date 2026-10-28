module

public import Theory.SpecificGroups.MinusExtraspecial.Model
public import Mathlib.Data.BitVec

/-!
# Finite certificate for square actions on the minus extraspecial model

Five bits encode the quaternion coordinate (the low three bits) and the two
reflection coordinates. The central involution is bit 1. We enumerate generator
images satisfying the model's relations, and conjugating elements with central
bit zero. For every outer involution obtained from an inner twist of a square,
the certificate checks that the fixed elements have exponent two, that there
are exactly four of them, and that an inner twist of the original automorphism
squares to the prescribed involution.

The enumeration covers every first generator image. Its proof uses kernel
reduction only. `ModelFixedFour` transports this finite certificate to groups;
these exposed definitions form its computational interface.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed pp.389–390,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

@[expose] public section

namespace MinusExtraspecial.FixedFourCalculation
abbrev B := BitVec 5
instance : Fintype B := Fintype.ofEquiv (Fin 32) (BitVec.equivFin (m := 5)).toEquiv.symm
def mul (a b : B) : B :=
  let low := a ^^^ b
  let carry := ((a &&& b) <<< 1) &&& 2
  let neg := ((b >>> 2) &&& a) <<< 1 &&& 2
  let quat := ((a &&& b) >>> 1) &&& 2
  let twist := ((a >>> 3) &&& (b >>> 2)) &&& 2
  low ^^^ carry ^^^ neg ^^^ quat ^^^ twist
def inv (a : B) : B := a ^^^ mul a a
def word (u v r s x : B) : B :=
  mul (mul (mul (mul (if x[2] then v else 0)
    (if x[1] then mul u u else 0)) (if x[0] then u else 0))
    (if x[3] then r else 0)) (if x[4] then s else 0)
def conj (p x : B) : B :=
  if (p[0] && x[2]) ^^ (p[2] && x[0]) ^^ (p[4] && x[3]) ^^ (p[3] && x[4])
  then x ^^^ 2 else x
def act (u v r s p x : B) : B := conj p (word u v r s (word u v r s x))
def gens : List B := [1,4,8,16]
def all : List B := List.range 32 |>.map (BitVec.ofNat 5)
def relations (u v r s : B) : Bool :=
  mul u u != 0 && mul v v == mul u u && mul v u == mul (inv u) v &&
  mul r r == 0 && mul r u == mul u r && mul r v == mul v r &&
  mul s s == 0 && mul s u == mul u s && mul s v == mul v s &&
  mul s r == mul (mul (mul u u) r) s
def invol (u v r s p : B) : Bool :=
  gens.all fun g => act u v r s p (act u v r s p g) == g
def outer (u v r s p : B) : Bool :=
  gens.any fun g => (act u v r s p g ^^^ g) &&& 29 != 0
def count (u v r s p : B) : BitVec 6 :=
  (all.map fun x => if act u v r s p x == x then (1 : BitVec 6) else 0).sum
def root (u v r s p : B) : Bool :=
  all.any fun x => gens.all fun g =>
    conj x (word u v r s (conj x (word u v r s g))) == act u v r s p g


def calculation (u : B) : Prop :=
  mul u u ≠ 0 → ∀ v : B,
  mul v v = mul u u → mul v u = mul (inv u) v → ∀ r : B,
  mul r r = 0 → mul r u = mul u r → mul r v = mul v r → ∀ s : B,
  mul s s = 0 → mul s u = mul u s → mul s v = mul v s →
  mul s r = mul (mul (mul u u) r) s → outer u v r s 0 → ∀ p : B,
  p[1] = false → invol u v r s p →
  (all.all fun y => act u v r s p y != y || mul y y == 0) ∧
  count u v r s p = 4 ∧ root u v r s p
set_option synthInstance.maxSize 1024 in
instance (u : B) : Decidable (calculation u) := by unfold calculation; infer_instance
/- The complete finite certificate, for all four generator images. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calculation_all : ∀ u : B, calculation u := by decide +kernel

end MinusExtraspecial.FixedFourCalculation
