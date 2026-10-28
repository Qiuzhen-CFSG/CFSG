module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The coordinate group of order 11³

The normal form `x^i y^j z^k`, with `z = x⁻¹ y⁻¹ x y`, has multiplication
`(i,j,k)(r,s,t) = (i+r,j+s,k+t-j*r)`. We construct this group over `ZMod 11`,
prove its order and exponent, and give four endomorphisms to be matched with
conjugation in the binary J₄ model. The first two come from the proposed
normalizer words in ATLAS J4G1-max7W1; the last two are inner conjugations.
This module makes no assertion that the concrete matrices satisfy these laws.
-/

@[expose] public section

namespace Janko4.Simplicity.Elevens.LocalCoordinates
@[ext] structure Coord where
  i : ZMod 11
  j : ZMod 11
  k : ZMod 11
  deriving DecidableEq

def tripleEquiv : (ZMod 11 × ZMod 11 × ZMod 11) ≃ Coord where
  toFun a := ⟨a.1, a.2.1, a.2.2⟩
  invFun a := (a.i, a.j, a.k)
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Coord := Fintype.ofEquiv _ tripleEquiv

def cmul (a b : Coord) : Coord := ⟨a.i+b.i, a.j+b.j, a.k+b.k-a.j*b.i⟩
def cinv (a : Coord) : Coord := ⟨-a.i, -a.j, -a.k-a.j*a.i⟩
def cone : Coord := ⟨0, 0, 0⟩
def cpow : ℕ → Coord → Coord
  | 0, _ => cone
  | n+1, a => cmul (cpow n a) a

instance : Group Coord where
  mul := cmul
  one := cone
  inv := cinv
  npow := cpow
  npow_zero _ := rfl
  npow_succ _ _ := rfl
  mul_assoc a b c := by
    change cmul (cmul a b) c = cmul a (cmul b c)
    apply Coord.ext <;> simp [cmul] <;> ring
  one_mul a := by
    change cmul cone a = a
    apply Coord.ext <;> simp [cmul, cone]
  mul_one a := by
    change cmul a cone = a
    apply Coord.ext <;> simp [cmul, cone]
  inv_mul_cancel a := by
    change cmul (cinv a) a = cone
    apply Coord.ext <;> simp [cmul, cinv, cone]; ring

theorem card_coord : Nat.card Coord = 1331 := by
  rw [Nat.card_eq_fintype_card, ← Fintype.card_congr tripleEquiv]
  simp

def X : Coord := ⟨1,0,0⟩
def Y : Coord := ⟨0,1,0⟩
def Z : Coord := ⟨0,0,1⟩

theorem pow_eleven (a : Coord) : a ^ 11 = 1 := by
  change cpow 11 a = cone
  have h11 : (11 : ZMod 11) = 0 := rfl
  have h55 : (55 : ZMod 11) = 0 := rfl
  apply Coord.ext <;> simp [cpow, cmul, cone] <;> ring_nf <;> simp [h11, h55]

def actU (a : Coord) : Coord :=
  ⟨7*a.j, 3*a.i+10*a.j, a.i+4*a.j-2*a.j^2+a.i*a.j+a.k⟩
def actV (a : Coord) : Coord :=
  ⟨5*a.j, a.i+a.j, a.j+3*a.j^2-5*a.i*a.j+6*a.k⟩

theorem actU_mul (a b : Coord) : actU (a*b) = actU a * actU b := by
  change actU (cmul a b) = cmul (actU a) (actU b)
  have h21 : (21 : ZMod 11) = -1 := by decide
  have h70 : (70 : ZMod 11) = 4 := rfl
  apply Coord.ext <;> simp [actU, cmul] <;> ring_nf
  simp only [h21, h70]
  ring

theorem actV_mul (a b : Coord) : actV (a*b) = actV a * actV b := by
  change actV (cmul a b) = cmul (actV a) (actV b)
  have h11 : (11 : ZMod 11) = 0 := rfl
  have h6 : (6 : ZMod 11) = -5 := by decide
  apply Coord.ext <;> simp [actV, cmul] <;> ring_nf
  simp only [h11, h6]
  ring


theorem X_pow (n : ℕ) : X ^ n = ⟨n, 0, 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    change cmul ⟨n, 0, 0⟩ X = _
    simp [cmul, X, Nat.cast_add, Nat.cast_one]

theorem Y_pow (n : ℕ) : Y ^ n = ⟨0, n, 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    change cmul ⟨0, n, 0⟩ Y = _
    simp [cmul, Y, Nat.cast_add, Nat.cast_one]

theorem Z_pow (n : ℕ) : Z ^ n = ⟨0, 0, n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    change cmul ⟨0, 0, n⟩ Z = _
    simp [cmul, Z, Nat.cast_add, Nat.cast_one]

theorem normal_form (c : Coord) : X ^ c.i.val * Y ^ c.j.val * Z ^ c.k.val = c := by
  rw [X_pow, Y_pow, Z_pow]
  change cmul (cmul _ _) _ = c
  apply Coord.ext <;> simp [cmul]

def actUHom : Coord →* Coord where
  toFun := actU
  map_one' := by decide
  map_mul' := actU_mul

def actVHom : Coord →* Coord where
  toFun := actV
  map_one' := by decide
  map_mul' := actV_mul

def actX (a : Coord) : Coord := ⟨a.i, a.j, a.k-a.j⟩
def actY (a : Coord) : Coord := ⟨a.i, a.j, a.k+a.i⟩

theorem actX_eq (a : Coord) : actX a = X⁻¹ * a * X := by
  change actX a = cmul (cmul (cinv X) a) X
  apply Coord.ext <;> simp [actX, cmul, cinv, X]

theorem actY_eq (a : Coord) : actY a = Y⁻¹ * a * Y := by
  change actY a = cmul (cmul (cinv Y) a) Y
  apply Coord.ext <;> simp [actY, cmul, cinv, Y]

def actXHom : Coord →* Coord where
  toFun := actX
  map_one' := by decide
  map_mul' a b := by
    change actX (cmul a b) = cmul (actX a) (actX b)
    apply Coord.ext <;> simp [actX, cmul]; ring

def actYHom : Coord →* Coord where
  toFun := actY
  map_one' := by decide
  map_mul' a b := by
    change actY (cmul a b) = cmul (actY a) (actY b)
    apply Coord.ext <;> simp [actY, cmul]; ring

def action (s : Fin 4) : Coord →* Coord :=
  ![actUHom, actVHom, actXHom, actYHom] s

def wordHom : List (Fin 4) → (Coord →* Coord)
  | [] => MonoidHom.id _
  | s :: ss => (wordHom ss).comp (action s)

def representative (j : Fin 2) : Coord := ![Z, X] j


theorem hom_ext {G : Type*} [Monoid G] (f g : Coord →* G)
    (hX : f X = g X) (hY : f Y = g Y) (hZ : f Z = g Z) : f = g := by
  ext c
  rw [← normal_form c]
  simp only [map_mul, map_pow, hX, hY, hZ]

theorem actU_X : actUHom X = Y ^ 3 * Z := by decide
theorem actU_Y : actUHom Y = X ^ 7 * Y ^ 10 * Z ^ 2 := by decide
theorem actU_Z : actUHom Z = Z := by decide
theorem actV_X : actVHom X = Y := by decide
theorem actV_Y : actVHom Y = X ^ 5 * Y * Z ^ 4 := by decide
theorem actV_Z : actVHom Z = Z ^ 6 := by decide

end Janko4.Simplicity.Elevens.LocalCoordinates
