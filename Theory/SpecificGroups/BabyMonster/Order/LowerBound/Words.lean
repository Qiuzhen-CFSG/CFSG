module

public import Theory.SpecificGroups.BabyMonster.Order.Bounds

/-!
# The eleven explicit Baby Monster words

This is the straight-line program of Breuer–Magaard–Wilson,
*Verification of the ordinary character table of the Baby Monster*,
J. Algebra 534 (2019), §3.3, Table 1, https://arxiv.org/abs/1902.07758.
The program is interpreted in an arbitrary group, so the matrix calculations
and the cardinality certificate can use exactly the same words.

Source indices are shifted down by one. Conjugation and commutators follow
the source's conventions, made explicit below. In particular, the commutator
convention is the inverse-first convention. The word for `f` is transcribed
from Table 1, with its factor `e*c*e^2*c`. We make no assumption that these
words satisfy the presentation in an arbitrary group.
-/

@[expose] public section

namespace BabyMonster.OrderLowerBound

variable {G : Type*} [Group G]

/-- The source's right conjugation convention. -/
def wordConjugate (x y : G) : G := y⁻¹ * x * y

/-- The source's inverse-first commutator convention. -/
def wordCommutator (x y : G) : G := x⁻¹ * y⁻¹ * x * y

/-- Table 1, with the source generator `t_(i+1)` at index `i`. -/
def generatorWords (a b : G) : Generator → G :=
  let d := (a * b) ^ 15 * b
  let t11 := d ^ 19
  let c := (a * t11) ^ 3
  let e := wordConjugate ((c * d ^ 3) ^ 10) d
  let f := wordConjugate ((((e * c) ^ 6 * c * (e * c) ^ 3) ^ 2 *
    e * c * e ^ 2 * c) ^ 5) ((e * c) ^ 4)
  let g := wordConjugate ((e * c) ^ 8 * c * (e * c) ^ 3) ((e * c * e ^ 2 * c) ^ 2)
  let arm := fun n : ℕ => wordConjugate f (g * f * g ^ n)
  let t1 := f
  let t2 := arm 0
  let t3 := arm 1
  let t4 := arm 2
  let t5 := arm 3
  let t6 := arm 4
  let t7 := arm 5
  let t8 := arm 6
  let p := ((a * b) ^ 5 * t11 * ((a * b) ^ 5)⁻¹ * t1 * (a * b) ^ 5)⁻¹
  let i := wordConjugate d p
  let j := wordCommutator (wordConjugate t5 (i ^ 2)) (t3 * t4)
  let k := wordCommutator (wordConjugate t5 (i ^ 5)) (t3 * t4)
  let l := wordCommutator (wordConjugate t8 (j * k)) (t6 * t7) *
    wordCommutator (wordConjugate t8 (k * j)) (t6 * t7)
  let l3 := wordCommutator (wordConjugate t8 ((j * k) ^ 4)) (t6 * t7)
  let l4 := wordConjugate t8 ((j * k) ^ 3 * k * j)
  let l5 := (l * l3 * l4) ^ 3 * l3 * l4
  let m2 := wordConjugate l4 (l5 ^ 4)
  let m3 := wordConjugate m2 l5
  let t10 := m3 * m2 * l4 * m2 * m3
  let t9 := l4 * m2 * t10 * m2 * l4
  fun n => match n.val with
    | 0 => t1
    | 1 => t2
    | 2 => t3
    | 3 => t4
    | 4 => t5
    | 5 => t6
    | 6 => t7
    | 7 => t8
    | 8 => t9
    | 9 => t10
    | _ => t11

end BabyMonster.OrderLowerBound
