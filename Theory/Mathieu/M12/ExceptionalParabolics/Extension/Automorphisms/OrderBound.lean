module

public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Seeds
public import Theory.GroupTheory.WordSubgroup

/-!
# Order bound for the fixed degree-24 M₁₂ extension

A kernel-checked Schreier chain for the literal ATLAS generator pair has base
`[4, 6, 0, 15, 11]`, successive indices `24, 11, 10, 9, 8`, and trivial final
subgroup. Each representative and next-level generator is certified by a word;
every generator/representative product is reduced by a checked Schreier factor.
The generic word-subgroup cardinality theorem then gives the order bound.

GAP supplied candidate generators only. All permutation tables, word identities,
point separation, and termination are checked by Lean's kernel. Multiplication
uses Lean's composition convention; ATLAS point 24 is Fin24 point 0.

Sources: ATLAS M12d2G1-p24B0,
https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/M12d2G1-p24B0;
Aschbacher–Smith F.1.12(I)(13), printed p.263, supplies the intended outer-model
application. This module proves the intrinsic numerical prerequisite only.
-/

namespace Sporadic.Mathieu.M12ExceptionalExtension
namespace OrderBoundCertificate
open Theory.GroupTheory
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def l0g0To : Fin 24 → Fin 24
  | 0 => 22
  | 1 => 4
  | 2 => 17
  | 3 => 15
  | 4 => 1
  | 5 => 18
  | 6 => 19
  | 7 => 12
  | 8 => 10
  | 9 => 21
  | 10 => 8
  | 11 => 13
  | 12 => 7
  | 13 => 11
  | 14 => 16
  | 15 => 3
  | 16 => 14
  | 17 => 2
  | 18 => 5
  | 19 => 6
  | 20 => 23
  | 21 => 9
  | 22 => 0
  | 23 => 20
  | _ => 22

def l0g0Inv : Fin 24 → Fin 24
  | 0 => 22
  | 1 => 4
  | 2 => 17
  | 3 => 15
  | 4 => 1
  | 5 => 18
  | 6 => 19
  | 7 => 12
  | 8 => 10
  | 9 => 21
  | 10 => 8
  | 11 => 13
  | 12 => 7
  | 13 => 11
  | 14 => 16
  | 15 => 3
  | 16 => 14
  | 17 => 2
  | 18 => 5
  | 19 => 6
  | 20 => 23
  | 21 => 9
  | 22 => 0
  | 23 => 20
  | _ => 22

theorem l0g0_left : ∀ x, l0g0Inv (l0g0To x) = x := by decide +kernel
def l0g0 : Equiv.Perm (Fin 24) :=
  tablePerm l0g0To l0g0Inv l0g0_left
    (rightInverse_of_leftInverse_fin l0g0_left)

def l0g1To : Fin 24 → Fin 24
  | 0 => 20
  | 1 => 1
  | 2 => 18
  | 3 => 19
  | 4 => 11
  | 5 => 10
  | 6 => 6
  | 7 => 22
  | 8 => 8
  | 9 => 9
  | 10 => 16
  | 11 => 21
  | 12 => 12
  | 13 => 7
  | 14 => 3
  | 15 => 15
  | 16 => 5
  | 17 => 0
  | 18 => 23
  | 19 => 14
  | 20 => 17
  | 21 => 4
  | 22 => 13
  | 23 => 2
  | _ => 20

def l0g1Inv : Fin 24 → Fin 24
  | 0 => 17
  | 1 => 1
  | 2 => 23
  | 3 => 14
  | 4 => 21
  | 5 => 16
  | 6 => 6
  | 7 => 13
  | 8 => 8
  | 9 => 9
  | 10 => 5
  | 11 => 4
  | 12 => 12
  | 13 => 22
  | 14 => 19
  | 15 => 15
  | 16 => 10
  | 17 => 20
  | 18 => 2
  | 19 => 3
  | 20 => 0
  | 21 => 11
  | 22 => 7
  | 23 => 18
  | _ => 17

theorem l0g1_left : ∀ x, l0g1Inv (l0g1To x) = x := by decide +kernel
def l0g1 : Equiv.Perm (Fin 24) :=
  tablePerm l0g1To l0g1Inv l0g1_left
    (rightInverse_of_leftInverse_fin l0g1_left)

def gen0 : Fin 4 → Equiv.Perm (Fin 24)
  | 0 => l0g0
  | 1 => l0g1
  | 2 => (l0g0)⁻¹
  | 3 => (l0g1)⁻¹
  | _ => l0g0

def inv0 : Fin 4 → Fin 4
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | _ => 2

theorem inv0_spec : ∀ i, gen0 (inv0 i) = (gen0 i)⁻¹ := by decide +kernel

def l1g0To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 14
  | 2 => 23
  | 3 => 7
  | 4 => 4
  | 5 => 20
  | 6 => 10
  | 7 => 22
  | 8 => 1
  | 9 => 9
  | 10 => 17
  | 11 => 16
  | 12 => 5
  | 13 => 13
  | 14 => 8
  | 15 => 11
  | 16 => 15
  | 17 => 6
  | 18 => 18
  | 19 => 2
  | 20 => 12
  | 21 => 21
  | 22 => 3
  | 23 => 19
  | _ => 0

def l1g0Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 8
  | 2 => 19
  | 3 => 22
  | 4 => 4
  | 5 => 12
  | 6 => 17
  | 7 => 3
  | 8 => 14
  | 9 => 9
  | 10 => 6
  | 11 => 15
  | 12 => 20
  | 13 => 13
  | 14 => 1
  | 15 => 16
  | 16 => 11
  | 17 => 10
  | 18 => 18
  | 19 => 23
  | 20 => 5
  | 21 => 21
  | 22 => 7
  | 23 => 2
  | _ => 0

theorem l1g0_left : ∀ x, l1g0Inv (l1g0To x) = x := by decide +kernel
def l1g0 : Equiv.Perm (Fin 24) :=
  tablePerm l1g0To l1g0Inv l1g0_left
    (rightInverse_of_leftInverse_fin l1g0_left)

def l1g1To : Fin 24 → Fin 24
  | 0 => 10
  | 1 => 1
  | 2 => 9
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 8
  | 8 => 13
  | 9 => 19
  | 10 => 16
  | 11 => 20
  | 12 => 11
  | 13 => 7
  | 14 => 23
  | 15 => 17
  | 16 => 0
  | 17 => 21
  | 18 => 18
  | 19 => 2
  | 20 => 12
  | 21 => 15
  | 22 => 14
  | 23 => 22
  | _ => 10

def l1g1Inv : Fin 24 → Fin 24
  | 0 => 16
  | 1 => 1
  | 2 => 19
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 13
  | 8 => 7
  | 9 => 2
  | 10 => 0
  | 11 => 12
  | 12 => 20
  | 13 => 8
  | 14 => 22
  | 15 => 21
  | 16 => 10
  | 17 => 15
  | 18 => 18
  | 19 => 9
  | 20 => 11
  | 21 => 17
  | 22 => 23
  | 23 => 14
  | _ => 16

theorem l1g1_left : ∀ x, l1g1Inv (l1g1To x) = x := by decide +kernel
def l1g1 : Equiv.Perm (Fin 24) :=
  tablePerm l1g1To l1g1Inv l1g1_left
    (rightInverse_of_leftInverse_fin l1g1_left)

def l1g2To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 13
  | 3 => 23
  | 4 => 4
  | 5 => 17
  | 6 => 6
  | 7 => 2
  | 8 => 7
  | 9 => 19
  | 10 => 20
  | 11 => 21
  | 12 => 16
  | 13 => 8
  | 14 => 18
  | 15 => 15
  | 16 => 5
  | 17 => 12
  | 18 => 14
  | 19 => 9
  | 20 => 11
  | 21 => 10
  | 22 => 1
  | 23 => 22
  | _ => 0

def l1g2Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 22
  | 2 => 7
  | 3 => 1
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 8
  | 8 => 13
  | 9 => 19
  | 10 => 21
  | 11 => 20
  | 12 => 17
  | 13 => 2
  | 14 => 18
  | 15 => 15
  | 16 => 12
  | 17 => 5
  | 18 => 14
  | 19 => 9
  | 20 => 10
  | 21 => 11
  | 22 => 23
  | 23 => 3
  | _ => 0

theorem l1g2_left : ∀ x, l1g2Inv (l1g2To x) = x := by decide +kernel
def l1g2 : Equiv.Perm (Fin 24) :=
  tablePerm l1g2To l1g2Inv l1g2_left
    (rightInverse_of_leftInverse_fin l1g2_left)

def gen1 : Fin 6 → Equiv.Perm (Fin 24)
  | 0 => l1g0
  | 1 => l1g1
  | 2 => l1g2
  | 3 => (l1g0)⁻¹
  | 4 => (l1g1)⁻¹
  | 5 => (l1g2)⁻¹
  | _ => l1g0

def inv1 : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | _ => 3

theorem inv1_spec : ∀ i, gen1 (inv1 i) = (gen1 i)⁻¹ := by decide +kernel

def gen1Word : Fin 6 → List (Fin 4)
  | 0 => [3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1]
  | 1 => [3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1]
  | 2 => [1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0]
  | 3 => [3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1]
  | 4 => [3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1]
  | 5 => [3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0]
  | _ => [3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1]

theorem gen1_eq_word : ∀ i, gen1 i = evalWord gen0 (gen1Word i) := by decide +kernel

def l2g0To : Fin 24 → Fin 24
  | 0 => 10
  | 1 => 1
  | 2 => 9
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 8
  | 8 => 13
  | 9 => 19
  | 10 => 16
  | 11 => 20
  | 12 => 11
  | 13 => 7
  | 14 => 23
  | 15 => 17
  | 16 => 0
  | 17 => 21
  | 18 => 18
  | 19 => 2
  | 20 => 12
  | 21 => 15
  | 22 => 14
  | 23 => 22
  | _ => 10

def l2g0Inv : Fin 24 → Fin 24
  | 0 => 16
  | 1 => 1
  | 2 => 19
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 13
  | 8 => 7
  | 9 => 2
  | 10 => 0
  | 11 => 12
  | 12 => 20
  | 13 => 8
  | 14 => 22
  | 15 => 21
  | 16 => 10
  | 17 => 15
  | 18 => 18
  | 19 => 9
  | 20 => 11
  | 21 => 17
  | 22 => 23
  | 23 => 14
  | _ => 16

theorem l2g0_left : ∀ x, l2g0Inv (l2g0To x) = x := by decide +kernel
def l2g0 : Equiv.Perm (Fin 24) :=
  tablePerm l2g0To l2g0Inv l2g0_left
    (rightInverse_of_leftInverse_fin l2g0_left)

def l2g1To : Fin 24 → Fin 24
  | 0 => 12
  | 1 => 3
  | 2 => 13
  | 3 => 23
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 9
  | 8 => 7
  | 9 => 8
  | 10 => 20
  | 11 => 11
  | 12 => 17
  | 13 => 19
  | 14 => 14
  | 15 => 5
  | 16 => 15
  | 17 => 0
  | 18 => 18
  | 19 => 2
  | 20 => 21
  | 21 => 10
  | 22 => 22
  | 23 => 1
  | _ => 12

def l2g1Inv : Fin 24 → Fin 24
  | 0 => 17
  | 1 => 23
  | 2 => 19
  | 3 => 1
  | 4 => 4
  | 5 => 15
  | 6 => 6
  | 7 => 8
  | 8 => 9
  | 9 => 7
  | 10 => 21
  | 11 => 11
  | 12 => 0
  | 13 => 2
  | 14 => 14
  | 15 => 16
  | 16 => 5
  | 17 => 12
  | 18 => 18
  | 19 => 13
  | 20 => 10
  | 21 => 20
  | 22 => 22
  | 23 => 3
  | _ => 17

theorem l2g1_left : ∀ x, l2g1Inv (l2g1To x) = x := by decide +kernel
def l2g1 : Equiv.Perm (Fin 24) :=
  tablePerm l2g1To l2g1Inv l2g1_left
    (rightInverse_of_leftInverse_fin l2g1_left)

def l2g2To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 13
  | 3 => 23
  | 4 => 4
  | 5 => 17
  | 6 => 6
  | 7 => 2
  | 8 => 7
  | 9 => 19
  | 10 => 20
  | 11 => 21
  | 12 => 16
  | 13 => 8
  | 14 => 18
  | 15 => 15
  | 16 => 5
  | 17 => 12
  | 18 => 14
  | 19 => 9
  | 20 => 11
  | 21 => 10
  | 22 => 1
  | 23 => 22
  | _ => 0

def l2g2Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 22
  | 2 => 7
  | 3 => 1
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 8
  | 8 => 13
  | 9 => 19
  | 10 => 21
  | 11 => 20
  | 12 => 17
  | 13 => 2
  | 14 => 18
  | 15 => 15
  | 16 => 12
  | 17 => 5
  | 18 => 14
  | 19 => 9
  | 20 => 10
  | 21 => 11
  | 22 => 23
  | 23 => 3
  | _ => 0

theorem l2g2_left : ∀ x, l2g2Inv (l2g2To x) = x := by decide +kernel
def l2g2 : Equiv.Perm (Fin 24) :=
  tablePerm l2g2To l2g2Inv l2g2_left
    (rightInverse_of_leftInverse_fin l2g2_left)

def l2g3To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 13
  | 2 => 22
  | 3 => 2
  | 4 => 4
  | 5 => 11
  | 6 => 6
  | 7 => 1
  | 8 => 3
  | 9 => 14
  | 10 => 5
  | 11 => 12
  | 12 => 10
  | 13 => 23
  | 14 => 9
  | 15 => 15
  | 16 => 21
  | 17 => 20
  | 18 => 19
  | 19 => 18
  | 20 => 16
  | 21 => 17
  | 22 => 8
  | 23 => 7
  | _ => 0

def l2g3Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 7
  | 2 => 3
  | 3 => 8
  | 4 => 4
  | 5 => 10
  | 6 => 6
  | 7 => 23
  | 8 => 22
  | 9 => 14
  | 10 => 12
  | 11 => 5
  | 12 => 11
  | 13 => 1
  | 14 => 9
  | 15 => 15
  | 16 => 20
  | 17 => 21
  | 18 => 19
  | 19 => 18
  | 20 => 17
  | 21 => 16
  | 22 => 2
  | 23 => 13
  | _ => 0

theorem l2g3_left : ∀ x, l2g3Inv (l2g3To x) = x := by decide +kernel
def l2g3 : Equiv.Perm (Fin 24) :=
  tablePerm l2g3To l2g3Inv l2g3_left
    (rightInverse_of_leftInverse_fin l2g3_left)

def gen2 : Fin 8 → Equiv.Perm (Fin 24)
  | 0 => l2g0
  | 1 => l2g1
  | 2 => l2g2
  | 3 => l2g3
  | 4 => (l2g0)⁻¹
  | 5 => (l2g1)⁻¹
  | 6 => (l2g2)⁻¹
  | 7 => (l2g3)⁻¹
  | _ => l2g0

def inv2 : Fin 8 → Fin 8
  | 0 => 4
  | 1 => 5
  | 2 => 6
  | 3 => 7
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | _ => 4

theorem inv2_spec : ∀ i, gen2 (inv2 i) = (gen2 i)⁻¹ := by decide +kernel

def gen2Word : Fin 8 → List (Fin 6)
  | 0 => [1]
  | 1 => [0, 2, 2, 4, 0, 4, 0]
  | 2 => [2]
  | 3 => [4, 3, 1, 5, 4, 0, 1]
  | 4 => [4]
  | 5 => [1, 5, 0, 4, 3, 5, 0]
  | 6 => [5]
  | 7 => [4, 3, 1, 2, 4, 0, 1]
  | _ => [1]

theorem gen2_eq_word : ∀ i, gen2 i = evalWord gen1 (gen2Word i) := by decide +kernel

def l3g0To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 22
  | 4 => 4
  | 5 => 17
  | 6 => 6
  | 7 => 9
  | 8 => 19
  | 9 => 7
  | 10 => 12
  | 11 => 16
  | 12 => 10
  | 13 => 13
  | 14 => 23
  | 15 => 21
  | 16 => 11
  | 17 => 5
  | 18 => 18
  | 19 => 8
  | 20 => 20
  | 21 => 15
  | 22 => 3
  | 23 => 14
  | _ => 0

def l3g0Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 22
  | 4 => 4
  | 5 => 17
  | 6 => 6
  | 7 => 9
  | 8 => 19
  | 9 => 7
  | 10 => 12
  | 11 => 16
  | 12 => 10
  | 13 => 13
  | 14 => 23
  | 15 => 21
  | 16 => 11
  | 17 => 5
  | 18 => 18
  | 19 => 8
  | 20 => 20
  | 21 => 15
  | 22 => 3
  | 23 => 14
  | _ => 0

theorem l3g0_left : ∀ x, l3g0Inv (l3g0To x) = x := by decide +kernel
def l3g0 : Equiv.Perm (Fin 24) :=
  tablePerm l3g0To l3g0Inv l3g0_left
    (rightInverse_of_leftInverse_fin l3g0_left)

def l3g1To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 23
  | 2 => 8
  | 3 => 22
  | 4 => 4
  | 5 => 12
  | 6 => 6
  | 7 => 13
  | 8 => 2
  | 9 => 9
  | 10 => 11
  | 11 => 10
  | 12 => 5
  | 13 => 7
  | 14 => 14
  | 15 => 15
  | 16 => 17
  | 17 => 16
  | 18 => 18
  | 19 => 19
  | 20 => 21
  | 21 => 20
  | 22 => 3
  | 23 => 1
  | _ => 0

def l3g1Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 23
  | 2 => 8
  | 3 => 22
  | 4 => 4
  | 5 => 12
  | 6 => 6
  | 7 => 13
  | 8 => 2
  | 9 => 9
  | 10 => 11
  | 11 => 10
  | 12 => 5
  | 13 => 7
  | 14 => 14
  | 15 => 15
  | 16 => 17
  | 17 => 16
  | 18 => 18
  | 19 => 19
  | 20 => 21
  | 21 => 20
  | 22 => 3
  | 23 => 1
  | _ => 0

theorem l3g1_left : ∀ x, l3g1Inv (l3g1To x) = x := by decide +kernel
def l3g1 : Equiv.Perm (Fin 24) :=
  tablePerm l3g1To l3g1Inv l3g1_left
    (rightInverse_of_leftInverse_fin l3g1_left)

def l3g2To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 13
  | 3 => 23
  | 4 => 4
  | 5 => 17
  | 6 => 6
  | 7 => 2
  | 8 => 7
  | 9 => 19
  | 10 => 20
  | 11 => 21
  | 12 => 16
  | 13 => 8
  | 14 => 18
  | 15 => 15
  | 16 => 5
  | 17 => 12
  | 18 => 14
  | 19 => 9
  | 20 => 11
  | 21 => 10
  | 22 => 1
  | 23 => 22
  | _ => 0

def l3g2Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 22
  | 2 => 7
  | 3 => 1
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 8
  | 8 => 13
  | 9 => 19
  | 10 => 21
  | 11 => 20
  | 12 => 17
  | 13 => 2
  | 14 => 18
  | 15 => 15
  | 16 => 12
  | 17 => 5
  | 18 => 14
  | 19 => 9
  | 20 => 10
  | 21 => 11
  | 22 => 23
  | 23 => 3
  | _ => 0

theorem l3g2_left : ∀ x, l3g2Inv (l3g2To x) = x := by decide +kernel
def l3g2 : Equiv.Perm (Fin 24) :=
  tablePerm l3g2To l3g2Inv l3g2_left
    (rightInverse_of_leftInverse_fin l3g2_left)

def l3g3To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 13
  | 2 => 22
  | 3 => 2
  | 4 => 4
  | 5 => 11
  | 6 => 6
  | 7 => 1
  | 8 => 3
  | 9 => 14
  | 10 => 5
  | 11 => 12
  | 12 => 10
  | 13 => 23
  | 14 => 9
  | 15 => 15
  | 16 => 21
  | 17 => 20
  | 18 => 19
  | 19 => 18
  | 20 => 16
  | 21 => 17
  | 22 => 8
  | 23 => 7
  | _ => 0

def l3g3Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 7
  | 2 => 3
  | 3 => 8
  | 4 => 4
  | 5 => 10
  | 6 => 6
  | 7 => 23
  | 8 => 22
  | 9 => 14
  | 10 => 12
  | 11 => 5
  | 12 => 11
  | 13 => 1
  | 14 => 9
  | 15 => 15
  | 16 => 20
  | 17 => 21
  | 18 => 19
  | 19 => 18
  | 20 => 17
  | 21 => 16
  | 22 => 2
  | 23 => 13
  | _ => 0

theorem l3g3_left : ∀ x, l3g3Inv (l3g3To x) = x := by decide +kernel
def l3g3 : Equiv.Perm (Fin 24) :=
  tablePerm l3g3To l3g3Inv l3g3_left
    (rightInverse_of_leftInverse_fin l3g3_left)

def gen3 : Fin 8 → Equiv.Perm (Fin 24)
  | 0 => l3g0
  | 1 => l3g1
  | 2 => l3g2
  | 3 => l3g3
  | 4 => (l3g0)⁻¹
  | 5 => (l3g1)⁻¹
  | 6 => (l3g2)⁻¹
  | 7 => (l3g3)⁻¹
  | _ => l3g0

def inv3 : Fin 8 → Fin 8
  | 0 => 4
  | 1 => 5
  | 2 => 6
  | 3 => 7
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | _ => 4

theorem inv3_spec : ∀ i, gen3 (inv3 i) = (gen3 i)⁻¹ := by decide +kernel

def gen3Word : Fin 8 → List (Fin 8)
  | 0 => [5, 0, 1, 0]
  | 1 => [2, 2]
  | 2 => [2]
  | 3 => [3]
  | 4 => [5, 0, 1, 0]
  | 5 => [2, 2]
  | 6 => [6]
  | 7 => [7]
  | _ => [5, 0, 1, 0]

theorem gen3_eq_word : ∀ i, gen3 i = evalWord gen2 (gen3Word i) := by decide +kernel

def l4g0To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 23
  | 2 => 8
  | 3 => 22
  | 4 => 4
  | 5 => 12
  | 6 => 6
  | 7 => 13
  | 8 => 2
  | 9 => 9
  | 10 => 11
  | 11 => 10
  | 12 => 5
  | 13 => 7
  | 14 => 14
  | 15 => 15
  | 16 => 17
  | 17 => 16
  | 18 => 18
  | 19 => 19
  | 20 => 21
  | 21 => 20
  | 22 => 3
  | 23 => 1
  | _ => 0

def l4g0Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 23
  | 2 => 8
  | 3 => 22
  | 4 => 4
  | 5 => 12
  | 6 => 6
  | 7 => 13
  | 8 => 2
  | 9 => 9
  | 10 => 11
  | 11 => 10
  | 12 => 5
  | 13 => 7
  | 14 => 14
  | 15 => 15
  | 16 => 17
  | 17 => 16
  | 18 => 18
  | 19 => 19
  | 20 => 21
  | 21 => 20
  | 22 => 3
  | 23 => 1
  | _ => 0

theorem l4g0_left : ∀ x, l4g0Inv (l4g0To x) = x := by decide +kernel
def l4g0 : Equiv.Perm (Fin 24) :=
  tablePerm l4g0To l4g0Inv l4g0_left
    (rightInverse_of_leftInverse_fin l4g0_left)

def l4g1To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 13
  | 3 => 23
  | 4 => 4
  | 5 => 17
  | 6 => 6
  | 7 => 2
  | 8 => 7
  | 9 => 19
  | 10 => 20
  | 11 => 21
  | 12 => 16
  | 13 => 8
  | 14 => 18
  | 15 => 15
  | 16 => 5
  | 17 => 12
  | 18 => 14
  | 19 => 9
  | 20 => 11
  | 21 => 10
  | 22 => 1
  | 23 => 22
  | _ => 0

def l4g1Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 22
  | 2 => 7
  | 3 => 1
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 8
  | 8 => 13
  | 9 => 19
  | 10 => 21
  | 11 => 20
  | 12 => 17
  | 13 => 2
  | 14 => 18
  | 15 => 15
  | 16 => 12
  | 17 => 5
  | 18 => 14
  | 19 => 9
  | 20 => 10
  | 21 => 11
  | 22 => 23
  | 23 => 3
  | _ => 0

theorem l4g1_left : ∀ x, l4g1Inv (l4g1To x) = x := by decide +kernel
def l4g1 : Equiv.Perm (Fin 24) :=
  tablePerm l4g1To l4g1Inv l4g1_left
    (rightInverse_of_leftInverse_fin l4g1_left)

def l4g2To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 13
  | 2 => 22
  | 3 => 2
  | 4 => 4
  | 5 => 11
  | 6 => 6
  | 7 => 1
  | 8 => 3
  | 9 => 14
  | 10 => 5
  | 11 => 12
  | 12 => 10
  | 13 => 23
  | 14 => 9
  | 15 => 15
  | 16 => 21
  | 17 => 20
  | 18 => 19
  | 19 => 18
  | 20 => 16
  | 21 => 17
  | 22 => 8
  | 23 => 7
  | _ => 0

def l4g2Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 7
  | 2 => 3
  | 3 => 8
  | 4 => 4
  | 5 => 10
  | 6 => 6
  | 7 => 23
  | 8 => 22
  | 9 => 14
  | 10 => 12
  | 11 => 5
  | 12 => 11
  | 13 => 1
  | 14 => 9
  | 15 => 15
  | 16 => 20
  | 17 => 21
  | 18 => 19
  | 19 => 18
  | 20 => 17
  | 21 => 16
  | 22 => 2
  | 23 => 13
  | _ => 0

theorem l4g2_left : ∀ x, l4g2Inv (l4g2To x) = x := by decide +kernel
def l4g2 : Equiv.Perm (Fin 24) :=
  tablePerm l4g2To l4g2Inv l4g2_left
    (rightInverse_of_leftInverse_fin l4g2_left)

def gen4 : Fin 6 → Equiv.Perm (Fin 24)
  | 0 => l4g0
  | 1 => l4g1
  | 2 => l4g2
  | 3 => (l4g0)⁻¹
  | 4 => (l4g1)⁻¹
  | 5 => (l4g2)⁻¹
  | _ => l4g0

def inv4 : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | _ => 3

theorem inv4_spec : ∀ i, gen4 (inv4 i) = (gen4 i)⁻¹ := by decide +kernel

def gen4Word : Fin 6 → List (Fin 8)
  | 0 => [1]
  | 1 => [2]
  | 2 => [3]
  | 3 => [1]
  | 4 => [6]
  | 5 => [7]
  | _ => [1]

theorem gen4_eq_word : ∀ i, gen4 i = evalWord gen3 (gen4Word i) := by decide +kernel

def gen5 : Fin 0 → Equiv.Perm (Fin 24) := fun i => Fin.elim0 i
def inv5 : Fin 0 → Fin 0 := fun i => Fin.elim0 i
theorem inv5_spec : ∀ i, gen5 (inv5 i) = (gen5 i)⁻¹ := fun i => Fin.elim0 i

def l0r0 : Equiv.Perm (Fin 24) := 1

def l0r1To : Fin 24 → Fin 24
  | 0 => 22
  | 1 => 4
  | 2 => 17
  | 3 => 15
  | 4 => 1
  | 5 => 18
  | 6 => 19
  | 7 => 12
  | 8 => 10
  | 9 => 21
  | 10 => 8
  | 11 => 13
  | 12 => 7
  | 13 => 11
  | 14 => 16
  | 15 => 3
  | 16 => 14
  | 17 => 2
  | 18 => 5
  | 19 => 6
  | 20 => 23
  | 21 => 9
  | 22 => 0
  | 23 => 20
  | _ => 22

def l0r1Inv : Fin 24 → Fin 24
  | 0 => 22
  | 1 => 4
  | 2 => 17
  | 3 => 15
  | 4 => 1
  | 5 => 18
  | 6 => 19
  | 7 => 12
  | 8 => 10
  | 9 => 21
  | 10 => 8
  | 11 => 13
  | 12 => 7
  | 13 => 11
  | 14 => 16
  | 15 => 3
  | 16 => 14
  | 17 => 2
  | 18 => 5
  | 19 => 6
  | 20 => 23
  | 21 => 9
  | 22 => 0
  | 23 => 20
  | _ => 22

theorem l0r1_left : ∀ x, l0r1Inv (l0r1To x) = x := by decide +kernel
def l0r1 : Equiv.Perm (Fin 24) :=
  tablePerm l0r1To l0r1Inv l0r1_left
    (rightInverse_of_leftInverse_fin l0r1_left)

def l0r2To : Fin 24 → Fin 24
  | 0 => 20
  | 1 => 1
  | 2 => 18
  | 3 => 19
  | 4 => 11
  | 5 => 10
  | 6 => 6
  | 7 => 22
  | 8 => 8
  | 9 => 9
  | 10 => 16
  | 11 => 21
  | 12 => 12
  | 13 => 7
  | 14 => 3
  | 15 => 15
  | 16 => 5
  | 17 => 0
  | 18 => 23
  | 19 => 14
  | 20 => 17
  | 21 => 4
  | 22 => 13
  | 23 => 2
  | _ => 20

def l0r2Inv : Fin 24 → Fin 24
  | 0 => 17
  | 1 => 1
  | 2 => 23
  | 3 => 14
  | 4 => 21
  | 5 => 16
  | 6 => 6
  | 7 => 13
  | 8 => 8
  | 9 => 9
  | 10 => 5
  | 11 => 4
  | 12 => 12
  | 13 => 22
  | 14 => 19
  | 15 => 15
  | 16 => 10
  | 17 => 20
  | 18 => 2
  | 19 => 3
  | 20 => 0
  | 21 => 11
  | 22 => 7
  | 23 => 18
  | _ => 17

theorem l0r2_left : ∀ x, l0r2Inv (l0r2To x) = x := by decide +kernel
def l0r2 : Equiv.Perm (Fin 24) :=
  tablePerm l0r2To l0r2Inv l0r2_left
    (rightInverse_of_leftInverse_fin l0r2_left)

def l0r3To : Fin 24 → Fin 24
  | 0 => 17
  | 1 => 1
  | 2 => 23
  | 3 => 14
  | 4 => 21
  | 5 => 16
  | 6 => 6
  | 7 => 13
  | 8 => 8
  | 9 => 9
  | 10 => 5
  | 11 => 4
  | 12 => 12
  | 13 => 22
  | 14 => 19
  | 15 => 15
  | 16 => 10
  | 17 => 20
  | 18 => 2
  | 19 => 3
  | 20 => 0
  | 21 => 11
  | 22 => 7
  | 23 => 18
  | _ => 17

def l0r3Inv : Fin 24 → Fin 24
  | 0 => 20
  | 1 => 1
  | 2 => 18
  | 3 => 19
  | 4 => 11
  | 5 => 10
  | 6 => 6
  | 7 => 22
  | 8 => 8
  | 9 => 9
  | 10 => 16
  | 11 => 21
  | 12 => 12
  | 13 => 7
  | 14 => 3
  | 15 => 15
  | 16 => 5
  | 17 => 0
  | 18 => 23
  | 19 => 14
  | 20 => 17
  | 21 => 4
  | 22 => 13
  | 23 => 2
  | _ => 20

theorem l0r3_left : ∀ x, l0r3Inv (l0r3To x) = x := by decide +kernel
def l0r3 : Equiv.Perm (Fin 24) :=
  tablePerm l0r3To l0r3Inv l0r3_left
    (rightInverse_of_leftInverse_fin l0r3_left)

def l0r4To : Fin 24 → Fin 24
  | 0 => 23
  | 1 => 4
  | 2 => 5
  | 3 => 6
  | 4 => 13
  | 5 => 8
  | 6 => 19
  | 7 => 0
  | 8 => 10
  | 9 => 21
  | 10 => 14
  | 11 => 9
  | 12 => 7
  | 13 => 12
  | 14 => 15
  | 15 => 3
  | 16 => 18
  | 17 => 22
  | 18 => 20
  | 19 => 16
  | 20 => 2
  | 21 => 1
  | 22 => 11
  | 23 => 17
  | _ => 23

def l0r4Inv : Fin 24 → Fin 24
  | 0 => 7
  | 1 => 21
  | 2 => 20
  | 3 => 15
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | 7 => 12
  | 8 => 5
  | 9 => 11
  | 10 => 8
  | 11 => 22
  | 12 => 13
  | 13 => 4
  | 14 => 10
  | 15 => 14
  | 16 => 19
  | 17 => 23
  | 18 => 16
  | 19 => 6
  | 20 => 18
  | 21 => 9
  | 22 => 17
  | 23 => 0
  | _ => 7

theorem l0r4_left : ∀ x, l0r4Inv (l0r4To x) = x := by decide +kernel
def l0r4 : Equiv.Perm (Fin 24) :=
  tablePerm l0r4To l0r4Inv l0r4_left
    (rightInverse_of_leftInverse_fin l0r4_left)

def l0r5To : Fin 24 → Fin 24
  | 0 => 2
  | 1 => 4
  | 2 => 20
  | 3 => 16
  | 4 => 9
  | 5 => 14
  | 6 => 19
  | 7 => 11
  | 8 => 10
  | 9 => 21
  | 10 => 18
  | 11 => 1
  | 12 => 7
  | 13 => 0
  | 14 => 6
  | 15 => 3
  | 16 => 8
  | 17 => 23
  | 18 => 17
  | 19 => 15
  | 20 => 22
  | 21 => 13
  | 22 => 12
  | 23 => 5
  | _ => 2

def l0r5Inv : Fin 24 → Fin 24
  | 0 => 13
  | 1 => 11
  | 2 => 0
  | 3 => 15
  | 4 => 1
  | 5 => 23
  | 6 => 14
  | 7 => 12
  | 8 => 16
  | 9 => 4
  | 10 => 8
  | 11 => 7
  | 12 => 22
  | 13 => 21
  | 14 => 5
  | 15 => 19
  | 16 => 3
  | 17 => 18
  | 18 => 10
  | 19 => 6
  | 20 => 2
  | 21 => 9
  | 22 => 20
  | 23 => 17
  | _ => 13

theorem l0r5_left : ∀ x, l0r5Inv (l0r5To x) = x := by decide +kernel
def l0r5 : Equiv.Perm (Fin 24) :=
  tablePerm l0r5To l0r5Inv l0r5_left
    (rightInverse_of_leftInverse_fin l0r5_left)

def l0r6To : Fin 24 → Fin 24
  | 0 => 2
  | 1 => 11
  | 2 => 10
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 14
  | 7 => 20
  | 8 => 16
  | 9 => 4
  | 10 => 3
  | 11 => 9
  | 12 => 22
  | 13 => 12
  | 14 => 15
  | 15 => 19
  | 16 => 23
  | 17 => 13
  | 18 => 17
  | 19 => 5
  | 20 => 18
  | 21 => 1
  | 22 => 21
  | 23 => 0
  | _ => 2

def l0r6Inv : Fin 24 → Fin 24
  | 0 => 23
  | 1 => 21
  | 2 => 0
  | 3 => 10
  | 4 => 9
  | 5 => 19
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | 9 => 11
  | 10 => 2
  | 11 => 1
  | 12 => 13
  | 13 => 17
  | 14 => 6
  | 15 => 14
  | 16 => 8
  | 17 => 18
  | 18 => 20
  | 19 => 15
  | 20 => 7
  | 21 => 22
  | 22 => 12
  | 23 => 16
  | _ => 23

theorem l0r6_left : ∀ x, l0r6Inv (l0r6To x) = x := by decide +kernel
def l0r6 : Equiv.Perm (Fin 24) :=
  tablePerm l0r6To l0r6Inv l0r6_left
    (rightInverse_of_leftInverse_fin l0r6_left)

def l0r7To : Fin 24 → Fin 24
  | 0 => 18
  | 1 => 21
  | 2 => 16
  | 3 => 6
  | 4 => 22
  | 5 => 8
  | 6 => 3
  | 7 => 17
  | 8 => 5
  | 9 => 11
  | 10 => 19
  | 11 => 9
  | 12 => 13
  | 13 => 12
  | 14 => 15
  | 15 => 14
  | 16 => 2
  | 17 => 7
  | 18 => 0
  | 19 => 10
  | 20 => 23
  | 21 => 1
  | 22 => 4
  | 23 => 20
  | _ => 18

def l0r7Inv : Fin 24 → Fin 24
  | 0 => 18
  | 1 => 21
  | 2 => 16
  | 3 => 6
  | 4 => 22
  | 5 => 8
  | 6 => 3
  | 7 => 17
  | 8 => 5
  | 9 => 11
  | 10 => 19
  | 11 => 9
  | 12 => 13
  | 13 => 12
  | 14 => 15
  | 15 => 14
  | 16 => 2
  | 17 => 7
  | 18 => 0
  | 19 => 10
  | 20 => 23
  | 21 => 1
  | 22 => 4
  | 23 => 20
  | _ => 18

theorem l0r7_left : ∀ x, l0r7Inv (l0r7To x) = x := by decide +kernel
def l0r7 : Equiv.Perm (Fin 24) :=
  tablePerm l0r7To l0r7Inv l0r7_left
    (rightInverse_of_leftInverse_fin l0r7_left)

def l0r8To : Fin 24 → Fin 24
  | 0 => 17
  | 1 => 13
  | 2 => 8
  | 3 => 19
  | 4 => 12
  | 5 => 10
  | 6 => 16
  | 7 => 23
  | 8 => 14
  | 9 => 1
  | 10 => 15
  | 11 => 21
  | 12 => 0
  | 13 => 7
  | 14 => 3
  | 15 => 6
  | 16 => 20
  | 17 => 11
  | 18 => 2
  | 19 => 18
  | 20 => 5
  | 21 => 4
  | 22 => 9
  | 23 => 22
  | _ => 17

def l0r8Inv : Fin 24 → Fin 24
  | 0 => 12
  | 1 => 9
  | 2 => 18
  | 3 => 14
  | 4 => 21
  | 5 => 20
  | 6 => 15
  | 7 => 13
  | 8 => 2
  | 9 => 22
  | 10 => 5
  | 11 => 17
  | 12 => 4
  | 13 => 1
  | 14 => 8
  | 15 => 10
  | 16 => 6
  | 17 => 0
  | 18 => 19
  | 19 => 3
  | 20 => 16
  | 21 => 11
  | 22 => 23
  | 23 => 7
  | _ => 12

theorem l0r8_left : ∀ x, l0r8Inv (l0r8To x) = x := by decide +kernel
def l0r8 : Equiv.Perm (Fin 24) :=
  tablePerm l0r8To l0r8Inv l0r8_left
    (rightInverse_of_leftInverse_fin l0r8_left)

def l0r9To : Fin 24 → Fin 24
  | 0 => 5
  | 1 => 9
  | 2 => 14
  | 3 => 19
  | 4 => 0
  | 5 => 10
  | 6 => 15
  | 7 => 2
  | 8 => 18
  | 9 => 13
  | 10 => 6
  | 11 => 21
  | 12 => 11
  | 13 => 7
  | 14 => 3
  | 15 => 16
  | 16 => 17
  | 17 => 12
  | 18 => 22
  | 19 => 8
  | 20 => 20
  | 21 => 4
  | 22 => 1
  | 23 => 23
  | _ => 5

def l0r9Inv : Fin 24 → Fin 24
  | 0 => 4
  | 1 => 22
  | 2 => 7
  | 3 => 14
  | 4 => 21
  | 5 => 0
  | 6 => 10
  | 7 => 13
  | 8 => 19
  | 9 => 1
  | 10 => 5
  | 11 => 12
  | 12 => 17
  | 13 => 9
  | 14 => 2
  | 15 => 6
  | 16 => 15
  | 17 => 16
  | 18 => 8
  | 19 => 3
  | 20 => 20
  | 21 => 11
  | 22 => 18
  | 23 => 23
  | _ => 4

theorem l0r9_left : ∀ x, l0r9Inv (l0r9To x) = x := by decide +kernel
def l0r9 : Equiv.Perm (Fin 24) :=
  tablePerm l0r9To l0r9Inv l0r9_left
    (rightInverse_of_leftInverse_fin l0r9_left)

def l0r10To : Fin 24 → Fin 24
  | 0 => 10
  | 1 => 9
  | 2 => 3
  | 3 => 14
  | 4 => 20
  | 5 => 16
  | 6 => 15
  | 7 => 18
  | 8 => 23
  | 9 => 7
  | 10 => 6
  | 11 => 4
  | 12 => 21
  | 13 => 22
  | 14 => 19
  | 15 => 5
  | 16 => 0
  | 17 => 12
  | 18 => 13
  | 19 => 8
  | 20 => 17
  | 21 => 11
  | 22 => 1
  | 23 => 2
  | _ => 10

def l0r10Inv : Fin 24 → Fin 24
  | 0 => 16
  | 1 => 22
  | 2 => 23
  | 3 => 2
  | 4 => 11
  | 5 => 15
  | 6 => 10
  | 7 => 9
  | 8 => 19
  | 9 => 1
  | 10 => 0
  | 11 => 21
  | 12 => 17
  | 13 => 18
  | 14 => 3
  | 15 => 6
  | 16 => 5
  | 17 => 20
  | 18 => 7
  | 19 => 14
  | 20 => 4
  | 21 => 12
  | 22 => 13
  | 23 => 8
  | _ => 16

theorem l0r10_left : ∀ x, l0r10Inv (l0r10To x) = x := by decide +kernel
def l0r10 : Equiv.Perm (Fin 24) :=
  tablePerm l0r10To l0r10Inv l0r10_left
    (rightInverse_of_leftInverse_fin l0r10_left)

def l0r11To : Fin 24 → Fin 24
  | 0 => 16
  | 1 => 9
  | 2 => 19
  | 3 => 3
  | 4 => 17
  | 5 => 5
  | 6 => 15
  | 7 => 23
  | 8 => 2
  | 9 => 22
  | 10 => 6
  | 11 => 11
  | 12 => 4
  | 13 => 13
  | 14 => 14
  | 15 => 10
  | 16 => 20
  | 17 => 12
  | 18 => 7
  | 19 => 8
  | 20 => 0
  | 21 => 21
  | 22 => 1
  | 23 => 18
  | _ => 16

def l0r11Inv : Fin 24 → Fin 24
  | 0 => 20
  | 1 => 22
  | 2 => 8
  | 3 => 3
  | 4 => 12
  | 5 => 5
  | 6 => 10
  | 7 => 18
  | 8 => 19
  | 9 => 1
  | 10 => 15
  | 11 => 11
  | 12 => 17
  | 13 => 13
  | 14 => 14
  | 15 => 6
  | 16 => 0
  | 17 => 4
  | 18 => 23
  | 19 => 2
  | 20 => 16
  | 21 => 21
  | 22 => 9
  | 23 => 7
  | _ => 20

theorem l0r11_left : ∀ x, l0r11Inv (l0r11To x) = x := by decide +kernel
def l0r11 : Equiv.Perm (Fin 24) :=
  tablePerm l0r11To l0r11Inv l0r11_left
    (rightInverse_of_leftInverse_fin l0r11_left)

def l0r12To : Fin 24 → Fin 24
  | 0 => 8
  | 1 => 21
  | 2 => 15
  | 3 => 16
  | 4 => 23
  | 5 => 14
  | 6 => 3
  | 7 => 5
  | 8 => 20
  | 9 => 12
  | 10 => 19
  | 11 => 1
  | 12 => 9
  | 13 => 0
  | 14 => 6
  | 15 => 18
  | 16 => 22
  | 17 => 7
  | 18 => 11
  | 19 => 10
  | 20 => 2
  | 21 => 13
  | 22 => 4
  | 23 => 17
  | _ => 8

def l0r12Inv : Fin 24 → Fin 24
  | 0 => 13
  | 1 => 11
  | 2 => 20
  | 3 => 6
  | 4 => 22
  | 5 => 7
  | 6 => 14
  | 7 => 17
  | 8 => 0
  | 9 => 12
  | 10 => 19
  | 11 => 18
  | 12 => 9
  | 13 => 21
  | 14 => 5
  | 15 => 2
  | 16 => 3
  | 17 => 23
  | 18 => 15
  | 19 => 10
  | 20 => 8
  | 21 => 1
  | 22 => 16
  | 23 => 4
  | _ => 13

theorem l0r12_left : ∀ x, l0r12Inv (l0r12To x) = x := by decide +kernel
def l0r12 : Equiv.Perm (Fin 24) :=
  tablePerm l0r12To l0r12Inv l0r12_left
    (rightInverse_of_leftInverse_fin l0r12_left)

def l0r13To : Fin 24 → Fin 24
  | 0 => 14
  | 1 => 21
  | 2 => 6
  | 3 => 15
  | 4 => 2
  | 5 => 18
  | 6 => 3
  | 7 => 20
  | 8 => 17
  | 9 => 0
  | 10 => 19
  | 11 => 13
  | 12 => 1
  | 13 => 11
  | 14 => 16
  | 15 => 8
  | 16 => 23
  | 17 => 7
  | 18 => 12
  | 19 => 10
  | 20 => 22
  | 21 => 9
  | 22 => 4
  | 23 => 5
  | _ => 14

def l0r13Inv : Fin 24 → Fin 24
  | 0 => 9
  | 1 => 12
  | 2 => 4
  | 3 => 6
  | 4 => 22
  | 5 => 23
  | 6 => 2
  | 7 => 17
  | 8 => 15
  | 9 => 21
  | 10 => 19
  | 11 => 13
  | 12 => 18
  | 13 => 11
  | 14 => 0
  | 15 => 3
  | 16 => 14
  | 17 => 8
  | 18 => 5
  | 19 => 10
  | 20 => 7
  | 21 => 1
  | 22 => 20
  | 23 => 16
  | _ => 9

theorem l0r13_left : ∀ x, l0r13Inv (l0r13To x) = x := by decide +kernel
def l0r13 : Equiv.Perm (Fin 24) :=
  tablePerm l0r13To l0r13Inv l0r13_left
    (rightInverse_of_leftInverse_fin l0r13_left)

def l0r14To : Fin 24 → Fin 24
  | 0 => 8
  | 1 => 11
  | 2 => 15
  | 3 => 10
  | 4 => 18
  | 5 => 19
  | 6 => 14
  | 7 => 16
  | 8 => 0
  | 9 => 12
  | 10 => 3
  | 11 => 1
  | 12 => 9
  | 13 => 17
  | 14 => 6
  | 15 => 2
  | 16 => 7
  | 17 => 13
  | 18 => 4
  | 19 => 5
  | 20 => 23
  | 21 => 22
  | 22 => 21
  | 23 => 20
  | _ => 8

def l0r14Inv : Fin 24 → Fin 24
  | 0 => 8
  | 1 => 11
  | 2 => 15
  | 3 => 10
  | 4 => 18
  | 5 => 19
  | 6 => 14
  | 7 => 16
  | 8 => 0
  | 9 => 12
  | 10 => 3
  | 11 => 1
  | 12 => 9
  | 13 => 17
  | 14 => 6
  | 15 => 2
  | 16 => 7
  | 17 => 13
  | 18 => 4
  | 19 => 5
  | 20 => 23
  | 21 => 22
  | 22 => 21
  | 23 => 20
  | _ => 8

theorem l0r14_left : ∀ x, l0r14Inv (l0r14To x) = x := by decide +kernel
def l0r14 : Equiv.Perm (Fin 24) :=
  tablePerm l0r14To l0r14Inv l0r14_left
    (rightInverse_of_leftInverse_fin l0r14_left)

def l0r15To : Fin 24 → Fin 24
  | 0 => 10
  | 1 => 13
  | 2 => 3
  | 3 => 8
  | 4 => 5
  | 5 => 6
  | 6 => 16
  | 7 => 14
  | 8 => 22
  | 9 => 7
  | 10 => 15
  | 11 => 4
  | 12 => 21
  | 13 => 2
  | 14 => 19
  | 15 => 17
  | 16 => 12
  | 17 => 11
  | 18 => 1
  | 19 => 18
  | 20 => 20
  | 21 => 0
  | 22 => 9
  | 23 => 23
  | _ => 10

def l0r15Inv : Fin 24 → Fin 24
  | 0 => 21
  | 1 => 18
  | 2 => 13
  | 3 => 2
  | 4 => 11
  | 5 => 4
  | 6 => 5
  | 7 => 9
  | 8 => 3
  | 9 => 22
  | 10 => 0
  | 11 => 17
  | 12 => 16
  | 13 => 1
  | 14 => 7
  | 15 => 10
  | 16 => 6
  | 17 => 15
  | 18 => 19
  | 19 => 14
  | 20 => 20
  | 21 => 12
  | 22 => 8
  | 23 => 23
  | _ => 21

theorem l0r15_left : ∀ x, l0r15Inv (l0r15To x) = x := by decide +kernel
def l0r15 : Equiv.Perm (Fin 24) :=
  tablePerm l0r15To l0r15Inv l0r15_left
    (rightInverse_of_leftInverse_fin l0r15_left)

def l0r16To : Fin 24 → Fin 24
  | 0 => 16
  | 1 => 7
  | 2 => 19
  | 3 => 8
  | 4 => 10
  | 5 => 6
  | 6 => 5
  | 7 => 3
  | 8 => 13
  | 9 => 22
  | 10 => 15
  | 11 => 11
  | 12 => 4
  | 13 => 18
  | 14 => 14
  | 15 => 0
  | 16 => 12
  | 17 => 21
  | 18 => 1
  | 19 => 23
  | 20 => 17
  | 21 => 20
  | 22 => 9
  | 23 => 2
  | _ => 16

def l0r16Inv : Fin 24 → Fin 24
  | 0 => 15
  | 1 => 18
  | 2 => 23
  | 3 => 7
  | 4 => 12
  | 5 => 6
  | 6 => 5
  | 7 => 1
  | 8 => 3
  | 9 => 22
  | 10 => 4
  | 11 => 11
  | 12 => 16
  | 13 => 8
  | 14 => 14
  | 15 => 10
  | 16 => 0
  | 17 => 20
  | 18 => 13
  | 19 => 2
  | 20 => 21
  | 21 => 17
  | 22 => 9
  | 23 => 19
  | _ => 15

theorem l0r16_left : ∀ x, l0r16Inv (l0r16To x) = x := by decide +kernel
def l0r16 : Equiv.Perm (Fin 24) :=
  tablePerm l0r16To l0r16Inv l0r16_left
    (rightInverse_of_leftInverse_fin l0r16_left)

def l0r17To : Fin 24 → Fin 24
  | 0 => 5
  | 1 => 22
  | 2 => 14
  | 3 => 8
  | 4 => 16
  | 5 => 6
  | 6 => 10
  | 7 => 19
  | 8 => 7
  | 9 => 13
  | 10 => 15
  | 11 => 21
  | 12 => 11
  | 13 => 23
  | 14 => 3
  | 15 => 20
  | 16 => 12
  | 17 => 4
  | 18 => 1
  | 19 => 2
  | 20 => 0
  | 21 => 17
  | 22 => 9
  | 23 => 18
  | _ => 5

def l0r17Inv : Fin 24 → Fin 24
  | 0 => 20
  | 1 => 18
  | 2 => 19
  | 3 => 14
  | 4 => 17
  | 5 => 0
  | 6 => 5
  | 7 => 8
  | 8 => 3
  | 9 => 22
  | 10 => 6
  | 11 => 12
  | 12 => 16
  | 13 => 9
  | 14 => 2
  | 15 => 10
  | 16 => 4
  | 17 => 21
  | 18 => 23
  | 19 => 7
  | 20 => 15
  | 21 => 11
  | 22 => 1
  | 23 => 13
  | _ => 20

theorem l0r17_left : ∀ x, l0r17Inv (l0r17To x) = x := by decide +kernel
def l0r17 : Equiv.Perm (Fin 24) :=
  tablePerm l0r17To l0r17Inv l0r17_left
    (rightInverse_of_leftInverse_fin l0r17_left)

def l0r18To : Fin 24 → Fin 24
  | 0 => 14
  | 1 => 12
  | 2 => 6
  | 3 => 10
  | 4 => 8
  | 5 => 19
  | 6 => 18
  | 7 => 15
  | 8 => 11
  | 9 => 0
  | 10 => 3
  | 11 => 13
  | 12 => 1
  | 13 => 5
  | 14 => 16
  | 15 => 22
  | 16 => 7
  | 17 => 9
  | 18 => 4
  | 19 => 20
  | 20 => 2
  | 21 => 23
  | 22 => 21
  | 23 => 17
  | _ => 14

def l0r18Inv : Fin 24 → Fin 24
  | 0 => 9
  | 1 => 12
  | 2 => 20
  | 3 => 10
  | 4 => 18
  | 5 => 13
  | 6 => 2
  | 7 => 16
  | 8 => 4
  | 9 => 17
  | 10 => 3
  | 11 => 8
  | 12 => 1
  | 13 => 11
  | 14 => 0
  | 15 => 7
  | 16 => 14
  | 17 => 23
  | 18 => 6
  | 19 => 5
  | 20 => 19
  | 21 => 22
  | 22 => 15
  | 23 => 21
  | _ => 9

theorem l0r18_left : ∀ x, l0r18Inv (l0r18To x) = x := by decide +kernel
def l0r18 : Equiv.Perm (Fin 24) :=
  tablePerm l0r18To l0r18Inv l0r18_left
    (rightInverse_of_leftInverse_fin l0r18_left)

def l0r19To : Fin 24 → Fin 24
  | 0 => 18
  | 1 => 0
  | 2 => 16
  | 3 => 10
  | 4 => 14
  | 5 => 19
  | 6 => 8
  | 7 => 6
  | 8 => 12
  | 9 => 11
  | 10 => 3
  | 11 => 9
  | 12 => 13
  | 13 => 20
  | 14 => 15
  | 15 => 23
  | 16 => 7
  | 17 => 1
  | 18 => 4
  | 19 => 17
  | 20 => 22
  | 21 => 2
  | 22 => 21
  | 23 => 5
  | _ => 18

def l0r19Inv : Fin 24 → Fin 24
  | 0 => 1
  | 1 => 17
  | 2 => 21
  | 3 => 10
  | 4 => 18
  | 5 => 23
  | 6 => 7
  | 7 => 16
  | 8 => 6
  | 9 => 11
  | 10 => 3
  | 11 => 9
  | 12 => 8
  | 13 => 12
  | 14 => 4
  | 15 => 14
  | 16 => 2
  | 17 => 19
  | 18 => 0
  | 19 => 5
  | 20 => 13
  | 21 => 22
  | 22 => 20
  | 23 => 15
  | _ => 1

theorem l0r19_left : ∀ x, l0r19Inv (l0r19To x) = x := by decide +kernel
def l0r19 : Equiv.Perm (Fin 24) :=
  tablePerm l0r19To l0r19Inv l0r19_left
    (rightInverse_of_leftInverse_fin l0r19_left)

def l0r20To : Fin 24 → Fin 24
  | 0 => 23
  | 1 => 20
  | 2 => 5
  | 3 => 16
  | 4 => 3
  | 5 => 14
  | 6 => 8
  | 7 => 6
  | 8 => 12
  | 9 => 21
  | 10 => 19
  | 11 => 9
  | 12 => 7
  | 13 => 17
  | 14 => 15
  | 15 => 2
  | 16 => 22
  | 17 => 1
  | 18 => 11
  | 19 => 0
  | 20 => 13
  | 21 => 18
  | 22 => 4
  | 23 => 10
  | _ => 23

def l0r20Inv : Fin 24 → Fin 24
  | 0 => 19
  | 1 => 17
  | 2 => 15
  | 3 => 4
  | 4 => 22
  | 5 => 2
  | 6 => 7
  | 7 => 12
  | 8 => 6
  | 9 => 11
  | 10 => 23
  | 11 => 18
  | 12 => 8
  | 13 => 20
  | 14 => 5
  | 15 => 14
  | 16 => 3
  | 17 => 13
  | 18 => 21
  | 19 => 10
  | 20 => 1
  | 21 => 9
  | 22 => 16
  | 23 => 0
  | _ => 19

theorem l0r20_left : ∀ x, l0r20Inv (l0r20To x) = x := by decide +kernel
def l0r20 : Equiv.Perm (Fin 24) :=
  tablePerm l0r20To l0r20Inv l0r20_left
    (rightInverse_of_leftInverse_fin l0r20_left)

def l0r21To : Fin 24 → Fin 24
  | 0 => 2
  | 1 => 17
  | 2 => 10
  | 3 => 5
  | 4 => 19
  | 5 => 3
  | 6 => 8
  | 7 => 6
  | 8 => 12
  | 9 => 4
  | 10 => 14
  | 11 => 9
  | 12 => 22
  | 13 => 0
  | 14 => 15
  | 15 => 18
  | 16 => 13
  | 17 => 1
  | 18 => 21
  | 19 => 20
  | 20 => 7
  | 21 => 23
  | 22 => 11
  | 23 => 16
  | _ => 2

def l0r21Inv : Fin 24 → Fin 24
  | 0 => 13
  | 1 => 17
  | 2 => 0
  | 3 => 5
  | 4 => 9
  | 5 => 3
  | 6 => 7
  | 7 => 20
  | 8 => 6
  | 9 => 11
  | 10 => 2
  | 11 => 22
  | 12 => 8
  | 13 => 16
  | 14 => 10
  | 15 => 14
  | 16 => 23
  | 17 => 1
  | 18 => 15
  | 19 => 4
  | 20 => 19
  | 21 => 18
  | 22 => 12
  | 23 => 21
  | _ => 13

theorem l0r21_left : ∀ x, l0r21Inv (l0r21To x) = x := by decide +kernel
def l0r21 : Equiv.Perm (Fin 24) :=
  tablePerm l0r21To l0r21Inv l0r21_left
    (rightInverse_of_leftInverse_fin l0r21_left)

def l0r22To : Fin 24 → Fin 24
  | 0 => 20
  | 1 => 23
  | 2 => 18
  | 3 => 14
  | 4 => 15
  | 5 => 16
  | 6 => 10
  | 7 => 19
  | 8 => 7
  | 9 => 9
  | 10 => 6
  | 11 => 21
  | 12 => 12
  | 13 => 2
  | 14 => 3
  | 15 => 17
  | 16 => 0
  | 17 => 4
  | 18 => 13
  | 19 => 22
  | 20 => 11
  | 21 => 5
  | 22 => 1
  | 23 => 8
  | _ => 20

def l0r22Inv : Fin 24 → Fin 24
  | 0 => 16
  | 1 => 22
  | 2 => 13
  | 3 => 14
  | 4 => 17
  | 5 => 21
  | 6 => 10
  | 7 => 8
  | 8 => 23
  | 9 => 9
  | 10 => 6
  | 11 => 20
  | 12 => 12
  | 13 => 18
  | 14 => 3
  | 15 => 4
  | 16 => 5
  | 17 => 15
  | 18 => 2
  | 19 => 7
  | 20 => 0
  | 21 => 11
  | 22 => 19
  | 23 => 1
  | _ => 16

theorem l0r22_left : ∀ x, l0r22Inv (l0r22To x) = x := by decide +kernel
def l0r22 : Equiv.Perm (Fin 24) :=
  tablePerm l0r22To l0r22Inv l0r22_left
    (rightInverse_of_leftInverse_fin l0r22_left)

def l0r23To : Fin 24 → Fin 24
  | 0 => 17
  | 1 => 2
  | 2 => 8
  | 3 => 18
  | 4 => 6
  | 5 => 15
  | 6 => 10
  | 7 => 19
  | 8 => 7
  | 9 => 1
  | 10 => 16
  | 11 => 21
  | 12 => 0
  | 13 => 22
  | 14 => 3
  | 15 => 5
  | 16 => 11
  | 17 => 4
  | 18 => 9
  | 19 => 23
  | 20 => 12
  | 21 => 20
  | 22 => 13
  | 23 => 14
  | _ => 17

def l0r23Inv : Fin 24 → Fin 24
  | 0 => 12
  | 1 => 9
  | 2 => 1
  | 3 => 14
  | 4 => 17
  | 5 => 15
  | 6 => 4
  | 7 => 8
  | 8 => 2
  | 9 => 18
  | 10 => 6
  | 11 => 16
  | 12 => 20
  | 13 => 22
  | 14 => 23
  | 15 => 5
  | 16 => 10
  | 17 => 0
  | 18 => 3
  | 19 => 7
  | 20 => 21
  | 21 => 11
  | 22 => 13
  | 23 => 19
  | _ => 12

theorem l0r23_left : ∀ x, l0r23Inv (l0r23To x) = x := by decide +kernel
def l0r23 : Equiv.Perm (Fin 24) :=
  tablePerm l0r23To l0r23Inv l0r23_left
    (rightInverse_of_leftInverse_fin l0r23_left)

def rep0 : Fin 24 → Equiv.Perm (Fin 24)
  | 0 => l0r0
  | 1 => l0r1
  | 2 => l0r2
  | 3 => l0r3
  | 4 => l0r4
  | 5 => l0r5
  | 6 => l0r6
  | 7 => l0r7
  | 8 => l0r8
  | 9 => l0r9
  | 10 => l0r10
  | 11 => l0r11
  | 12 => l0r12
  | 13 => l0r13
  | 14 => l0r14
  | 15 => l0r15
  | 16 => l0r16
  | 17 => l0r17
  | 18 => l0r18
  | 19 => l0r19
  | 20 => l0r20
  | 21 => l0r21
  | 22 => l0r22
  | 23 => l0r23
  | _ => l0r0

def rep0Word : Fin 24 → List (Fin 4)
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [3]
  | 4 => [0, 1]
  | 5 => [0, 3]
  | 6 => [1, 0, 1]
  | 7 => [3, 0, 1]
  | 8 => [0, 1, 0, 1]
  | 9 => [0, 3, 0, 1]
  | 10 => [1, 0, 3, 0, 1]
  | 11 => [3, 0, 3, 0, 1]
  | 12 => [0, 1, 0, 3, 0, 1]
  | 13 => [0, 3, 0, 3, 0, 1]
  | 14 => [3, 0, 1, 0, 3, 0, 1]
  | 15 => [0, 3, 0, 1, 0, 3, 0, 1]
  | 16 => [1, 0, 3, 0, 1, 0, 3, 0, 1]
  | 17 => [3, 0, 3, 0, 1, 0, 3, 0, 1]
  | 18 => [0, 1, 0, 3, 0, 1, 0, 3, 0, 1]
  | 19 => [0, 3, 0, 3, 0, 1, 0, 3, 0, 1]
  | 20 => [1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1]
  | 21 => [3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1]
  | 22 => [0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1]
  | 23 => [0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1]
  | _ => []

theorem rep0_eq_word : ∀ r, rep0 r = evalWord gen0 (rep0Word r) := by decide +kernel

def point0 : Fin 24 → Fin 24
  | 0 => 4
  | 1 => 1
  | 2 => 11
  | 3 => 21
  | 4 => 13
  | 5 => 9
  | 6 => 7
  | 7 => 22
  | 8 => 12
  | 9 => 0
  | 10 => 20
  | 11 => 17
  | 12 => 23
  | 13 => 2
  | 14 => 18
  | 15 => 5
  | 16 => 10
  | 17 => 16
  | 18 => 8
  | 19 => 14
  | 20 => 3
  | 21 => 19
  | 22 => 15
  | 23 => 6
  | _ => 4

def pointInv0 : Fin 24 → Fin 24
  | 0 => 9
  | 1 => 1
  | 2 => 13
  | 3 => 20
  | 4 => 0
  | 5 => 15
  | 6 => 23
  | 7 => 6
  | 8 => 18
  | 9 => 5
  | 10 => 16
  | 11 => 2
  | 12 => 8
  | 13 => 4
  | 14 => 19
  | 15 => 22
  | 16 => 17
  | 17 => 11
  | 18 => 14
  | 19 => 21
  | 20 => 10
  | 21 => 3
  | 22 => 7
  | 23 => 12
  | _ => 9

theorem point0_injective : Function.Injective point0 := by
  have h : ∀ r, pointInv0 (point0 r) = r := by decide +kernel
  exact Function.LeftInverse.injective h

def act0 : Fin 4 → Fin 24 → Fin 24
  | 0 => ![1, 0, 4, 5, 2, 3, 8, 9, 6, 7, 12, 13, 10, 11, 15, 14, 18, 19, 16, 17, 22, 23, 20, 21]
  | 1 => ![2, 1, 3, 0, 6, 5, 7, 4, 8, 10, 11, 9, 13, 14, 12, 16, 17, 15, 18, 20, 21, 19, 22, 23]
  | 2 => ![1, 0, 4, 5, 2, 3, 8, 9, 6, 7, 12, 13, 10, 11, 15, 14, 18, 19, 16, 17, 22, 23, 20, 21]
  | 3 => ![3, 1, 0, 2, 7, 5, 4, 6, 8, 11, 9, 10, 14, 12, 13, 17, 15, 16, 18, 21, 19, 20, 22, 23]
  | _ => ![1, 0, 4, 5, 2, 3, 8, 9, 6, 7, 12, 13, 10, 11, 15, 14, 18, 19, 16, 17, 22, 23, 20, 21]

def factor0 : Fin 4 → Fin 24 → List (Fin 6)
  | 0, 0 => []
  | 0, 1 => []
  | 0, 2 => []
  | 0, 3 => []
  | 0, 4 => []
  | 0, 5 => []
  | 0, 6 => []
  | 0, 7 => []
  | 0, 8 => []
  | 0, 9 => []
  | 0, 10 => []
  | 0, 11 => []
  | 0, 12 => []
  | 0, 13 => []
  | 0, 14 => []
  | 0, 15 => []
  | 0, 16 => []
  | 0, 17 => []
  | 0, 18 => []
  | 0, 19 => []
  | 0, 20 => []
  | 0, 21 => []
  | 0, 22 => []
  | 0, 23 => []
  | 1, 0 => []
  | 1, 1 => [3, 4, 3, 5]
  | 1, 2 => []
  | 1, 3 => []
  | 1, 4 => []
  | 1, 5 => [2, 1, 0, 1, 2]
  | 1, 6 => []
  | 1, 7 => []
  | 1, 8 => [3, 1, 0, 1, 2, 1, 0]
  | 1, 9 => []
  | 1, 10 => []
  | 1, 11 => []
  | 1, 12 => [4, 3, 5, 4, 3, 1]
  | 1, 13 => [0, 1, 3, 1, 2, 0]
  | 1, 14 => []
  | 1, 15 => []
  | 1, 16 => []
  | 1, 17 => []
  | 1, 18 => [4, 0, 1, 0, 2, 1]
  | 1, 19 => []
  | 1, 20 => []
  | 1, 21 => []
  | 1, 22 => [5, 3, 1, 5, 4, 2]
  | 1, 23 => [4, 3, 4, 3]
  | 2, 0 => []
  | 2, 1 => []
  | 2, 2 => []
  | 2, 3 => []
  | 2, 4 => []
  | 2, 5 => []
  | 2, 6 => []
  | 2, 7 => []
  | 2, 8 => []
  | 2, 9 => []
  | 2, 10 => []
  | 2, 11 => []
  | 2, 12 => []
  | 2, 13 => []
  | 2, 14 => []
  | 2, 15 => []
  | 2, 16 => []
  | 2, 17 => []
  | 2, 18 => []
  | 2, 19 => []
  | 2, 20 => []
  | 2, 21 => []
  | 2, 22 => []
  | 2, 23 => []
  | 3, 0 => []
  | 3, 1 => [2, 0, 1, 0]
  | 3, 2 => []
  | 3, 3 => []
  | 3, 4 => []
  | 3, 5 => [5, 4, 3, 4, 5]
  | 3, 6 => []
  | 3, 7 => []
  | 3, 8 => [3, 2, 1, 2, 3, 4, 0]
  | 3, 9 => []
  | 3, 10 => []
  | 3, 11 => []
  | 3, 12 => []
  | 3, 13 => [0, 1, 3, 1, 2, 0]
  | 3, 14 => [4, 3, 5, 4, 3, 1]
  | 3, 15 => []
  | 3, 16 => []
  | 3, 17 => []
  | 3, 18 => [2, 4, 5, 3, 2, 0]
  | 3, 19 => []
  | 3, 20 => []
  | 3, 21 => []
  | 3, 22 => [5, 1, 2, 4, 0, 2]
  | 3, 23 => [0, 1, 0, 1]
  | _, _ => []

theorem rep0_base : rep0 0 = 1 := rfl

theorem rep0_point : ∀ r, rep0 r 4 = point0 r := by decide +kernel

theorem next0_fix : ∀ i, gen1 i 4 = 4 := by decide +kernel

theorem step0 : ∀ i r,
    gen0 i * rep0 r = rep0 (act0 i r) * evalWord gen1 (factor0 i r) := by decide +kernel

theorem card0 :
    Nat.card (wordSubgroup gen0 inv0 inv0_spec) =
      24 * Nat.card (wordSubgroup gen1 inv1 inv1_spec) :=
  wordSubgroup_card_eq_mul_next
    gen0 inv0 inv0_spec gen1 inv1 inv1_spec
    rep0 act0 factor0 4 point0 0
    (fun r => by rw [rep0_eq_word r]; exact evalWord_mem_wordSubgroup _ _ _ _)
    (wordSubgroup_le_of_gen_mem
      (fun i => by rw [gen1_eq_word i]; exact evalWord_mem_wordSubgroup _ _ _ _))
    rep0_base rep0_point point0_injective
    (wordSubgroup_fix_of_gen_fix _ _ _ next0_fix) step0

def l1r0 : Equiv.Perm (Fin 24) := 1

def l1r1To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 14
  | 2 => 23
  | 3 => 7
  | 4 => 4
  | 5 => 20
  | 6 => 10
  | 7 => 22
  | 8 => 1
  | 9 => 9
  | 10 => 17
  | 11 => 16
  | 12 => 5
  | 13 => 13
  | 14 => 8
  | 15 => 11
  | 16 => 15
  | 17 => 6
  | 18 => 18
  | 19 => 2
  | 20 => 12
  | 21 => 21
  | 22 => 3
  | 23 => 19
  | _ => 0

def l1r1Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 8
  | 2 => 19
  | 3 => 22
  | 4 => 4
  | 5 => 12
  | 6 => 17
  | 7 => 3
  | 8 => 14
  | 9 => 9
  | 10 => 6
  | 11 => 15
  | 12 => 20
  | 13 => 13
  | 14 => 1
  | 15 => 16
  | 16 => 11
  | 17 => 10
  | 18 => 18
  | 19 => 23
  | 20 => 5
  | 21 => 21
  | 22 => 7
  | 23 => 2
  | _ => 0

theorem l1r1_left : ∀ x, l1r1Inv (l1r1To x) = x := by decide +kernel
def l1r1 : Equiv.Perm (Fin 24) :=
  tablePerm l1r1To l1r1Inv l1r1_left
    (rightInverse_of_leftInverse_fin l1r1_left)

def l1r2To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 8
  | 2 => 19
  | 3 => 22
  | 4 => 4
  | 5 => 12
  | 6 => 17
  | 7 => 3
  | 8 => 14
  | 9 => 9
  | 10 => 6
  | 11 => 15
  | 12 => 20
  | 13 => 13
  | 14 => 1
  | 15 => 16
  | 16 => 11
  | 17 => 10
  | 18 => 18
  | 19 => 23
  | 20 => 5
  | 21 => 21
  | 22 => 7
  | 23 => 2
  | _ => 0

def l1r2Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 14
  | 2 => 23
  | 3 => 7
  | 4 => 4
  | 5 => 20
  | 6 => 10
  | 7 => 22
  | 8 => 1
  | 9 => 9
  | 10 => 17
  | 11 => 16
  | 12 => 5
  | 13 => 13
  | 14 => 8
  | 15 => 11
  | 16 => 15
  | 17 => 6
  | 18 => 18
  | 19 => 2
  | 20 => 12
  | 21 => 21
  | 22 => 3
  | 23 => 19
  | _ => 0

theorem l1r2_left : ∀ x, l1r2Inv (l1r2To x) = x := by decide +kernel
def l1r2 : Equiv.Perm (Fin 24) :=
  tablePerm l1r2To l1r2Inv l1r2_left
    (rightInverse_of_leftInverse_fin l1r2_left)

def l1r3To : Fin 24 → Fin 24
  | 0 => 10
  | 1 => 23
  | 2 => 22
  | 3 => 8
  | 4 => 4
  | 5 => 12
  | 6 => 16
  | 7 => 14
  | 8 => 1
  | 9 => 19
  | 10 => 21
  | 11 => 0
  | 12 => 5
  | 13 => 7
  | 14 => 13
  | 15 => 20
  | 16 => 17
  | 17 => 6
  | 18 => 18
  | 19 => 9
  | 20 => 11
  | 21 => 15
  | 22 => 3
  | 23 => 2
  | _ => 10

def l1r3Inv : Fin 24 → Fin 24
  | 0 => 11
  | 1 => 8
  | 2 => 23
  | 3 => 22
  | 4 => 4
  | 5 => 12
  | 6 => 17
  | 7 => 13
  | 8 => 3
  | 9 => 19
  | 10 => 0
  | 11 => 20
  | 12 => 5
  | 13 => 14
  | 14 => 7
  | 15 => 21
  | 16 => 6
  | 17 => 16
  | 18 => 18
  | 19 => 9
  | 20 => 15
  | 21 => 10
  | 22 => 2
  | 23 => 1
  | _ => 11

theorem l1r3_left : ∀ x, l1r3Inv (l1r3To x) = x := by decide +kernel
def l1r3 : Equiv.Perm (Fin 24) :=
  tablePerm l1r3To l1r3Inv l1r3_left
    (rightInverse_of_leftInverse_fin l1r3_left)

def l1r4To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 18
  | 2 => 22
  | 3 => 2
  | 4 => 4
  | 5 => 11
  | 6 => 20
  | 7 => 1
  | 8 => 3
  | 9 => 19
  | 10 => 12
  | 11 => 5
  | 12 => 17
  | 13 => 8
  | 14 => 7
  | 15 => 21
  | 16 => 15
  | 17 => 6
  | 18 => 14
  | 19 => 13
  | 20 => 16
  | 21 => 10
  | 22 => 23
  | 23 => 9
  | _ => 0

def l1r4Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 7
  | 2 => 3
  | 3 => 8
  | 4 => 4
  | 5 => 11
  | 6 => 17
  | 7 => 14
  | 8 => 13
  | 9 => 23
  | 10 => 21
  | 11 => 5
  | 12 => 10
  | 13 => 19
  | 14 => 18
  | 15 => 16
  | 16 => 20
  | 17 => 12
  | 18 => 1
  | 19 => 9
  | 20 => 6
  | 21 => 15
  | 22 => 2
  | 23 => 22
  | _ => 0

theorem l1r4_left : ∀ x, l1r4Inv (l1r4To x) = x := by decide +kernel
def l1r4 : Equiv.Perm (Fin 24) :=
  tablePerm l1r4To l1r4Inv l1r4_left
    (rightInverse_of_leftInverse_fin l1r4_left)

def l1r5To : Fin 24 → Fin 24
  | 0 => 16
  | 1 => 22
  | 2 => 14
  | 3 => 13
  | 4 => 4
  | 5 => 11
  | 6 => 0
  | 7 => 23
  | 8 => 1
  | 9 => 2
  | 10 => 15
  | 11 => 10
  | 12 => 5
  | 13 => 8
  | 14 => 7
  | 15 => 12
  | 16 => 21
  | 17 => 6
  | 18 => 18
  | 19 => 19
  | 20 => 20
  | 21 => 17
  | 22 => 3
  | 23 => 9
  | _ => 16

def l1r5Inv : Fin 24 → Fin 24
  | 0 => 6
  | 1 => 8
  | 2 => 9
  | 3 => 22
  | 4 => 4
  | 5 => 12
  | 6 => 17
  | 7 => 14
  | 8 => 13
  | 9 => 23
  | 10 => 11
  | 11 => 5
  | 12 => 15
  | 13 => 3
  | 14 => 2
  | 15 => 10
  | 16 => 0
  | 17 => 21
  | 18 => 18
  | 19 => 19
  | 20 => 20
  | 21 => 16
  | 22 => 1
  | 23 => 7
  | _ => 6

theorem l1r5_left : ∀ x, l1r5Inv (l1r5To x) = x := by decide +kernel
def l1r5 : Equiv.Perm (Fin 24) :=
  tablePerm l1r5To l1r5Inv l1r5_left
    (rightInverse_of_leftInverse_fin l1r5_left)

def l1r6To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 18
  | 2 => 3
  | 3 => 8
  | 4 => 4
  | 5 => 10
  | 6 => 21
  | 7 => 23
  | 8 => 22
  | 9 => 19
  | 10 => 5
  | 11 => 12
  | 12 => 16
  | 13 => 2
  | 14 => 13
  | 15 => 20
  | 16 => 15
  | 17 => 6
  | 18 => 14
  | 19 => 7
  | 20 => 17
  | 21 => 11
  | 22 => 1
  | 23 => 9
  | _ => 0

def l1r6Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 22
  | 2 => 13
  | 3 => 2
  | 4 => 4
  | 5 => 10
  | 6 => 17
  | 7 => 19
  | 8 => 3
  | 9 => 23
  | 10 => 5
  | 11 => 21
  | 12 => 11
  | 13 => 14
  | 14 => 18
  | 15 => 16
  | 16 => 12
  | 17 => 20
  | 18 => 1
  | 19 => 9
  | 20 => 15
  | 21 => 6
  | 22 => 8
  | 23 => 7
  | _ => 0

theorem l1r6_left : ∀ x, l1r6Inv (l1r6To x) = x := by decide +kernel
def l1r6 : Equiv.Perm (Fin 24) :=
  tablePerm l1r6To l1r6Inv l1r6_left
    (rightInverse_of_leftInverse_fin l1r6_left)

def l1r7To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 7
  | 2 => 9
  | 3 => 1
  | 4 => 4
  | 5 => 16
  | 6 => 12
  | 7 => 23
  | 8 => 18
  | 9 => 19
  | 10 => 6
  | 11 => 15
  | 12 => 11
  | 13 => 8
  | 14 => 3
  | 15 => 5
  | 16 => 21
  | 17 => 20
  | 18 => 14
  | 19 => 22
  | 20 => 17
  | 21 => 10
  | 22 => 2
  | 23 => 13
  | _ => 0

def l1r7Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 22
  | 3 => 14
  | 4 => 4
  | 5 => 15
  | 6 => 10
  | 7 => 1
  | 8 => 13
  | 9 => 2
  | 10 => 21
  | 11 => 12
  | 12 => 6
  | 13 => 23
  | 14 => 18
  | 15 => 11
  | 16 => 5
  | 17 => 20
  | 18 => 8
  | 19 => 9
  | 20 => 17
  | 21 => 16
  | 22 => 19
  | 23 => 7
  | _ => 0

theorem l1r7_left : ∀ x, l1r7Inv (l1r7To x) = x := by decide +kernel
def l1r7 : Equiv.Perm (Fin 24) :=
  tablePerm l1r7To l1r7Inv l1r7_left
    (rightInverse_of_leftInverse_fin l1r7_left)

def l1r8To : Fin 24 → Fin 24
  | 0 => 16
  | 1 => 7
  | 2 => 9
  | 3 => 23
  | 4 => 4
  | 5 => 20
  | 6 => 15
  | 7 => 3
  | 8 => 22
  | 9 => 2
  | 10 => 6
  | 11 => 21
  | 12 => 11
  | 13 => 8
  | 14 => 1
  | 15 => 10
  | 16 => 12
  | 17 => 0
  | 18 => 18
  | 19 => 14
  | 20 => 5
  | 21 => 17
  | 22 => 13
  | 23 => 19
  | _ => 16

def l1r8Inv : Fin 24 → Fin 24
  | 0 => 17
  | 1 => 14
  | 2 => 9
  | 3 => 7
  | 4 => 4
  | 5 => 20
  | 6 => 10
  | 7 => 1
  | 8 => 13
  | 9 => 2
  | 10 => 15
  | 11 => 12
  | 12 => 16
  | 13 => 22
  | 14 => 19
  | 15 => 6
  | 16 => 0
  | 17 => 21
  | 18 => 18
  | 19 => 23
  | 20 => 5
  | 21 => 11
  | 22 => 8
  | 23 => 3
  | _ => 17

theorem l1r8_left : ∀ x, l1r8Inv (l1r8To x) = x := by decide +kernel
def l1r8 : Equiv.Perm (Fin 24) :=
  tablePerm l1r8To l1r8Inv l1r8_left
    (rightInverse_of_leftInverse_fin l1r8_left)

def l1r9To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 13
  | 2 => 9
  | 3 => 23
  | 4 => 4
  | 5 => 17
  | 6 => 5
  | 7 => 1
  | 8 => 18
  | 9 => 19
  | 10 => 6
  | 11 => 15
  | 12 => 10
  | 13 => 2
  | 14 => 22
  | 15 => 12
  | 16 => 20
  | 17 => 21
  | 18 => 14
  | 19 => 3
  | 20 => 16
  | 21 => 11
  | 22 => 8
  | 23 => 7
  | _ => 0

def l1r9Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 7
  | 2 => 13
  | 3 => 19
  | 4 => 4
  | 5 => 6
  | 6 => 10
  | 7 => 23
  | 8 => 22
  | 9 => 2
  | 10 => 12
  | 11 => 21
  | 12 => 15
  | 13 => 1
  | 14 => 18
  | 15 => 11
  | 16 => 20
  | 17 => 5
  | 18 => 8
  | 19 => 9
  | 20 => 16
  | 21 => 17
  | 22 => 14
  | 23 => 3
  | _ => 0

theorem l1r9_left : ∀ x, l1r9Inv (l1r9To x) = x := by decide +kernel
def l1r9 : Equiv.Perm (Fin 24) :=
  tablePerm l1r9To l1r9Inv l1r9_left
    (rightInverse_of_leftInverse_fin l1r9_left)

def l1r10To : Fin 24 → Fin 24
  | 0 => 6
  | 1 => 2
  | 2 => 7
  | 3 => 14
  | 4 => 4
  | 5 => 20
  | 6 => 11
  | 7 => 1
  | 8 => 8
  | 9 => 23
  | 10 => 21
  | 11 => 0
  | 12 => 12
  | 13 => 3
  | 14 => 13
  | 15 => 5
  | 16 => 10
  | 17 => 17
  | 18 => 18
  | 19 => 9
  | 20 => 15
  | 21 => 16
  | 22 => 22
  | 23 => 19
  | _ => 6

def l1r10Inv : Fin 24 → Fin 24
  | 0 => 11
  | 1 => 7
  | 2 => 1
  | 3 => 13
  | 4 => 4
  | 5 => 15
  | 6 => 0
  | 7 => 2
  | 8 => 8
  | 9 => 19
  | 10 => 16
  | 11 => 6
  | 12 => 12
  | 13 => 14
  | 14 => 3
  | 15 => 20
  | 16 => 21
  | 17 => 17
  | 18 => 18
  | 19 => 23
  | 20 => 5
  | 21 => 10
  | 22 => 22
  | 23 => 9
  | _ => 11

theorem l1r10_left : ∀ x, l1r10Inv (l1r10To x) = x := by decide +kernel
def l1r10 : Equiv.Perm (Fin 24) :=
  tablePerm l1r10To l1r10Inv l1r10_left
    (rightInverse_of_leftInverse_fin l1r10_left)

def rep1 : Fin 11 → Equiv.Perm (Fin 24)
  | 0 => l1r0
  | 1 => l1r1
  | 2 => l1r2
  | 3 => l1r3
  | 4 => l1r4
  | 5 => l1r5
  | 6 => l1r6
  | 7 => l1r7
  | 8 => l1r8
  | 9 => l1r9
  | 10 => l1r10
  | _ => l1r0

def rep1Word : Fin 11 → List (Fin 6)
  | 0 => []
  | 1 => [0]
  | 2 => [3]
  | 3 => [1, 0]
  | 4 => [2, 0]
  | 5 => [4, 0]
  | 6 => [5, 0]
  | 7 => [2, 3]
  | 8 => [4, 3]
  | 9 => [5, 3]
  | 10 => [3, 1, 0]
  | _ => []

theorem rep1_eq_word : ∀ r, rep1 r = evalWord gen1 (rep1Word r) := by decide +kernel

def point1 : Fin 11 → Fin 24
  | 0 => 6
  | 1 => 10
  | 2 => 17
  | 3 => 16
  | 4 => 20
  | 5 => 0
  | 6 => 21
  | 7 => 12
  | 8 => 15
  | 9 => 5
  | 10 => 11
  | _ => 6

def pointInv1 : Fin 24 → Fin 11
  | 0 => 5
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 9
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => 10
  | 12 => 7
  | 13 => 0
  | 14 => 0
  | 15 => 8
  | 16 => 3
  | 17 => 2
  | 18 => 0
  | 19 => 0
  | 20 => 4
  | 21 => 6
  | 22 => 0
  | 23 => 0
  | _ => 5

theorem point1_injective : Function.Injective point1 := by
  have h : ∀ r, pointInv1 (point1 r) = r := by decide +kernel
  exact Function.LeftInverse.injective h

def act1 : Fin 6 → Fin 11 → Fin 11
  | 0 => ![1, 2, 0, 8, 7, 5, 6, 9, 10, 4, 3]
  | 1 => ![0, 3, 6, 5, 7, 1, 8, 10, 2, 9, 4]
  | 2 => ![0, 4, 7, 9, 10, 5, 1, 3, 8, 2, 6]
  | 3 => ![2, 0, 1, 10, 9, 5, 6, 4, 3, 7, 8]
  | 4 => ![0, 5, 8, 1, 10, 3, 2, 4, 6, 9, 7]
  | 5 => ![0, 6, 9, 7, 1, 5, 10, 2, 8, 3, 4]
  | _ => ![1, 2, 0, 8, 7, 5, 6, 9, 10, 4, 3]

def factor1 : Fin 6 → Fin 11 → List (Fin 8)
  | 0, 0 => []
  | 0, 1 => []
  | 0, 2 => []
  | 0, 3 => [1, 4, 1]
  | 0, 4 => [5, 0, 7, 2, 1]
  | 0, 5 => [1, 0, 5]
  | 0, 6 => [5, 0, 2, 0]
  | 0, 7 => [3, 1, 3, 5, 0]
  | 0, 8 => [5, 0, 5]
  | 0, 9 => [5, 3, 0, 1]
  | 0, 10 => []
  | 1, 0 => [0]
  | 1, 1 => []
  | 1, 2 => [4, 2, 4, 2]
  | 1, 3 => []
  | 1, 4 => [5, 3, 1, 2]
  | 1, 5 => []
  | 1, 6 => [6, 0, 6, 0]
  | 1, 7 => [3, 5, 6, 0]
  | 1, 8 => []
  | 1, 9 => [7, 0, 3]
  | 1, 10 => [1, 0, 2, 0]
  | 2, 0 => [2]
  | 2, 1 => []
  | 2, 2 => []
  | 2, 3 => [4, 2, 2]
  | 2, 4 => [4, 1, 0]
  | 2, 5 => [0, 7, 4]
  | 2, 6 => []
  | 2, 7 => [2, 2, 0]
  | 2, 8 => [4, 1, 3]
  | 2, 9 => []
  | 2, 10 => [4, 5, 0]
  | 3, 0 => []
  | 3, 1 => []
  | 3, 2 => []
  | 3, 3 => []
  | 3, 4 => [3, 0, 2, 1]
  | 3, 5 => [1, 4, 5]
  | 3, 6 => [2, 0, 2, 1]
  | 3, 7 => [6, 0, 7, 5, 0]
  | 3, 8 => [5, 0, 5]
  | 3, 9 => [7, 0, 7, 5, 0]
  | 3, 10 => [1, 4, 1]
  | 4, 0 => [4]
  | 4, 1 => []
  | 4, 2 => []
  | 4, 3 => []
  | 4, 4 => [3, 1, 3, 0]
  | 4, 5 => []
  | 4, 6 => [6, 0, 6, 0]
  | 4, 7 => [6, 5, 7, 1]
  | 4, 8 => [4, 2, 4, 2]
  | 4, 9 => [7, 4, 3]
  | 4, 10 => [4, 2, 1, 7]
  | 5, 0 => [6]
  | 5, 1 => []
  | 5, 2 => []
  | 5, 3 => [4, 2, 2]
  | 5, 4 => []
  | 5, 5 => [0, 3, 4]
  | 5, 6 => [4, 1, 0]
  | 5, 7 => []
  | 5, 8 => [7, 5, 0]
  | 5, 9 => [2, 2, 0]
  | 5, 10 => [4, 5, 0]
  | _, _ => []

theorem rep1_base : rep1 0 = 1 := rfl

theorem rep1_point : ∀ r, rep1 r 6 = point1 r := by decide +kernel

theorem next1_fix : ∀ i, gen2 i 6 = 6 := by decide +kernel

theorem step1 : ∀ i r,
    gen1 i * rep1 r = rep1 (act1 i r) * evalWord gen2 (factor1 i r) := by decide +kernel

theorem card1 :
    Nat.card (wordSubgroup gen1 inv1 inv1_spec) =
      11 * Nat.card (wordSubgroup gen2 inv2 inv2_spec) :=
  wordSubgroup_card_eq_mul_next
    gen1 inv1 inv1_spec gen2 inv2 inv2_spec
    rep1 act1 factor1 6 point1 0
    (fun r => by rw [rep1_eq_word r]; exact evalWord_mem_wordSubgroup _ _ _ _)
    (wordSubgroup_le_of_gen_mem
      (fun i => by rw [gen2_eq_word i]; exact evalWord_mem_wordSubgroup _ _ _ _))
    rep1_base rep1_point point1_injective
    (wordSubgroup_fix_of_gen_fix _ _ _ next1_fix) step1

def l2r0 : Equiv.Perm (Fin 24) := 1

def l2r1To : Fin 24 → Fin 24
  | 0 => 10
  | 1 => 1
  | 2 => 9
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 8
  | 8 => 13
  | 9 => 19
  | 10 => 16
  | 11 => 20
  | 12 => 11
  | 13 => 7
  | 14 => 23
  | 15 => 17
  | 16 => 0
  | 17 => 21
  | 18 => 18
  | 19 => 2
  | 20 => 12
  | 21 => 15
  | 22 => 14
  | 23 => 22
  | _ => 10

def l2r1Inv : Fin 24 → Fin 24
  | 0 => 16
  | 1 => 1
  | 2 => 19
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 13
  | 8 => 7
  | 9 => 2
  | 10 => 0
  | 11 => 12
  | 12 => 20
  | 13 => 8
  | 14 => 22
  | 15 => 21
  | 16 => 10
  | 17 => 15
  | 18 => 18
  | 19 => 9
  | 20 => 11
  | 21 => 17
  | 22 => 23
  | 23 => 14
  | _ => 16

theorem l2r1_left : ∀ x, l2r1Inv (l2r1To x) = x := by decide +kernel
def l2r1 : Equiv.Perm (Fin 24) :=
  tablePerm l2r1To l2r1Inv l2r1_left
    (rightInverse_of_leftInverse_fin l2r1_left)

def l2r2To : Fin 24 → Fin 24
  | 0 => 12
  | 1 => 3
  | 2 => 13
  | 3 => 23
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 9
  | 8 => 7
  | 9 => 8
  | 10 => 20
  | 11 => 11
  | 12 => 17
  | 13 => 19
  | 14 => 14
  | 15 => 5
  | 16 => 15
  | 17 => 0
  | 18 => 18
  | 19 => 2
  | 20 => 21
  | 21 => 10
  | 22 => 22
  | 23 => 1
  | _ => 12

def l2r2Inv : Fin 24 → Fin 24
  | 0 => 17
  | 1 => 23
  | 2 => 19
  | 3 => 1
  | 4 => 4
  | 5 => 15
  | 6 => 6
  | 7 => 8
  | 8 => 9
  | 9 => 7
  | 10 => 21
  | 11 => 11
  | 12 => 0
  | 13 => 2
  | 14 => 14
  | 15 => 16
  | 16 => 5
  | 17 => 12
  | 18 => 18
  | 19 => 13
  | 20 => 10
  | 21 => 20
  | 22 => 22
  | 23 => 3
  | _ => 17

theorem l2r2_left : ∀ x, l2r2Inv (l2r2To x) = x := by decide +kernel
def l2r2 : Equiv.Perm (Fin 24) :=
  tablePerm l2r2To l2r2Inv l2r2_left
    (rightInverse_of_leftInverse_fin l2r2_left)

def l2r3To : Fin 24 → Fin 24
  | 0 => 16
  | 1 => 1
  | 2 => 19
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 13
  | 8 => 7
  | 9 => 2
  | 10 => 0
  | 11 => 12
  | 12 => 20
  | 13 => 8
  | 14 => 22
  | 15 => 21
  | 16 => 10
  | 17 => 15
  | 18 => 18
  | 19 => 9
  | 20 => 11
  | 21 => 17
  | 22 => 23
  | 23 => 14
  | _ => 16

def l2r3Inv : Fin 24 → Fin 24
  | 0 => 10
  | 1 => 1
  | 2 => 9
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 8
  | 8 => 13
  | 9 => 19
  | 10 => 16
  | 11 => 20
  | 12 => 11
  | 13 => 7
  | 14 => 23
  | 15 => 17
  | 16 => 0
  | 17 => 21
  | 18 => 18
  | 19 => 2
  | 20 => 12
  | 21 => 15
  | 22 => 14
  | 23 => 22
  | _ => 10

theorem l2r3_left : ∀ x, l2r3Inv (l2r3To x) = x := by decide +kernel
def l2r3 : Equiv.Perm (Fin 24) :=
  tablePerm l2r3To l2r3Inv l2r3_left
    (rightInverse_of_leftInverse_fin l2r3_left)

def l2r4To : Fin 24 → Fin 24
  | 0 => 17
  | 1 => 23
  | 2 => 19
  | 3 => 1
  | 4 => 4
  | 5 => 15
  | 6 => 6
  | 7 => 8
  | 8 => 9
  | 9 => 7
  | 10 => 21
  | 11 => 11
  | 12 => 0
  | 13 => 2
  | 14 => 14
  | 15 => 16
  | 16 => 5
  | 17 => 12
  | 18 => 18
  | 19 => 13
  | 20 => 10
  | 21 => 20
  | 22 => 22
  | 23 => 3
  | _ => 17

def l2r4Inv : Fin 24 → Fin 24
  | 0 => 12
  | 1 => 3
  | 2 => 13
  | 3 => 23
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 9
  | 8 => 7
  | 9 => 8
  | 10 => 20
  | 11 => 11
  | 12 => 17
  | 13 => 19
  | 14 => 14
  | 15 => 5
  | 16 => 15
  | 17 => 0
  | 18 => 18
  | 19 => 2
  | 20 => 21
  | 21 => 10
  | 22 => 22
  | 23 => 1
  | _ => 12

theorem l2r4_left : ∀ x, l2r4Inv (l2r4To x) = x := by decide +kernel
def l2r4 : Equiv.Perm (Fin 24) :=
  tablePerm l2r4To l2r4Inv l2r4_left
    (rightInverse_of_leftInverse_fin l2r4_left)

def l2r5To : Fin 24 → Fin 24
  | 0 => 20
  | 1 => 3
  | 2 => 8
  | 3 => 23
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 7
  | 8 => 19
  | 9 => 2
  | 10 => 15
  | 11 => 21
  | 12 => 11
  | 13 => 9
  | 14 => 1
  | 15 => 0
  | 16 => 12
  | 17 => 10
  | 18 => 18
  | 19 => 13
  | 20 => 17
  | 21 => 5
  | 22 => 14
  | 23 => 22
  | _ => 20

def l2r5Inv : Fin 24 → Fin 24
  | 0 => 15
  | 1 => 14
  | 2 => 9
  | 3 => 1
  | 4 => 4
  | 5 => 21
  | 6 => 6
  | 7 => 7
  | 8 => 2
  | 9 => 13
  | 10 => 17
  | 11 => 12
  | 12 => 16
  | 13 => 19
  | 14 => 22
  | 15 => 10
  | 16 => 5
  | 17 => 20
  | 18 => 18
  | 19 => 8
  | 20 => 0
  | 21 => 11
  | 22 => 23
  | 23 => 3
  | _ => 15

theorem l2r5_left : ∀ x, l2r5Inv (l2r5To x) = x := by decide +kernel
def l2r5 : Equiv.Perm (Fin 24) :=
  tablePerm l2r5To l2r5Inv l2r5_left
    (rightInverse_of_leftInverse_fin l2r5_left)

def l2r6To : Fin 24 → Fin 24
  | 0 => 5
  | 1 => 13
  | 2 => 14
  | 3 => 2
  | 4 => 4
  | 5 => 11
  | 6 => 6
  | 7 => 3
  | 8 => 23
  | 9 => 18
  | 10 => 21
  | 11 => 16
  | 12 => 12
  | 13 => 1
  | 14 => 7
  | 15 => 20
  | 16 => 0
  | 17 => 17
  | 18 => 19
  | 19 => 22
  | 20 => 10
  | 21 => 15
  | 22 => 9
  | 23 => 8
  | _ => 5

def l2r6Inv : Fin 24 → Fin 24
  | 0 => 16
  | 1 => 13
  | 2 => 3
  | 3 => 7
  | 4 => 4
  | 5 => 0
  | 6 => 6
  | 7 => 14
  | 8 => 23
  | 9 => 22
  | 10 => 20
  | 11 => 5
  | 12 => 12
  | 13 => 1
  | 14 => 2
  | 15 => 21
  | 16 => 11
  | 17 => 17
  | 18 => 9
  | 19 => 18
  | 20 => 15
  | 21 => 10
  | 22 => 19
  | 23 => 8
  | _ => 16

theorem l2r6_left : ∀ x, l2r6Inv (l2r6To x) = x := by decide +kernel
def l2r6 : Equiv.Perm (Fin 24) :=
  tablePerm l2r6To l2r6Inv l2r6_left
    (rightInverse_of_leftInverse_fin l2r6_left)

def l2r7To : Fin 24 → Fin 24
  | 0 => 21
  | 1 => 23
  | 2 => 7
  | 3 => 1
  | 4 => 4
  | 5 => 15
  | 6 => 6
  | 7 => 9
  | 8 => 2
  | 9 => 13
  | 10 => 5
  | 11 => 10
  | 12 => 11
  | 13 => 8
  | 14 => 3
  | 15 => 12
  | 16 => 17
  | 17 => 20
  | 18 => 18
  | 19 => 19
  | 20 => 0
  | 21 => 16
  | 22 => 14
  | 23 => 22
  | _ => 21

def l2r7Inv : Fin 24 → Fin 24
  | 0 => 20
  | 1 => 3
  | 2 => 8
  | 3 => 14
  | 4 => 4
  | 5 => 10
  | 6 => 6
  | 7 => 2
  | 8 => 13
  | 9 => 7
  | 10 => 11
  | 11 => 12
  | 12 => 15
  | 13 => 9
  | 14 => 22
  | 15 => 5
  | 16 => 21
  | 17 => 16
  | 18 => 18
  | 19 => 19
  | 20 => 17
  | 21 => 0
  | 22 => 23
  | 23 => 1
  | _ => 20

theorem l2r7_left : ∀ x, l2r7Inv (l2r7To x) = x := by decide +kernel
def l2r7 : Equiv.Perm (Fin 24) :=
  tablePerm l2r7To l2r7Inv l2r7_left
    (rightInverse_of_leftInverse_fin l2r7_left)

def l2r8To : Fin 24 → Fin 24
  | 0 => 11
  | 1 => 3
  | 2 => 7
  | 3 => 22
  | 4 => 4
  | 5 => 0
  | 6 => 6
  | 7 => 19
  | 8 => 8
  | 9 => 13
  | 10 => 12
  | 11 => 20
  | 12 => 21
  | 13 => 2
  | 14 => 23
  | 15 => 5
  | 16 => 17
  | 17 => 10
  | 18 => 18
  | 19 => 9
  | 20 => 15
  | 21 => 16
  | 22 => 14
  | 23 => 1
  | _ => 11

def l2r8Inv : Fin 24 → Fin 24
  | 0 => 5
  | 1 => 23
  | 2 => 13
  | 3 => 1
  | 4 => 4
  | 5 => 15
  | 6 => 6
  | 7 => 2
  | 8 => 8
  | 9 => 19
  | 10 => 17
  | 11 => 0
  | 12 => 10
  | 13 => 9
  | 14 => 22
  | 15 => 20
  | 16 => 21
  | 17 => 16
  | 18 => 18
  | 19 => 7
  | 20 => 11
  | 21 => 12
  | 22 => 3
  | 23 => 14
  | _ => 5

theorem l2r8_left : ∀ x, l2r8Inv (l2r8To x) = x := by decide +kernel
def l2r8 : Equiv.Perm (Fin 24) :=
  tablePerm l2r8To l2r8Inv l2r8_left
    (rightInverse_of_leftInverse_fin l2r8_left)

def l2r9To : Fin 24 → Fin 24
  | 0 => 15
  | 1 => 3
  | 2 => 2
  | 3 => 23
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 19
  | 8 => 9
  | 9 => 13
  | 10 => 12
  | 11 => 17
  | 12 => 21
  | 13 => 7
  | 14 => 22
  | 15 => 10
  | 16 => 20
  | 17 => 5
  | 18 => 18
  | 19 => 8
  | 20 => 11
  | 21 => 0
  | 22 => 1
  | 23 => 14
  | _ => 15

def l2r9Inv : Fin 24 → Fin 24
  | 0 => 21
  | 1 => 22
  | 2 => 2
  | 3 => 1
  | 4 => 4
  | 5 => 17
  | 6 => 6
  | 7 => 13
  | 8 => 19
  | 9 => 8
  | 10 => 15
  | 11 => 20
  | 12 => 10
  | 13 => 9
  | 14 => 23
  | 15 => 0
  | 16 => 5
  | 17 => 11
  | 18 => 18
  | 19 => 7
  | 20 => 16
  | 21 => 12
  | 22 => 14
  | 23 => 3
  | _ => 21

theorem l2r9_left : ∀ x, l2r9Inv (l2r9To x) = x := by decide +kernel
def l2r9 : Equiv.Perm (Fin 24) :=
  tablePerm l2r9To l2r9Inv l2r9_left
    (rightInverse_of_leftInverse_fin l2r9_left)

def rep2 : Fin 10 → Equiv.Perm (Fin 24)
  | 0 => l2r0
  | 1 => l2r1
  | 2 => l2r2
  | 3 => l2r3
  | 4 => l2r4
  | 5 => l2r5
  | 6 => l2r6
  | 7 => l2r7
  | 8 => l2r8
  | 9 => l2r9
  | _ => l2r0

def rep2Word : Fin 10 → List (Fin 8)
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [4]
  | 4 => [5]
  | 5 => [1, 0]
  | 6 => [3, 0]
  | 7 => [5, 0]
  | 8 => [0, 1]
  | 9 => [1, 4]
  | _ => []

theorem rep2_eq_word : ∀ r, rep2 r = evalWord gen2 (rep2Word r) := by decide +kernel

def point2 : Fin 10 → Fin 24
  | 0 => 0
  | 1 => 10
  | 2 => 12
  | 3 => 16
  | 4 => 17
  | 5 => 20
  | 6 => 5
  | 7 => 21
  | 8 => 11
  | 9 => 15
  | _ => 0

def pointInv2 : Fin 24 → Fin 10
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 6
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => 8
  | 12 => 2
  | 13 => 0
  | 14 => 0
  | 15 => 9
  | 16 => 3
  | 17 => 4
  | 18 => 0
  | 19 => 0
  | 20 => 5
  | 21 => 7
  | 22 => 0
  | 23 => 0
  | _ => 0

theorem point2_injective : Function.Injective point2 := by
  have h : ∀ r, pointInv2 (point2 r) = r := by decide +kernel
  exact Function.LeftInverse.injective h

def act2 : Fin 8 → Fin 10 → Fin 10
  | 0 => ![1, 3, 8, 0, 7, 2, 6, 9, 5, 4]
  | 1 => ![2, 5, 4, 9, 0, 7, 3, 1, 8, 6]
  | 2 => ![0, 5, 3, 6, 2, 8, 4, 1, 7, 9]
  | 3 => ![0, 6, 1, 7, 5, 3, 8, 4, 2, 9]
  | 4 => ![3, 0, 5, 1, 9, 8, 6, 4, 2, 7]
  | 5 => ![4, 7, 0, 6, 2, 1, 9, 5, 8, 3]
  | 6 => ![0, 7, 4, 2, 6, 1, 3, 8, 5, 9]
  | 7 => ![0, 2, 8, 5, 7, 4, 1, 3, 6, 9]
  | _ => ![1, 3, 8, 0, 7, 2, 6, 9, 5, 4]

def factor2 : Fin 8 → Fin 10 → List (Fin 8)
  | 0, 0 => []
  | 0, 1 => []
  | 0, 2 => []
  | 0, 3 => []
  | 0, 4 => [1, 0]
  | 0, 5 => [0]
  | 0, 6 => [3, 0, 7, 0]
  | 0, 7 => [0, 1, 0]
  | 0, 8 => [0]
  | 0, 9 => [1]
  | 1, 0 => []
  | 1, 1 => []
  | 1, 2 => []
  | 1, 3 => []
  | 1, 4 => []
  | 1, 5 => []
  | 1, 6 => [3, 2]
  | 1, 7 => []
  | 1, 8 => [0, 1]
  | 1, 9 => [7, 2]
  | 2, 0 => [2]
  | 2, 1 => [7, 0, 3]
  | 2, 2 => [0, 2]
  | 2, 3 => [1, 0, 3]
  | 2, 4 => [6]
  | 2, 5 => [7, 0, 7, 0]
  | 2, 6 => [0, 7, 0, 1]
  | 2, 7 => [2, 0, 6]
  | 2, 8 => [7, 0, 3]
  | 2, 9 => [0, 6, 0]
  | 3, 0 => [3]
  | 3, 1 => []
  | 3, 2 => [7, 2, 0, 1]
  | 3, 3 => [7, 0, 1]
  | 3, 4 => [0, 7, 0, 1]
  | 3, 5 => [1, 0, 7, 0]
  | 3, 6 => [0, 1]
  | 3, 7 => [1, 0, 7]
  | 3, 8 => [6, 0, 7]
  | 3, 9 => [3, 0, 6]
  | 4, 0 => []
  | 4, 1 => []
  | 4, 2 => [0]
  | 4, 3 => []
  | 4, 4 => [1]
  | 4, 5 => [0]
  | 4, 6 => [2, 0, 6, 0]
  | 4, 7 => [0, 1]
  | 4, 8 => []
  | 4, 9 => [0, 1, 0]
  | 5, 0 => []
  | 5, 1 => []
  | 5, 2 => []
  | 5, 3 => [7, 2]
  | 5, 4 => []
  | 5, 5 => []
  | 5, 6 => [3, 2]
  | 5, 7 => []
  | 5, 8 => [1, 0]
  | 5, 9 => []
  | 6, 0 => [6]
  | 6, 1 => [2, 0, 6]
  | 6, 2 => [2]
  | 6, 3 => [6, 0]
  | 6, 4 => [1, 0, 3, 0]
  | 6, 5 => [7, 0, 3]
  | 6, 6 => [7, 0, 1]
  | 6, 7 => [7, 0, 3]
  | 6, 8 => [7, 0, 7, 0]
  | 6, 9 => [0, 2, 0]
  | 7, 0 => [7]
  | 7, 1 => [7, 0, 6, 0]
  | 7, 2 => [3, 0, 2]
  | 7, 3 => [0, 3, 0, 1]
  | 7, 4 => [3, 0, 1]
  | 7, 5 => [1, 0, 3, 0]
  | 7, 6 => []
  | 7, 7 => [1, 0, 3]
  | 7, 8 => [1, 0]
  | 7, 9 => [2, 0, 7]
  | _, _ => []

theorem rep2_base : rep2 0 = 1 := rfl

theorem rep2_point : ∀ r, rep2 r 0 = point2 r := by decide +kernel

theorem next2_fix : ∀ i, gen3 i 0 = 0 := by decide +kernel

theorem step2 : ∀ i r,
    gen2 i * rep2 r = rep2 (act2 i r) * evalWord gen3 (factor2 i r) := by decide +kernel

theorem card2 :
    Nat.card (wordSubgroup gen2 inv2 inv2_spec) =
      10 * Nat.card (wordSubgroup gen3 inv3 inv3_spec) :=
  wordSubgroup_card_eq_mul_next
    gen2 inv2 inv2_spec gen3 inv3 inv3_spec
    rep2 act2 factor2 0 point2 0
    (fun r => by rw [rep2_eq_word r]; exact evalWord_mem_wordSubgroup _ _ _ _)
    (wordSubgroup_le_of_gen_mem
      (fun i => by rw [gen3_eq_word i]; exact evalWord_mem_wordSubgroup _ _ _ _))
    rep2_base rep2_point point2_injective
    (wordSubgroup_fix_of_gen_fix _ _ _ next2_fix) step2

def l3r0 : Equiv.Perm (Fin 24) := 1

def l3r1To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 22
  | 4 => 4
  | 5 => 17
  | 6 => 6
  | 7 => 9
  | 8 => 19
  | 9 => 7
  | 10 => 12
  | 11 => 16
  | 12 => 10
  | 13 => 13
  | 14 => 23
  | 15 => 21
  | 16 => 11
  | 17 => 5
  | 18 => 18
  | 19 => 8
  | 20 => 20
  | 21 => 15
  | 22 => 3
  | 23 => 14
  | _ => 0

def l3r1Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 22
  | 4 => 4
  | 5 => 17
  | 6 => 6
  | 7 => 9
  | 8 => 19
  | 9 => 7
  | 10 => 12
  | 11 => 16
  | 12 => 10
  | 13 => 13
  | 14 => 23
  | 15 => 21
  | 16 => 11
  | 17 => 5
  | 18 => 18
  | 19 => 8
  | 20 => 20
  | 21 => 15
  | 22 => 3
  | 23 => 14
  | _ => 0

theorem l3r1_left : ∀ x, l3r1Inv (l3r1To x) = x := by decide +kernel
def l3r1 : Equiv.Perm (Fin 24) :=
  tablePerm l3r1To l3r1Inv l3r1_left
    (rightInverse_of_leftInverse_fin l3r1_left)

def l3r2To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 23
  | 2 => 8
  | 3 => 3
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 9
  | 8 => 19
  | 9 => 13
  | 10 => 5
  | 11 => 17
  | 12 => 11
  | 13 => 7
  | 14 => 1
  | 15 => 20
  | 16 => 10
  | 17 => 12
  | 18 => 18
  | 19 => 2
  | 20 => 21
  | 21 => 15
  | 22 => 22
  | 23 => 14
  | _ => 0

def l3r2Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 14
  | 2 => 19
  | 3 => 3
  | 4 => 4
  | 5 => 10
  | 6 => 6
  | 7 => 13
  | 8 => 2
  | 9 => 7
  | 10 => 16
  | 11 => 12
  | 12 => 17
  | 13 => 9
  | 14 => 23
  | 15 => 21
  | 16 => 5
  | 17 => 11
  | 18 => 18
  | 19 => 8
  | 20 => 15
  | 21 => 20
  | 22 => 22
  | 23 => 1
  | _ => 0

theorem l3r2_left : ∀ x, l3r2Inv (l3r2To x) = x := by decide +kernel
def l3r2 : Equiv.Perm (Fin 24) :=
  tablePerm l3r2To l3r2Inv l3r2_left
    (rightInverse_of_leftInverse_fin l3r2_left)

def l3r3To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 13
  | 3 => 1
  | 4 => 4
  | 5 => 12
  | 6 => 6
  | 7 => 19
  | 8 => 9
  | 9 => 2
  | 10 => 16
  | 11 => 5
  | 12 => 20
  | 13 => 8
  | 14 => 22
  | 15 => 10
  | 16 => 21
  | 17 => 17
  | 18 => 14
  | 19 => 7
  | 20 => 11
  | 21 => 15
  | 22 => 23
  | 23 => 18
  | _ => 0

def l3r3Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 9
  | 3 => 1
  | 4 => 4
  | 5 => 11
  | 6 => 6
  | 7 => 19
  | 8 => 13
  | 9 => 8
  | 10 => 15
  | 11 => 20
  | 12 => 5
  | 13 => 2
  | 14 => 18
  | 15 => 21
  | 16 => 10
  | 17 => 17
  | 18 => 23
  | 19 => 7
  | 20 => 12
  | 21 => 16
  | 22 => 14
  | 23 => 22
  | _ => 0

theorem l3r3_left : ∀ x, l3r3Inv (l3r3To x) = x := by decide +kernel
def l3r3 : Equiv.Perm (Fin 24) :=
  tablePerm l3r3To l3r3Inv l3r3_left
    (rightInverse_of_leftInverse_fin l3r3_left)

def l3r4To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 13
  | 2 => 22
  | 3 => 8
  | 4 => 4
  | 5 => 20
  | 6 => 6
  | 7 => 14
  | 8 => 18
  | 9 => 1
  | 10 => 10
  | 11 => 21
  | 12 => 5
  | 13 => 23
  | 14 => 7
  | 15 => 17
  | 16 => 12
  | 17 => 11
  | 18 => 19
  | 19 => 3
  | 20 => 16
  | 21 => 15
  | 22 => 2
  | 23 => 9
  | _ => 0

def l3r4Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 9
  | 2 => 22
  | 3 => 19
  | 4 => 4
  | 5 => 12
  | 6 => 6
  | 7 => 14
  | 8 => 3
  | 9 => 23
  | 10 => 10
  | 11 => 17
  | 12 => 16
  | 13 => 1
  | 14 => 7
  | 15 => 21
  | 16 => 20
  | 17 => 15
  | 18 => 8
  | 19 => 18
  | 20 => 5
  | 21 => 11
  | 22 => 2
  | 23 => 13
  | _ => 0

theorem l3r4_left : ∀ x, l3r4Inv (l3r4To x) = x := by decide +kernel
def l3r4 : Equiv.Perm (Fin 24) :=
  tablePerm l3r4To l3r4Inv l3r4_left
    (rightInverse_of_leftInverse_fin l3r4_left)

def l3r5To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 22
  | 2 => 7
  | 3 => 23
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 19
  | 8 => 9
  | 9 => 8
  | 10 => 17
  | 11 => 12
  | 12 => 21
  | 13 => 2
  | 14 => 3
  | 15 => 11
  | 16 => 20
  | 17 => 16
  | 18 => 14
  | 19 => 13
  | 20 => 10
  | 21 => 15
  | 22 => 1
  | 23 => 18
  | _ => 0

def l3r5Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 22
  | 2 => 13
  | 3 => 14
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 2
  | 8 => 9
  | 9 => 8
  | 10 => 20
  | 11 => 15
  | 12 => 11
  | 13 => 19
  | 14 => 18
  | 15 => 21
  | 16 => 17
  | 17 => 10
  | 18 => 23
  | 19 => 7
  | 20 => 16
  | 21 => 12
  | 22 => 1
  | 23 => 3
  | _ => 0

theorem l3r5_left : ∀ x, l3r5Inv (l3r5To x) = x := by decide +kernel
def l3r5 : Equiv.Perm (Fin 24) :=
  tablePerm l3r5To l3r5Inv l3r5_left
    (rightInverse_of_leftInverse_fin l3r5_left)

def l3r6To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 7
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | 5 => 21
  | 6 => 6
  | 7 => 14
  | 8 => 18
  | 9 => 23
  | 10 => 11
  | 11 => 20
  | 12 => 12
  | 13 => 1
  | 14 => 13
  | 15 => 16
  | 16 => 5
  | 17 => 10
  | 18 => 19
  | 19 => 22
  | 20 => 17
  | 21 => 15
  | 22 => 8
  | 23 => 9
  | _ => 0

def l3r6Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 13
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 1
  | 8 => 22
  | 9 => 23
  | 10 => 17
  | 11 => 10
  | 12 => 12
  | 13 => 14
  | 14 => 7
  | 15 => 21
  | 16 => 15
  | 17 => 20
  | 18 => 8
  | 19 => 18
  | 20 => 11
  | 21 => 5
  | 22 => 19
  | 23 => 9
  | _ => 0

theorem l3r6_left : ∀ x, l3r6Inv (l3r6To x) = x := by decide +kernel
def l3r6 : Equiv.Perm (Fin 24) :=
  tablePerm l3r6To l3r6Inv l3r6_left
    (rightInverse_of_leftInverse_fin l3r6_left)

def l3r7To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 22
  | 2 => 13
  | 3 => 1
  | 4 => 4
  | 5 => 10
  | 6 => 6
  | 7 => 8
  | 8 => 7
  | 9 => 2
  | 10 => 11
  | 11 => 17
  | 12 => 20
  | 13 => 19
  | 14 => 3
  | 15 => 12
  | 16 => 15
  | 17 => 5
  | 18 => 23
  | 19 => 9
  | 20 => 16
  | 21 => 21
  | 22 => 14
  | 23 => 18
  | _ => 0

def l3r7Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 9
  | 3 => 14
  | 4 => 4
  | 5 => 17
  | 6 => 6
  | 7 => 8
  | 8 => 7
  | 9 => 19
  | 10 => 5
  | 11 => 10
  | 12 => 15
  | 13 => 2
  | 14 => 22
  | 15 => 16
  | 16 => 20
  | 17 => 11
  | 18 => 23
  | 19 => 13
  | 20 => 12
  | 21 => 21
  | 22 => 1
  | 23 => 18
  | _ => 0

theorem l3r7_left : ∀ x, l3r7Inv (l3r7To x) = x := by decide +kernel
def l3r7 : Equiv.Perm (Fin 24) :=
  tablePerm l3r7To l3r7Inv l3r7_left
    (rightInverse_of_leftInverse_fin l3r7_left)

def l3r8To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 2
  | 2 => 23
  | 3 => 13
  | 4 => 4
  | 5 => 10
  | 6 => 6
  | 7 => 18
  | 8 => 14
  | 9 => 22
  | 10 => 21
  | 11 => 11
  | 12 => 16
  | 13 => 3
  | 14 => 8
  | 15 => 5
  | 16 => 17
  | 17 => 20
  | 18 => 9
  | 19 => 1
  | 20 => 12
  | 21 => 15
  | 22 => 7
  | 23 => 19
  | _ => 0

def l3r8Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 19
  | 2 => 1
  | 3 => 13
  | 4 => 4
  | 5 => 15
  | 6 => 6
  | 7 => 22
  | 8 => 14
  | 9 => 18
  | 10 => 5
  | 11 => 11
  | 12 => 20
  | 13 => 3
  | 14 => 8
  | 15 => 21
  | 16 => 12
  | 17 => 16
  | 18 => 7
  | 19 => 23
  | 20 => 17
  | 21 => 10
  | 22 => 9
  | 23 => 2
  | _ => 0

theorem l3r8_left : ∀ x, l3r8Inv (l3r8To x) = x := by decide +kernel
def l3r8 : Equiv.Perm (Fin 24) :=
  tablePerm l3r8To l3r8Inv l3r8_left
    (rightInverse_of_leftInverse_fin l3r8_left)

def rep3 : Fin 9 → Equiv.Perm (Fin 24)
  | 0 => l3r0
  | 1 => l3r1
  | 2 => l3r2
  | 3 => l3r3
  | 4 => l3r4
  | 5 => l3r5
  | 6 => l3r6
  | 7 => l3r7
  | 8 => l3r8
  | _ => l3r0

def rep3Word : Fin 9 → List (Fin 8)
  | 0 => []
  | 1 => [0]
  | 2 => [1, 0]
  | 3 => [2, 0]
  | 4 => [3, 0]
  | 5 => [6, 0]
  | 6 => [7, 0]
  | 7 => [0, 2, 0]
  | 8 => [3, 2, 0]
  | _ => []

theorem rep3_eq_word : ∀ r, rep3 r = evalWord gen3 (rep3Word r) := by decide +kernel

def point3 : Fin 9 → Fin 24
  | 0 => 15
  | 1 => 21
  | 2 => 20
  | 3 => 10
  | 4 => 17
  | 5 => 11
  | 6 => 16
  | 7 => 12
  | 8 => 5
  | _ => 15

def pointInv3 : Fin 24 → Fin 9
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 8
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 3
  | 11 => 5
  | 12 => 7
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 6
  | 17 => 4
  | 18 => 0
  | 19 => 0
  | 20 => 2
  | 21 => 1
  | 22 => 0
  | 23 => 0
  | _ => 0

theorem point3_injective : Function.Injective point3 := by
  have h : ∀ r, pointInv3 (point3 r) = r := by decide +kernel
  exact Function.LeftInverse.injective h

def act3 : Fin 8 → Fin 9 → Fin 9
  | 0 => ![1, 0, 2, 7, 8, 6, 5, 3, 4]
  | 1 => ![0, 2, 1, 5, 6, 3, 4, 8, 7]
  | 2 => ![0, 3, 5, 2, 7, 1, 8, 6, 4]
  | 3 => ![0, 4, 6, 8, 2, 7, 1, 3, 5]
  | 4 => ![1, 0, 2, 7, 8, 6, 5, 3, 4]
  | 5 => ![0, 2, 1, 5, 6, 3, 4, 8, 7]
  | 6 => ![0, 5, 3, 1, 8, 2, 7, 4, 6]
  | 7 => ![0, 6, 4, 7, 1, 8, 2, 5, 3]
  | _ => ![1, 0, 2, 7, 8, 6, 5, 3, 4]

def factor3 : Fin 8 → Fin 9 → List (Fin 6)
  | 0, 0 => []
  | 0, 1 => []
  | 0, 2 => [0]
  | 0, 3 => []
  | 0, 4 => [1]
  | 0, 5 => [2, 1]
  | 0, 6 => [5, 1]
  | 0, 7 => []
  | 0, 8 => [4]
  | 1, 0 => [0]
  | 1, 1 => []
  | 1, 2 => []
  | 1, 3 => []
  | 1, 4 => []
  | 1, 5 => []
  | 1, 6 => []
  | 1, 7 => [2]
  | 1, 8 => [5]
  | 2, 0 => [1]
  | 2, 1 => []
  | 2, 2 => []
  | 2, 3 => []
  | 2, 4 => [5]
  | 2, 5 => []
  | 2, 6 => []
  | 2, 7 => [2]
  | 2, 8 => []
  | 3, 0 => [2]
  | 3, 1 => []
  | 3, 2 => []
  | 3, 3 => []
  | 3, 4 => []
  | 3, 5 => [5]
  | 3, 6 => []
  | 3, 7 => [2]
  | 3, 8 => []
  | 4, 0 => []
  | 4, 1 => []
  | 4, 2 => [0]
  | 4, 3 => []
  | 4, 4 => [1]
  | 4, 5 => [2, 1]
  | 4, 6 => [5, 1]
  | 4, 7 => []
  | 4, 8 => [4]
  | 5, 0 => [0]
  | 5, 1 => []
  | 5, 2 => []
  | 5, 3 => []
  | 5, 4 => []
  | 5, 5 => []
  | 5, 6 => []
  | 5, 7 => [2]
  | 5, 8 => [5]
  | 6, 0 => [4]
  | 6, 1 => []
  | 6, 2 => []
  | 6, 3 => []
  | 6, 4 => []
  | 6, 5 => []
  | 6, 6 => [5]
  | 6, 7 => [2]
  | 6, 8 => []
  | 7, 0 => [5]
  | 7, 1 => []
  | 7, 2 => []
  | 7, 3 => [5]
  | 7, 4 => []
  | 7, 5 => []
  | 7, 6 => []
  | 7, 7 => [2]
  | 7, 8 => []
  | _, _ => []

theorem rep3_base : rep3 0 = 1 := rfl

theorem rep3_point : ∀ r, rep3 r 15 = point3 r := by decide +kernel

theorem next3_fix : ∀ i, gen4 i 15 = 15 := by decide +kernel

theorem step3 : ∀ i r,
    gen3 i * rep3 r = rep3 (act3 i r) * evalWord gen4 (factor3 i r) := by decide +kernel

theorem card3 :
    Nat.card (wordSubgroup gen3 inv3 inv3_spec) =
      9 * Nat.card (wordSubgroup gen4 inv4 inv4_spec) :=
  wordSubgroup_card_eq_mul_next
    gen3 inv3 inv3_spec gen4 inv4 inv4_spec
    rep3 act3 factor3 15 point3 0
    (fun r => by rw [rep3_eq_word r]; exact evalWord_mem_wordSubgroup _ _ _ _)
    (wordSubgroup_le_of_gen_mem
      (fun i => by rw [gen4_eq_word i]; exact evalWord_mem_wordSubgroup _ _ _ _))
    rep3_base rep3_point point3_injective
    (wordSubgroup_fix_of_gen_fix _ _ _ next3_fix) step3

def l4r0 : Equiv.Perm (Fin 24) := 1

def l4r1To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 23
  | 2 => 8
  | 3 => 22
  | 4 => 4
  | 5 => 12
  | 6 => 6
  | 7 => 13
  | 8 => 2
  | 9 => 9
  | 10 => 11
  | 11 => 10
  | 12 => 5
  | 13 => 7
  | 14 => 14
  | 15 => 15
  | 16 => 17
  | 17 => 16
  | 18 => 18
  | 19 => 19
  | 20 => 21
  | 21 => 20
  | 22 => 3
  | 23 => 1
  | _ => 0

def l4r1Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 23
  | 2 => 8
  | 3 => 22
  | 4 => 4
  | 5 => 12
  | 6 => 6
  | 7 => 13
  | 8 => 2
  | 9 => 9
  | 10 => 11
  | 11 => 10
  | 12 => 5
  | 13 => 7
  | 14 => 14
  | 15 => 15
  | 16 => 17
  | 17 => 16
  | 18 => 18
  | 19 => 19
  | 20 => 21
  | 21 => 20
  | 22 => 3
  | 23 => 1
  | _ => 0

theorem l4r1_left : ∀ x, l4r1Inv (l4r1To x) = x := by decide +kernel
def l4r1 : Equiv.Perm (Fin 24) :=
  tablePerm l4r1To l4r1Inv l4r1_left
    (rightInverse_of_leftInverse_fin l4r1_left)

def l4r2To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 13
  | 3 => 23
  | 4 => 4
  | 5 => 17
  | 6 => 6
  | 7 => 2
  | 8 => 7
  | 9 => 19
  | 10 => 20
  | 11 => 21
  | 12 => 16
  | 13 => 8
  | 14 => 18
  | 15 => 15
  | 16 => 5
  | 17 => 12
  | 18 => 14
  | 19 => 9
  | 20 => 11
  | 21 => 10
  | 22 => 1
  | 23 => 22
  | _ => 0

def l4r2Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 22
  | 2 => 7
  | 3 => 1
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 8
  | 8 => 13
  | 9 => 19
  | 10 => 21
  | 11 => 20
  | 12 => 17
  | 13 => 2
  | 14 => 18
  | 15 => 15
  | 16 => 12
  | 17 => 5
  | 18 => 14
  | 19 => 9
  | 20 => 10
  | 21 => 11
  | 22 => 23
  | 23 => 3
  | _ => 0

theorem l4r2_left : ∀ x, l4r2Inv (l4r2To x) = x := by decide +kernel
def l4r2 : Equiv.Perm (Fin 24) :=
  tablePerm l4r2To l4r2Inv l4r2_left
    (rightInverse_of_leftInverse_fin l4r2_left)

def l4r3To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 13
  | 2 => 22
  | 3 => 2
  | 4 => 4
  | 5 => 11
  | 6 => 6
  | 7 => 1
  | 8 => 3
  | 9 => 14
  | 10 => 5
  | 11 => 12
  | 12 => 10
  | 13 => 23
  | 14 => 9
  | 15 => 15
  | 16 => 21
  | 17 => 20
  | 18 => 19
  | 19 => 18
  | 20 => 16
  | 21 => 17
  | 22 => 8
  | 23 => 7
  | _ => 0

def l4r3Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 7
  | 2 => 3
  | 3 => 8
  | 4 => 4
  | 5 => 10
  | 6 => 6
  | 7 => 23
  | 8 => 22
  | 9 => 14
  | 10 => 12
  | 11 => 5
  | 12 => 11
  | 13 => 1
  | 14 => 9
  | 15 => 15
  | 16 => 20
  | 17 => 21
  | 18 => 19
  | 19 => 18
  | 20 => 17
  | 21 => 16
  | 22 => 2
  | 23 => 13
  | _ => 0

theorem l4r3_left : ∀ x, l4r3Inv (l4r3To x) = x := by decide +kernel
def l4r3 : Equiv.Perm (Fin 24) :=
  tablePerm l4r3To l4r3Inv l4r3_left
    (rightInverse_of_leftInverse_fin l4r3_left)

def l4r4To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 22
  | 2 => 7
  | 3 => 1
  | 4 => 4
  | 5 => 16
  | 6 => 6
  | 7 => 8
  | 8 => 13
  | 9 => 19
  | 10 => 21
  | 11 => 20
  | 12 => 17
  | 13 => 2
  | 14 => 18
  | 15 => 15
  | 16 => 12
  | 17 => 5
  | 18 => 14
  | 19 => 9
  | 20 => 10
  | 21 => 11
  | 22 => 23
  | 23 => 3
  | _ => 0

def l4r4Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 3
  | 2 => 13
  | 3 => 23
  | 4 => 4
  | 5 => 17
  | 6 => 6
  | 7 => 2
  | 8 => 7
  | 9 => 19
  | 10 => 20
  | 11 => 21
  | 12 => 16
  | 13 => 8
  | 14 => 18
  | 15 => 15
  | 16 => 5
  | 17 => 12
  | 18 => 14
  | 19 => 9
  | 20 => 11
  | 21 => 10
  | 22 => 1
  | 23 => 22
  | _ => 0

theorem l4r4_left : ∀ x, l4r4Inv (l4r4To x) = x := by decide +kernel
def l4r4 : Equiv.Perm (Fin 24) :=
  tablePerm l4r4To l4r4Inv l4r4_left
    (rightInverse_of_leftInverse_fin l4r4_left)

def l4r5To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 7
  | 2 => 3
  | 3 => 8
  | 4 => 4
  | 5 => 10
  | 6 => 6
  | 7 => 23
  | 8 => 22
  | 9 => 14
  | 10 => 12
  | 11 => 5
  | 12 => 11
  | 13 => 1
  | 14 => 9
  | 15 => 15
  | 16 => 20
  | 17 => 21
  | 18 => 19
  | 19 => 18
  | 20 => 17
  | 21 => 16
  | 22 => 2
  | 23 => 13
  | _ => 0

def l4r5Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 13
  | 2 => 22
  | 3 => 2
  | 4 => 4
  | 5 => 11
  | 6 => 6
  | 7 => 1
  | 8 => 3
  | 9 => 14
  | 10 => 5
  | 11 => 12
  | 12 => 10
  | 13 => 23
  | 14 => 9
  | 15 => 15
  | 16 => 21
  | 17 => 20
  | 18 => 19
  | 19 => 18
  | 20 => 16
  | 21 => 17
  | 22 => 8
  | 23 => 7
  | _ => 0

theorem l4r5_left : ∀ x, l4r5Inv (l4r5To x) = x := by decide +kernel
def l4r5 : Equiv.Perm (Fin 24) :=
  tablePerm l4r5To l4r5Inv l4r5_left
    (rightInverse_of_leftInverse_fin l4r5_left)

def l4r6To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 2
  | 2 => 23
  | 3 => 7
  | 4 => 4
  | 5 => 20
  | 6 => 6
  | 7 => 22
  | 8 => 1
  | 9 => 18
  | 10 => 16
  | 11 => 17
  | 12 => 21
  | 13 => 3
  | 14 => 19
  | 15 => 15
  | 16 => 11
  | 17 => 10
  | 18 => 9
  | 19 => 14
  | 20 => 12
  | 21 => 5
  | 22 => 13
  | 23 => 8
  | _ => 0

def l4r6Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 8
  | 2 => 1
  | 3 => 13
  | 4 => 4
  | 5 => 21
  | 6 => 6
  | 7 => 3
  | 8 => 23
  | 9 => 18
  | 10 => 17
  | 11 => 16
  | 12 => 20
  | 13 => 22
  | 14 => 19
  | 15 => 15
  | 16 => 10
  | 17 => 11
  | 18 => 9
  | 19 => 14
  | 20 => 5
  | 21 => 12
  | 22 => 7
  | 23 => 2
  | _ => 0

theorem l4r6_left : ∀ x, l4r6Inv (l4r6To x) = x := by decide +kernel
def l4r6 : Equiv.Perm (Fin 24) :=
  tablePerm l4r6To l4r6Inv l4r6_left
    (rightInverse_of_leftInverse_fin l4r6_left)

def l4r7To : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 8
  | 2 => 1
  | 3 => 13
  | 4 => 4
  | 5 => 21
  | 6 => 6
  | 7 => 3
  | 8 => 23
  | 9 => 18
  | 10 => 17
  | 11 => 16
  | 12 => 20
  | 13 => 22
  | 14 => 19
  | 15 => 15
  | 16 => 10
  | 17 => 11
  | 18 => 9
  | 19 => 14
  | 20 => 5
  | 21 => 12
  | 22 => 7
  | 23 => 2
  | _ => 0

def l4r7Inv : Fin 24 → Fin 24
  | 0 => 0
  | 1 => 2
  | 2 => 23
  | 3 => 7
  | 4 => 4
  | 5 => 20
  | 6 => 6
  | 7 => 22
  | 8 => 1
  | 9 => 18
  | 10 => 16
  | 11 => 17
  | 12 => 21
  | 13 => 3
  | 14 => 19
  | 15 => 15
  | 16 => 11
  | 17 => 10
  | 18 => 9
  | 19 => 14
  | 20 => 12
  | 21 => 5
  | 22 => 13
  | 23 => 8
  | _ => 0

theorem l4r7_left : ∀ x, l4r7Inv (l4r7To x) = x := by decide +kernel
def l4r7 : Equiv.Perm (Fin 24) :=
  tablePerm l4r7To l4r7Inv l4r7_left
    (rightInverse_of_leftInverse_fin l4r7_left)

def rep4 : Fin 8 → Equiv.Perm (Fin 24)
  | 0 => l4r0
  | 1 => l4r1
  | 2 => l4r2
  | 3 => l4r3
  | 4 => l4r4
  | 5 => l4r5
  | 6 => l4r6
  | 7 => l4r7
  | _ => l4r0

def rep4Word : Fin 8 → List (Fin 6)
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [2]
  | 4 => [4]
  | 5 => [5]
  | 6 => [2, 1]
  | 7 => [5, 1]
  | _ => []

theorem rep4_eq_word : ∀ r, rep4 r = evalWord gen4 (rep4Word r) := by decide +kernel

def point4 : Fin 8 → Fin 24
  | 0 => 11
  | 1 => 10
  | 2 => 21
  | 3 => 12
  | 4 => 20
  | 5 => 5
  | 6 => 17
  | 7 => 16
  | _ => 11

def pointInv4 : Fin 24 → Fin 8
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 5
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => 0
  | 12 => 3
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 7
  | 17 => 6
  | 18 => 0
  | 19 => 0
  | 20 => 4
  | 21 => 2
  | 22 => 0
  | 23 => 0
  | _ => 0

theorem point4_injective : Function.Injective point4 := by
  have h : ∀ r, pointInv4 (point4 r) = r := by decide +kernel
  exact Function.LeftInverse.injective h

def act4 : Fin 6 → Fin 8 → Fin 8
  | 0 => ![1, 0, 4, 5, 2, 3, 7, 6]
  | 1 => ![2, 4, 1, 7, 0, 6, 3, 5]
  | 2 => ![3, 5, 6, 1, 7, 0, 4, 2]
  | 3 => ![1, 0, 4, 5, 2, 3, 7, 6]
  | 4 => ![4, 2, 0, 6, 1, 7, 5, 3]
  | 5 => ![5, 3, 7, 0, 6, 1, 2, 4]
  | _ => ![1, 0, 4, 5, 2, 3, 7, 6]

def factor4 : Fin 6 → Fin 8 → List (Fin 0)
  | 0, 0 => []
  | 0, 1 => []
  | 0, 2 => []
  | 0, 3 => []
  | 0, 4 => []
  | 0, 5 => []
  | 0, 6 => []
  | 0, 7 => []
  | 1, 0 => []
  | 1, 1 => []
  | 1, 2 => []
  | 1, 3 => []
  | 1, 4 => []
  | 1, 5 => []
  | 1, 6 => []
  | 1, 7 => []
  | 2, 0 => []
  | 2, 1 => []
  | 2, 2 => []
  | 2, 3 => []
  | 2, 4 => []
  | 2, 5 => []
  | 2, 6 => []
  | 2, 7 => []
  | 3, 0 => []
  | 3, 1 => []
  | 3, 2 => []
  | 3, 3 => []
  | 3, 4 => []
  | 3, 5 => []
  | 3, 6 => []
  | 3, 7 => []
  | 4, 0 => []
  | 4, 1 => []
  | 4, 2 => []
  | 4, 3 => []
  | 4, 4 => []
  | 4, 5 => []
  | 4, 6 => []
  | 4, 7 => []
  | 5, 0 => []
  | 5, 1 => []
  | 5, 2 => []
  | 5, 3 => []
  | 5, 4 => []
  | 5, 5 => []
  | 5, 6 => []
  | 5, 7 => []
  | _, _ => []

theorem rep4_base : rep4 0 = 1 := rfl

theorem rep4_point : ∀ r, rep4 r 11 = point4 r := by decide +kernel

theorem next4_fix : ∀ i, gen5 i 11 = 11 := fun i => Fin.elim0 i

theorem step4 : ∀ i r,
    gen4 i * rep4 r = rep4 (act4 i r) * evalWord gen5 (factor4 i r) := by decide +kernel

theorem card4 :
    Nat.card (wordSubgroup gen4 inv4 inv4_spec) =
      8 * Nat.card (wordSubgroup gen5 inv5 inv5_spec) :=
  wordSubgroup_card_eq_mul_next
    gen4 inv4 inv4_spec gen5 inv5 inv5_spec
    rep4 act4 factor4 11 point4 0
    (fun r => by rw [rep4_eq_word r]; exact evalWord_mem_wordSubgroup _ _ _ _)
    (wordSubgroup_le_of_gen_mem
      (fun i => Fin.elim0 i))
    rep4_base rep4_point point4_injective
    (wordSubgroup_fix_of_gen_fix _ _ _ next4_fix) step4

theorem generated_order : Nat.card (wordSubgroup gen0 inv0 inv0_spec) = 190080 := by
  rw [card0, card1, card2, card3, card4, wordSubgroup_fin_zero_card]

theorem generatorA_eq : generatorA = gen0 0 := by decide +kernel
theorem generatorB_eq : generatorB = gen0 1 := by decide +kernel

theorem group_le : group ≤ wordSubgroup gen0 inv0 inv0_spec := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | hg
  · exact ⟨[0], by simpa only [evalWord, mul_one] using generatorA_eq.symm⟩
  · have hg' : g = generatorB := Set.mem_singleton_iff.mp hg
    subst g
    exact ⟨[1], by simpa only [evalWord, mul_one] using generatorB_eq.symm⟩

end OrderBoundCertificate

/-- The literal degree-24 ATLAS carrier has order at most 190080. -/
public theorem carrier_order_le : Nat.card Carrier ≤ 190080 := by
  calc
    Nat.card Carrier ≤ Nat.card (Theory.GroupTheory.wordSubgroup
        OrderBoundCertificate.gen0 OrderBoundCertificate.inv0
        OrderBoundCertificate.inv0_spec) :=
      Nat.card_le_card_of_injective
        (Subgroup.inclusion OrderBoundCertificate.group_le)
        (Subgroup.inclusion_injective OrderBoundCertificate.group_le)
    _ = 190080 := OrderBoundCertificate.generated_order

end Sporadic.Mathieu.M12ExceptionalExtension
