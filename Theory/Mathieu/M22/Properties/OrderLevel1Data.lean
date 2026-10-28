module

public import Theory.Mathieu.M22.Properties.OrderCertificate
import Mathlib.Tactic.FinCases

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise
@[reducible, expose]
public def m22L1R0To : Fin 22 -> Fin 22 := id

@[reducible, expose]
public def m22L1R0InvFun : Fin 22 -> Fin 22 := id

public theorem m22L1R0_left : forall x, m22L1R0InvFun (m22L1R0To x) = x := by
  intro x
  rfl

public theorem m22L1R0_right : forall x, m22L1R0To (m22L1R0InvFun x) = x := by
  intro x
  rfl

@[reducible, expose]
public def m22L1R0 : Equiv.Perm (Fin 22) := Equiv.refl _

@[reducible, expose]
public def m22L1R1To : Fin 22 -> Fin 22 :=
  m22L1G1To

@[reducible, expose]
public def m22L1R1InvFun : Fin 22 -> Fin 22 :=
  m22L1G1InvFun

public theorem m22L1R1_left : forall x, m22L1R1InvFun (m22L1R1To x) = x :=
  m22L1G1_left

public theorem m22L1R1_right : forall x, m22L1R1To (m22L1R1InvFun x) = x :=
  m22L1G1_right

@[reducible, expose]
public def m22L1R1 : Equiv.Perm (Fin 22) :=
  m22L1G1

@[reducible, expose]
public def m22L1R2To : Fin 22 -> Fin 22
  | 0 => (2 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (9 : Fin 22)
  | 3 => (13 : Fin 22)
  | 4 => (15 : Fin 22)
  | 5 => (11 : Fin 22)
  | 6 => (5 : Fin 22)
  | 7 => (20 : Fin 22)
  | 8 => (0 : Fin 22)
  | 9 => (17 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (3 : Fin 22)
  | 12 => (16 : Fin 22)
  | 13 => (6 : Fin 22)
  | 14 => (18 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (7 : Fin 22)
  | 17 => (8 : Fin 22)
  | 18 => (19 : Fin 22)
  | 19 => (4 : Fin 22)
  | 20 => (21 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R2InvFun : Fin 22 -> Fin 22
  | 0 => (8 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (0 : Fin 22)
  | 3 => (11 : Fin 22)
  | 4 => (19 : Fin 22)
  | 5 => (6 : Fin 22)
  | 6 => (13 : Fin 22)
  | 7 => (16 : Fin 22)
  | 8 => (17 : Fin 22)
  | 9 => (2 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (5 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (3 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (4 : Fin 22)
  | 16 => (12 : Fin 22)
  | 17 => (9 : Fin 22)
  | 18 => (14 : Fin 22)
  | 19 => (18 : Fin 22)
  | 20 => (7 : Fin 22)
  | 21 => (20 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R2_left : forall x, m22L1R2InvFun (m22L1R2To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R2_right : forall x, m22L1R2To (m22L1R2InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R2_left

@[reducible, expose]
public def m22L1R2 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R2To m22L1R2InvFun m22L1R2_left m22L1R2_right

@[reducible, expose]
public def m22L1R3To : Fin 22 -> Fin 22
  | 0 => (0 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (8 : Fin 22)
  | 3 => (5 : Fin 22)
  | 4 => (19 : Fin 22)
  | 5 => (3 : Fin 22)
  | 6 => (13 : Fin 22)
  | 7 => (7 : Fin 22)
  | 8 => (2 : Fin 22)
  | 9 => (17 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (6 : Fin 22)
  | 14 => (14 : Fin 22)
  | 15 => (18 : Fin 22)
  | 16 => (20 : Fin 22)
  | 17 => (9 : Fin 22)
  | 18 => (15 : Fin 22)
  | 19 => (4 : Fin 22)
  | 20 => (16 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R3InvFun : Fin 22 -> Fin 22
  | 0 => (0 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (8 : Fin 22)
  | 3 => (5 : Fin 22)
  | 4 => (19 : Fin 22)
  | 5 => (3 : Fin 22)
  | 6 => (13 : Fin 22)
  | 7 => (7 : Fin 22)
  | 8 => (2 : Fin 22)
  | 9 => (17 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (6 : Fin 22)
  | 14 => (14 : Fin 22)
  | 15 => (18 : Fin 22)
  | 16 => (20 : Fin 22)
  | 17 => (9 : Fin 22)
  | 18 => (15 : Fin 22)
  | 19 => (4 : Fin 22)
  | 20 => (16 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R3_left : forall x, m22L1R3InvFun (m22L1R3To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R3_right : forall x, m22L1R3To (m22L1R3InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R3_left

@[reducible, expose]
public def m22L1R3 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R3To m22L1R3InvFun m22L1R3_left m22L1R3_right

@[reducible, expose]
public def m22L1R4To : Fin 22 -> Fin 22
  | 0 => (9 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (17 : Fin 22)
  | 3 => (6 : Fin 22)
  | 4 => (14 : Fin 22)
  | 5 => (3 : Fin 22)
  | 6 => (11 : Fin 22)
  | 7 => (21 : Fin 22)
  | 8 => (2 : Fin 22)
  | 9 => (8 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (13 : Fin 22)
  | 12 => (7 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (18 : Fin 22)
  | 16 => (20 : Fin 22)
  | 17 => (0 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (12 : Fin 22)
  | 21 => (16 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R4InvFun : Fin 22 -> Fin 22
  | 0 => (17 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (8 : Fin 22)
  | 3 => (5 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (3 : Fin 22)
  | 7 => (12 : Fin 22)
  | 8 => (9 : Fin 22)
  | 9 => (0 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (6 : Fin 22)
  | 12 => (20 : Fin 22)
  | 13 => (11 : Fin 22)
  | 14 => (4 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (21 : Fin 22)
  | 17 => (2 : Fin 22)
  | 18 => (15 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (16 : Fin 22)
  | 21 => (7 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R4_left : forall x, m22L1R4InvFun (m22L1R4To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R4_right : forall x, m22L1R4To (m22L1R4InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R4_left

@[reducible, expose]
public def m22L1R4 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R4To m22L1R4InvFun m22L1R4_left m22L1R4_right

@[reducible, expose]
public def m22L1R5To : Fin 22 -> Fin 22
  | 0 => (2 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (21 : Fin 22)
  | 3 => (13 : Fin 22)
  | 4 => (20 : Fin 22)
  | 5 => (16 : Fin 22)
  | 6 => (14 : Fin 22)
  | 7 => (8 : Fin 22)
  | 8 => (7 : Fin 22)
  | 9 => (4 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (0 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (6 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (15 : Fin 22)
  | 18 => (19 : Fin 22)
  | 19 => (18 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (11 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R5InvFun : Fin 22 -> Fin 22
  | 0 => (11 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (0 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (9 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (15 : Fin 22)
  | 7 => (8 : Fin 22)
  | 8 => (7 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (21 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (3 : Fin 22)
  | 14 => (6 : Fin 22)
  | 15 => (17 : Fin 22)
  | 16 => (5 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (19 : Fin 22)
  | 19 => (18 : Fin 22)
  | 20 => (4 : Fin 22)
  | 21 => (2 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R5_left : forall x, m22L1R5InvFun (m22L1R5To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R5_right : forall x, m22L1R5To (m22L1R5InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R5_left

@[reducible, expose]
public def m22L1R5 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R5To m22L1R5InvFun m22L1R5_left m22L1R5_right

@[reducible, expose]
public def m22L1R6To : Fin 22 -> Fin 22
  | 0 => (2 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (7 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (5 : Fin 22)
  | 7 => (8 : Fin 22)
  | 8 => (21 : Fin 22)
  | 9 => (15 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (0 : Fin 22)
  | 12 => (11 : Fin 22)
  | 13 => (14 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (10 : Fin 22)
  | 17 => (4 : Fin 22)
  | 18 => (6 : Fin 22)
  | 19 => (20 : Fin 22)
  | 20 => (3 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R6InvFun : Fin 22 -> Fin 22
  | 0 => (11 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (0 : Fin 22)
  | 3 => (20 : Fin 22)
  | 4 => (17 : Fin 22)
  | 5 => (6 : Fin 22)
  | 6 => (18 : Fin 22)
  | 7 => (2 : Fin 22)
  | 8 => (7 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (16 : Fin 22)
  | 11 => (12 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (13 : Fin 22)
  | 15 => (9 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (19 : Fin 22)
  | 21 => (8 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R6_left : forall x, m22L1R6InvFun (m22L1R6To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R6_right : forall x, m22L1R6To (m22L1R6InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R6_left

@[reducible, expose]
public def m22L1R6 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R6To m22L1R6InvFun m22L1R6_left m22L1R6_right

@[reducible, expose]
public def m22L1R7To : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (4 : Fin 22)
  | 3 => (5 : Fin 22)
  | 4 => (6 : Fin 22)
  | 5 => (0 : Fin 22)
  | 6 => (16 : Fin 22)
  | 7 => (10 : Fin 22)
  | 8 => (2 : Fin 22)
  | 9 => (15 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (13 : Fin 22)
  | 12 => (3 : Fin 22)
  | 13 => (14 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (17 : Fin 22)
  | 16 => (8 : Fin 22)
  | 17 => (7 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (20 : Fin 22)
  | 20 => (11 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R7InvFun : Fin 22 -> Fin 22
  | 0 => (5 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (8 : Fin 22)
  | 3 => (12 : Fin 22)
  | 4 => (2 : Fin 22)
  | 5 => (3 : Fin 22)
  | 6 => (4 : Fin 22)
  | 7 => (17 : Fin 22)
  | 8 => (16 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (7 : Fin 22)
  | 11 => (20 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (11 : Fin 22)
  | 14 => (13 : Fin 22)
  | 15 => (9 : Fin 22)
  | 16 => (6 : Fin 22)
  | 17 => (15 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (19 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R7_left : forall x, m22L1R7InvFun (m22L1R7To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R7_right : forall x, m22L1R7To (m22L1R7InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R7_left

@[reducible, expose]
public def m22L1R7 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R7To m22L1R7InvFun m22L1R7_left m22L1R7_right

@[reducible, expose]
public def m22L1R8To : Fin 22 -> Fin 22
  | 0 => (7 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (15 : Fin 22)
  | 3 => (14 : Fin 22)
  | 4 => (19 : Fin 22)
  | 5 => (0 : Fin 22)
  | 6 => (13 : Fin 22)
  | 7 => (3 : Fin 22)
  | 8 => (2 : Fin 22)
  | 9 => (4 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (10 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (6 : Fin 22)
  | 15 => (17 : Fin 22)
  | 16 => (8 : Fin 22)
  | 17 => (21 : Fin 22)
  | 18 => (20 : Fin 22)
  | 19 => (18 : Fin 22)
  | 20 => (12 : Fin 22)
  | 21 => (11 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R8InvFun : Fin 22 -> Fin 22
  | 0 => (5 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (8 : Fin 22)
  | 3 => (7 : Fin 22)
  | 4 => (9 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (14 : Fin 22)
  | 7 => (0 : Fin 22)
  | 8 => (16 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (12 : Fin 22)
  | 11 => (21 : Fin 22)
  | 12 => (20 : Fin 22)
  | 13 => (6 : Fin 22)
  | 14 => (3 : Fin 22)
  | 15 => (2 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (15 : Fin 22)
  | 18 => (19 : Fin 22)
  | 19 => (4 : Fin 22)
  | 20 => (18 : Fin 22)
  | 21 => (17 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R8_left : forall x, m22L1R8InvFun (m22L1R8To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R8_right : forall x, m22L1R8To (m22L1R8InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R8_left

@[reducible, expose]
public def m22L1R8 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R8To m22L1R8InvFun m22L1R8_left m22L1R8_right

@[reducible, expose]
public def m22L1R9To : Fin 22 -> Fin 22
  | 0 => (0 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (16 : Fin 22)
  | 3 => (5 : Fin 22)
  | 4 => (7 : Fin 22)
  | 5 => (21 : Fin 22)
  | 6 => (18 : Fin 22)
  | 7 => (9 : Fin 22)
  | 8 => (20 : Fin 22)
  | 9 => (4 : Fin 22)
  | 10 => (8 : Fin 22)
  | 11 => (2 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (13 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (6 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (15 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R9InvFun : Fin 22 -> Fin 22
  | 0 => (0 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (11 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (9 : Fin 22)
  | 5 => (3 : Fin 22)
  | 6 => (15 : Fin 22)
  | 7 => (4 : Fin 22)
  | 8 => (10 : Fin 22)
  | 9 => (7 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (13 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (18 : Fin 22)
  | 16 => (2 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (6 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (8 : Fin 22)
  | 21 => (5 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R9_left : forall x, m22L1R9InvFun (m22L1R9To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R9_right : forall x, m22L1R9To (m22L1R9InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R9_left

@[reducible, expose]
public def m22L1R9 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R9To m22L1R9InvFun m22L1R9_left m22L1R9_right

@[reducible, expose]
public def m22L1R10To : Fin 22 -> Fin 22
  | 0 => (2 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (3 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (8 : Fin 22)
  | 5 => (11 : Fin 22)
  | 6 => (19 : Fin 22)
  | 7 => (4 : Fin 22)
  | 8 => (10 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (7 : Fin 22)
  | 11 => (21 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (18 : Fin 22)
  | 18 => (6 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (13 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R10InvFun : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (0 : Fin 22)
  | 3 => (2 : Fin 22)
  | 4 => (7 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (18 : Fin 22)
  | 7 => (10 : Fin 22)
  | 8 => (4 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (8 : Fin 22)
  | 11 => (5 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (21 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (17 : Fin 22)
  | 19 => (6 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (11 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R10_left : forall x, m22L1R10InvFun (m22L1R10To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R10_right : forall x, m22L1R10To (m22L1R10InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R10_left

@[reducible, expose]
public def m22L1R10 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R10To m22L1R10InvFun m22L1R10_left m22L1R10_right

@[reducible, expose]
public def m22L1R11To : Fin 22 -> Fin 22
  | 0 => (0 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (20 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (14 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (13 : Fin 22)
  | 7 => (9 : Fin 22)
  | 8 => (16 : Fin 22)
  | 9 => (19 : Fin 22)
  | 10 => (8 : Fin 22)
  | 11 => (2 : Fin 22)
  | 12 => (3 : Fin 22)
  | 13 => (18 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (10 : Fin 22)
  | 17 => (4 : Fin 22)
  | 18 => (6 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (11 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R11InvFun : Fin 22 -> Fin 22
  | 0 => (0 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (11 : Fin 22)
  | 3 => (12 : Fin 22)
  | 4 => (17 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (18 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (10 : Fin 22)
  | 9 => (7 : Fin 22)
  | 10 => (16 : Fin 22)
  | 11 => (20 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (6 : Fin 22)
  | 14 => (4 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (8 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (13 : Fin 22)
  | 19 => (9 : Fin 22)
  | 20 => (2 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R11_left : forall x, m22L1R11InvFun (m22L1R11To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R11_right : forall x, m22L1R11To (m22L1R11InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R11_left

@[reducible, expose]
public def m22L1R11 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R11To m22L1R11InvFun m22L1R11_left m22L1R11_right

@[reducible, expose]
public def m22L1R12To : Fin 22 -> Fin 22
  | 0 => (2 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (10 : Fin 22)
  | 3 => (11 : Fin 22)
  | 4 => (17 : Fin 22)
  | 5 => (16 : Fin 22)
  | 6 => (5 : Fin 22)
  | 7 => (4 : Fin 22)
  | 8 => (3 : Fin 22)
  | 9 => (18 : Fin 22)
  | 10 => (7 : Fin 22)
  | 11 => (21 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (19 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (6 : Fin 22)
  | 16 => (9 : Fin 22)
  | 17 => (20 : Fin 22)
  | 18 => (14 : Fin 22)
  | 19 => (8 : Fin 22)
  | 20 => (0 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R12InvFun : Fin 22 -> Fin 22
  | 0 => (20 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (0 : Fin 22)
  | 3 => (8 : Fin 22)
  | 4 => (7 : Fin 22)
  | 5 => (6 : Fin 22)
  | 6 => (15 : Fin 22)
  | 7 => (10 : Fin 22)
  | 8 => (19 : Fin 22)
  | 9 => (16 : Fin 22)
  | 10 => (2 : Fin 22)
  | 11 => (3 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (18 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (5 : Fin 22)
  | 17 => (4 : Fin 22)
  | 18 => (9 : Fin 22)
  | 19 => (13 : Fin 22)
  | 20 => (17 : Fin 22)
  | 21 => (11 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R12_left : forall x, m22L1R12InvFun (m22L1R12To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R12_right : forall x, m22L1R12To (m22L1R12InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R12_left

@[reducible, expose]
public def m22L1R12 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R12To m22L1R12InvFun m22L1R12_left m22L1R12_right

@[reducible, expose]
public def m22L1R13To : Fin 22 -> Fin 22
  | 0 => (20 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (19 : Fin 22)
  | 3 => (18 : Fin 22)
  | 4 => (15 : Fin 22)
  | 5 => (2 : Fin 22)
  | 6 => (5 : Fin 22)
  | 7 => (11 : Fin 22)
  | 8 => (0 : Fin 22)
  | 9 => (4 : Fin 22)
  | 10 => (8 : Fin 22)
  | 11 => (21 : Fin 22)
  | 12 => (10 : Fin 22)
  | 13 => (13 : Fin 22)
  | 14 => (6 : Fin 22)
  | 15 => (17 : Fin 22)
  | 16 => (9 : Fin 22)
  | 17 => (16 : Fin 22)
  | 18 => (7 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (12 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R13InvFun : Fin 22 -> Fin 22
  | 0 => (8 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (5 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (9 : Fin 22)
  | 5 => (6 : Fin 22)
  | 6 => (14 : Fin 22)
  | 7 => (18 : Fin 22)
  | 8 => (10 : Fin 22)
  | 9 => (16 : Fin 22)
  | 10 => (12 : Fin 22)
  | 11 => (7 : Fin 22)
  | 12 => (20 : Fin 22)
  | 13 => (13 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (4 : Fin 22)
  | 16 => (17 : Fin 22)
  | 17 => (15 : Fin 22)
  | 18 => (3 : Fin 22)
  | 19 => (2 : Fin 22)
  | 20 => (0 : Fin 22)
  | 21 => (11 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R13_left : forall x, m22L1R13InvFun (m22L1R13To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R13_right : forall x, m22L1R13To (m22L1R13InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R13_left

@[reducible, expose]
public def m22L1R13 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R13To m22L1R13InvFun m22L1R13_left m22L1R13_right

@[reducible, expose]
public def m22L1R14To : Fin 22 -> Fin 22
  | 0 => (10 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (18 : Fin 22)
  | 3 => (19 : Fin 22)
  | 4 => (6 : Fin 22)
  | 5 => (21 : Fin 22)
  | 6 => (16 : Fin 22)
  | 7 => (0 : Fin 22)
  | 8 => (2 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (7 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (9 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (14 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (4 : Fin 22)
  | 17 => (3 : Fin 22)
  | 18 => (8 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (12 : Fin 22)
  | 21 => (13 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R14InvFun : Fin 22 -> Fin 22
  | 0 => (7 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (8 : Fin 22)
  | 3 => (17 : Fin 22)
  | 4 => (16 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (4 : Fin 22)
  | 7 => (10 : Fin 22)
  | 8 => (18 : Fin 22)
  | 9 => (12 : Fin 22)
  | 10 => (0 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (20 : Fin 22)
  | 13 => (21 : Fin 22)
  | 14 => (14 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (6 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (2 : Fin 22)
  | 19 => (3 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (5 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R14_left : forall x, m22L1R14InvFun (m22L1R14To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R14_right : forall x, m22L1R14To (m22L1R14InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R14_left

@[reducible, expose]
public def m22L1R14 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R14To m22L1R14InvFun m22L1R14_left m22L1R14_right

@[reducible, expose]
public def m22L1R15To : Fin 22 -> Fin 22
  | 0 => (9 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (12 : Fin 22)
  | 3 => (6 : Fin 22)
  | 4 => (21 : Fin 22)
  | 5 => (7 : Fin 22)
  | 6 => (18 : Fin 22)
  | 7 => (0 : Fin 22)
  | 8 => (20 : Fin 22)
  | 9 => (15 : Fin 22)
  | 10 => (17 : Fin 22)
  | 11 => (2 : Fin 22)
  | 12 => (16 : Fin 22)
  | 13 => (11 : Fin 22)
  | 14 => (8 : Fin 22)
  | 15 => (5 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R15InvFun : Fin 22 -> Fin 22
  | 0 => (7 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (11 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (15 : Fin 22)
  | 6 => (3 : Fin 22)
  | 7 => (5 : Fin 22)
  | 8 => (14 : Fin 22)
  | 9 => (0 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (13 : Fin 22)
  | 12 => (2 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (9 : Fin 22)
  | 16 => (12 : Fin 22)
  | 17 => (10 : Fin 22)
  | 18 => (6 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (8 : Fin 22)
  | 21 => (4 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R15_left : forall x, m22L1R15InvFun (m22L1R15To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R15_right : forall x, m22L1R15To (m22L1R15InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R15_left

@[reducible, expose]
public def m22L1R15 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R15To m22L1R15InvFun m22L1R15_left m22L1R15_right

@[reducible, expose]
public def m22L1R16To : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (11 : Fin 22)
  | 3 => (5 : Fin 22)
  | 4 => (10 : Fin 22)
  | 5 => (3 : Fin 22)
  | 6 => (17 : Fin 22)
  | 7 => (7 : Fin 22)
  | 8 => (8 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (4 : Fin 22)
  | 11 => (2 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (6 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R16InvFun : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (11 : Fin 22)
  | 3 => (5 : Fin 22)
  | 4 => (10 : Fin 22)
  | 5 => (3 : Fin 22)
  | 6 => (17 : Fin 22)
  | 7 => (7 : Fin 22)
  | 8 => (8 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (4 : Fin 22)
  | 11 => (2 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (6 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R16_left : forall x, m22L1R16InvFun (m22L1R16To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R16_right : forall x, m22L1R16To (m22L1R16InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R16_left

@[reducible, expose]
public def m22L1R16 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R16To m22L1R16InvFun m22L1R16_left m22L1R16_right

@[reducible, expose]
public def m22L1R17To : Fin 22 -> Fin 22
  | 0 => (20 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (14 : Fin 22)
  | 3 => (18 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (2 : Fin 22)
  | 6 => (6 : Fin 22)
  | 7 => (13 : Fin 22)
  | 8 => (9 : Fin 22)
  | 9 => (15 : Fin 22)
  | 10 => (17 : Fin 22)
  | 11 => (7 : Fin 22)
  | 12 => (10 : Fin 22)
  | 13 => (11 : Fin 22)
  | 14 => (5 : Fin 22)
  | 15 => (8 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (12 : Fin 22)
  | 18 => (21 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (16 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R17InvFun : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (5 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (14 : Fin 22)
  | 6 => (6 : Fin 22)
  | 7 => (11 : Fin 22)
  | 8 => (15 : Fin 22)
  | 9 => (8 : Fin 22)
  | 10 => (12 : Fin 22)
  | 11 => (13 : Fin 22)
  | 12 => (17 : Fin 22)
  | 13 => (7 : Fin 22)
  | 14 => (2 : Fin 22)
  | 15 => (9 : Fin 22)
  | 16 => (20 : Fin 22)
  | 17 => (10 : Fin 22)
  | 18 => (3 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (0 : Fin 22)
  | 21 => (18 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R17_left : forall x, m22L1R17InvFun (m22L1R17To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R17_right : forall x, m22L1R17To (m22L1R17InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R17_left

@[reducible, expose]
public def m22L1R17 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R17To m22L1R17InvFun m22L1R17_left m22L1R17_right

@[reducible, expose]
public def m22L1R18To : Fin 22 -> Fin 22
  | 0 => (8 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (6 : Fin 22)
  | 3 => (17 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (2 : Fin 22)
  | 6 => (5 : Fin 22)
  | 7 => (13 : Fin 22)
  | 8 => (21 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (4 : Fin 22)
  | 11 => (3 : Fin 22)
  | 12 => (9 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (14 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (7 : Fin 22)
  | 17 => (11 : Fin 22)
  | 18 => (10 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (12 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R18InvFun : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (5 : Fin 22)
  | 3 => (11 : Fin 22)
  | 4 => (10 : Fin 22)
  | 5 => (6 : Fin 22)
  | 6 => (2 : Fin 22)
  | 7 => (16 : Fin 22)
  | 8 => (0 : Fin 22)
  | 9 => (12 : Fin 22)
  | 10 => (18 : Fin 22)
  | 11 => (17 : Fin 22)
  | 12 => (20 : Fin 22)
  | 13 => (7 : Fin 22)
  | 14 => (14 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (3 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (8 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R18_left : forall x, m22L1R18InvFun (m22L1R18To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R18_right : forall x, m22L1R18To (m22L1R18InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R18_left

@[reducible, expose]
public def m22L1R18 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R18To m22L1R18InvFun m22L1R18_left m22L1R18_right

@[reducible, expose]
public def m22L1R19To : Fin 22 -> Fin 22
  | 0 => (7 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (13 : Fin 22)
  | 3 => (6 : Fin 22)
  | 4 => (10 : Fin 22)
  | 5 => (3 : Fin 22)
  | 6 => (8 : Fin 22)
  | 7 => (21 : Fin 22)
  | 8 => (17 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (15 : Fin 22)
  | 11 => (2 : Fin 22)
  | 12 => (16 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (4 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (5 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (0 : Fin 22)
  | 21 => (9 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R19InvFun : Fin 22 -> Fin 22
  | 0 => (20 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (11 : Fin 22)
  | 3 => (5 : Fin 22)
  | 4 => (14 : Fin 22)
  | 5 => (17 : Fin 22)
  | 6 => (3 : Fin 22)
  | 7 => (0 : Fin 22)
  | 8 => (6 : Fin 22)
  | 9 => (21 : Fin 22)
  | 10 => (4 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (2 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (10 : Fin 22)
  | 16 => (12 : Fin 22)
  | 17 => (8 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (7 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R19_left : forall x, m22L1R19InvFun (m22L1R19To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R19_right : forall x, m22L1R19To (m22L1R19InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R19_left

@[reducible, expose]
public def m22L1R19 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R19To m22L1R19InvFun m22L1R19_left m22L1R19_right

@[reducible, expose]
public def m22L1R20To : Fin 22 -> Fin 22
  | 0 => (20 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (5 : Fin 22)
  | 3 => (6 : Fin 22)
  | 4 => (10 : Fin 22)
  | 5 => (11 : Fin 22)
  | 6 => (9 : Fin 22)
  | 7 => (16 : Fin 22)
  | 8 => (17 : Fin 22)
  | 9 => (7 : Fin 22)
  | 10 => (19 : Fin 22)
  | 11 => (0 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (4 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (13 : Fin 22)
  | 18 => (14 : Fin 22)
  | 19 => (18 : Fin 22)
  | 20 => (2 : Fin 22)
  | 21 => (8 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L1R20InvFun : Fin 22 -> Fin 22
  | 0 => (11 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (20 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (14 : Fin 22)
  | 5 => (2 : Fin 22)
  | 6 => (3 : Fin 22)
  | 7 => (9 : Fin 22)
  | 8 => (21 : Fin 22)
  | 9 => (6 : Fin 22)
  | 10 => (4 : Fin 22)
  | 11 => (5 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (17 : Fin 22)
  | 14 => (18 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (7 : Fin 22)
  | 17 => (8 : Fin 22)
  | 18 => (19 : Fin 22)
  | 19 => (10 : Fin 22)
  | 20 => (0 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1R20_left : forall x, m22L1R20InvFun (m22L1R20To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1R20_right : forall x, m22L1R20To (m22L1R20InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1R20_left

@[reducible, expose]
public def m22L1R20 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1R20To m22L1R20InvFun m22L1R20_left m22L1R20_right

@[reducible, expose]
public def m22L1RepWord : Fin 21 -> List (Fin 6)
  | 0 => []
  | 1 => [(1 : Fin 6)]
  | 2 => [(0 : Fin 6), (1 : Fin 6)]
  | 3 => [(1 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 4 => [(0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 5 => [(5 : Fin 6), (1 : Fin 6)]
  | 6 => [(5 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 7 => [(5 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 8 => [(5 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 9 => [(1 : Fin 6), (5 : Fin 6), (1 : Fin 6)]
  | 10 => [(2 : Fin 6), (1 : Fin 6)]
  | 11 => [(1 : Fin 6), (5 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 12 => [(2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 13 => [(1 : Fin 6), (5 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 14 => [(2 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 15 => [(0 : Fin 6), (1 : Fin 6), (5 : Fin 6), (1 : Fin 6)]
  | 16 => [(1 : Fin 6), (2 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | 17 => [(0 : Fin 6), (1 : Fin 6), (5 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 18 => [(5 : Fin 6), (1 : Fin 6), (5 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 19 => [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | 20 => [(1 : Fin 6), (0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | _ => []

@[reducible, expose]
public def m22L1Rep : Fin 21 -> Equiv.Perm (Fin 22)
  | 0 => m22L1R0
  | 1 => m22L1R1
  | 2 => m22L1R2
  | 3 => m22L1R3
  | 4 => m22L1R4
  | 5 => m22L1R5
  | 6 => m22L1R6
  | 7 => m22L1R7
  | 8 => m22L1R8
  | 9 => m22L1R9
  | 10 => m22L1R10
  | 11 => m22L1R11
  | 12 => m22L1R12
  | 13 => m22L1R13
  | 14 => m22L1R14
  | 15 => m22L1R15
  | 16 => m22L1R16
  | 17 => m22L1R17
  | 18 => m22L1R18
  | 19 => m22L1R19
  | 20 => m22L1R20
  | _ => m22L1R0

public theorem m22L1Rep_eq_word : (r : Fin 21) -> m22L1Rep r = evalWord m22L1Gen (m22L1RepWord r) := by
  intro r
  fin_cases r <;> apply Equiv.ext <;> intro x <;> fin_cases x <;> rfl

@[reducible, expose]
public def m22L1Point : Fin 21 -> Fin 22
  | 0 => (2 : Fin 22)
  | 1 => (0 : Fin 22)
  | 2 => (9 : Fin 22)
  | 3 => (8 : Fin 22)
  | 4 => (17 : Fin 22)
  | 5 => (21 : Fin 22)
  | 6 => (7 : Fin 22)
  | 7 => (4 : Fin 22)
  | 8 => (15 : Fin 22)
  | 9 => (16 : Fin 22)
  | 10 => (3 : Fin 22)
  | 11 => (20 : Fin 22)
  | 12 => (10 : Fin 22)
  | 13 => (19 : Fin 22)
  | 14 => (18 : Fin 22)
  | 15 => (12 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (6 : Fin 22)
  | 19 => (13 : Fin 22)
  | 20 => (5 : Fin 22)
  | _ => (2 : Fin 22)

@[reducible, expose]
public def m22L1Act : Fin 6 -> Fin 21 -> Fin 21
  | 0, 0 => (0 : Fin 21)
  | 0, 1 => (2 : Fin 21)
  | 0, 2 => (1 : Fin 21)
  | 0, 3 => (4 : Fin 21)
  | 0, 4 => (3 : Fin 21)
  | 0, 5 => (6 : Fin 21)
  | 0, 6 => (5 : Fin 21)
  | 0, 7 => (8 : Fin 21)
  | 0, 8 => (7 : Fin 21)
  | 0, 9 => (15 : Fin 21)
  | 0, 10 => (10 : Fin 21)
  | 0, 11 => (11 : Fin 21)
  | 0, 12 => (12 : Fin 21)
  | 0, 13 => (17 : Fin 21)
  | 0, 14 => (14 : Fin 21)
  | 0, 15 => (9 : Fin 21)
  | 0, 16 => (19 : Fin 21)
  | 0, 17 => (13 : Fin 21)
  | 0, 18 => (20 : Fin 21)
  | 0, 19 => (16 : Fin 21)
  | 0, 20 => (18 : Fin 21)
  | 1, 0 => (1 : Fin 21)
  | 1, 1 => (0 : Fin 21)
  | 1, 2 => (3 : Fin 21)
  | 1, 3 => (2 : Fin 21)
  | 1, 4 => (4 : Fin 21)
  | 1, 5 => (9 : Fin 21)
  | 1, 6 => (11 : Fin 21)
  | 1, 7 => (7 : Fin 21)
  | 1, 8 => (13 : Fin 21)
  | 1, 9 => (5 : Fin 21)
  | 1, 10 => (16 : Fin 21)
  | 1, 11 => (6 : Fin 21)
  | 1, 12 => (12 : Fin 21)
  | 1, 13 => (8 : Fin 21)
  | 1, 14 => (17 : Fin 21)
  | 1, 15 => (15 : Fin 21)
  | 1, 16 => (10 : Fin 21)
  | 1, 17 => (14 : Fin 21)
  | 1, 18 => (18 : Fin 21)
  | 1, 19 => (20 : Fin 21)
  | 1, 20 => (19 : Fin 21)
  | 2, 0 => (0 : Fin 21)
  | 2, 1 => (10 : Fin 21)
  | 2, 2 => (12 : Fin 21)
  | 2, 3 => (11 : Fin 21)
  | 2, 4 => (14 : Fin 21)
  | 2, 5 => (1 : Fin 21)
  | 2, 6 => (2 : Fin 21)
  | 2, 7 => (3 : Fin 21)
  | 2, 8 => (4 : Fin 21)
  | 2, 9 => (19 : Fin 21)
  | 2, 10 => (5 : Fin 21)
  | 2, 11 => (7 : Fin 21)
  | 2, 12 => (6 : Fin 21)
  | 2, 13 => (17 : Fin 21)
  | 2, 14 => (8 : Fin 21)
  | 2, 15 => (15 : Fin 21)
  | 2, 16 => (9 : Fin 21)
  | 2, 17 => (18 : Fin 21)
  | 2, 18 => (13 : Fin 21)
  | 2, 19 => (16 : Fin 21)
  | 2, 20 => (20 : Fin 21)
  | 3, 0 => (0 : Fin 21)
  | 3, 1 => (2 : Fin 21)
  | 3, 2 => (1 : Fin 21)
  | 3, 3 => (4 : Fin 21)
  | 3, 4 => (3 : Fin 21)
  | 3, 5 => (6 : Fin 21)
  | 3, 6 => (5 : Fin 21)
  | 3, 7 => (8 : Fin 21)
  | 3, 8 => (7 : Fin 21)
  | 3, 9 => (15 : Fin 21)
  | 3, 10 => (10 : Fin 21)
  | 3, 11 => (11 : Fin 21)
  | 3, 12 => (12 : Fin 21)
  | 3, 13 => (17 : Fin 21)
  | 3, 14 => (14 : Fin 21)
  | 3, 15 => (9 : Fin 21)
  | 3, 16 => (19 : Fin 21)
  | 3, 17 => (13 : Fin 21)
  | 3, 18 => (20 : Fin 21)
  | 3, 19 => (16 : Fin 21)
  | 3, 20 => (18 : Fin 21)
  | 4, 0 => (1 : Fin 21)
  | 4, 1 => (0 : Fin 21)
  | 4, 2 => (3 : Fin 21)
  | 4, 3 => (2 : Fin 21)
  | 4, 4 => (4 : Fin 21)
  | 4, 5 => (9 : Fin 21)
  | 4, 6 => (11 : Fin 21)
  | 4, 7 => (7 : Fin 21)
  | 4, 8 => (13 : Fin 21)
  | 4, 9 => (5 : Fin 21)
  | 4, 10 => (16 : Fin 21)
  | 4, 11 => (6 : Fin 21)
  | 4, 12 => (12 : Fin 21)
  | 4, 13 => (8 : Fin 21)
  | 4, 14 => (17 : Fin 21)
  | 4, 15 => (15 : Fin 21)
  | 4, 16 => (10 : Fin 21)
  | 4, 17 => (14 : Fin 21)
  | 4, 18 => (18 : Fin 21)
  | 4, 19 => (20 : Fin 21)
  | 4, 20 => (19 : Fin 21)
  | 5, 0 => (0 : Fin 21)
  | 5, 1 => (5 : Fin 21)
  | 5, 2 => (6 : Fin 21)
  | 5, 3 => (7 : Fin 21)
  | 5, 4 => (8 : Fin 21)
  | 5, 5 => (10 : Fin 21)
  | 5, 6 => (12 : Fin 21)
  | 5, 7 => (11 : Fin 21)
  | 5, 8 => (14 : Fin 21)
  | 5, 9 => (16 : Fin 21)
  | 5, 10 => (1 : Fin 21)
  | 5, 11 => (3 : Fin 21)
  | 5, 12 => (2 : Fin 21)
  | 5, 13 => (18 : Fin 21)
  | 5, 14 => (4 : Fin 21)
  | 5, 15 => (15 : Fin 21)
  | 5, 16 => (19 : Fin 21)
  | 5, 17 => (13 : Fin 21)
  | 5, 18 => (17 : Fin 21)
  | 5, 19 => (9 : Fin 21)
  | 5, 20 => (20 : Fin 21)
  | _, _ => (0 : Fin 21)

@[reducible, expose]
public def m22L1Factor : Fin 6 -> Fin 21 -> List (Fin 8)
  | 0, 0 => [(0 : Fin 8)]
  | 0, 1 => []
  | 0, 2 => []
  | 0, 3 => []
  | 0, 4 => []
  | 0, 5 => [(2 : Fin 8), (1 : Fin 8), (3 : Fin 8), (5 : Fin 8), (3 : Fin 8)]
  | 0, 6 => [(2 : Fin 8), (1 : Fin 8), (3 : Fin 8), (5 : Fin 8), (3 : Fin 8)]
  | 0, 7 => [(0 : Fin 8), (6 : Fin 8), (1 : Fin 8), (3 : Fin 8), (1 : Fin 8)]
  | 0, 8 => [(0 : Fin 8), (6 : Fin 8), (1 : Fin 8), (3 : Fin 8), (1 : Fin 8)]
  | 0, 9 => []
  | 0, 10 => [(2 : Fin 8), (1 : Fin 8), (3 : Fin 8), (5 : Fin 8), (3 : Fin 8)]
  | 0, 11 => [(0 : Fin 8), (1 : Fin 8), (0 : Fin 8), (2 : Fin 8), (1 : Fin 8)]
  | 0, 12 => [(2 : Fin 8), (1 : Fin 8), (3 : Fin 8), (5 : Fin 8), (3 : Fin 8)]
  | 0, 13 => []
  | 0, 14 => [(0 : Fin 8), (6 : Fin 8), (1 : Fin 8), (3 : Fin 8), (1 : Fin 8)]
  | 0, 15 => []
  | 0, 16 => []
  | 0, 17 => []
  | 0, 18 => [(1 : Fin 8), (2 : Fin 8)]
  | 0, 19 => []
  | 0, 20 => [(6 : Fin 8), (5 : Fin 8)]
  | 1, 0 => []
  | 1, 1 => []
  | 1, 2 => []
  | 1, 3 => []
  | 1, 4 => [(0 : Fin 8)]
  | 1, 5 => []
  | 1, 6 => []
  | 1, 7 => [(0 : Fin 8), (7 : Fin 8), (2 : Fin 8), (1 : Fin 8), (7 : Fin 8)]
  | 1, 8 => []
  | 1, 9 => []
  | 1, 10 => [(5 : Fin 8)]
  | 1, 11 => []
  | 1, 12 => [(1 : Fin 8), (3 : Fin 8), (2 : Fin 8), (5 : Fin 8)]
  | 1, 13 => []
  | 1, 14 => [(1 : Fin 8), (7 : Fin 8), (1 : Fin 8), (7 : Fin 8)]
  | 1, 15 => [(2 : Fin 8), (7 : Fin 8), (0 : Fin 8), (2 : Fin 8)]
  | 1, 16 => [(1 : Fin 8)]
  | 1, 17 => [(3 : Fin 8), (5 : Fin 8), (3 : Fin 8), (5 : Fin 8)]
  | 1, 18 => [(0 : Fin 8), (2 : Fin 8), (0 : Fin 8), (3 : Fin 8)]
  | 1, 19 => []
  | 1, 20 => []
  | 2, 0 => [(1 : Fin 8)]
  | 2, 1 => []
  | 2, 2 => []
  | 2, 3 => [(0 : Fin 8), (7 : Fin 8), (5 : Fin 8), (0 : Fin 8), (6 : Fin 8)]
  | 2, 4 => []
  | 2, 5 => []
  | 2, 6 => []
  | 2, 7 => []
  | 2, 8 => []
  | 2, 9 => [(0 : Fin 8), (1 : Fin 8), (2 : Fin 8), (5 : Fin 8)]
  | 2, 10 => []
  | 2, 11 => [(0 : Fin 8), (7 : Fin 8), (5 : Fin 8), (0 : Fin 8), (6 : Fin 8)]
  | 2, 12 => []
  | 2, 13 => [(6 : Fin 8), (1 : Fin 8), (6 : Fin 8), (0 : Fin 8)]
  | 2, 14 => []
  | 2, 15 => [(1 : Fin 8), (6 : Fin 8), (5 : Fin 8), (0 : Fin 8)]
  | 2, 16 => []
  | 2, 17 => [(0 : Fin 8), (2 : Fin 8), (5 : Fin 8), (2 : Fin 8)]
  | 2, 18 => []
  | 2, 19 => [(1 : Fin 8), (6 : Fin 8), (5 : Fin 8), (0 : Fin 8)]
  | 2, 20 => [(1 : Fin 8), (0 : Fin 8), (5 : Fin 8), (6 : Fin 8)]
  | 3, 0 => [(0 : Fin 8)]
  | 3, 1 => []
  | 3, 2 => []
  | 3, 3 => []
  | 3, 4 => []
  | 3, 5 => [(2 : Fin 8), (1 : Fin 8), (3 : Fin 8), (5 : Fin 8), (3 : Fin 8)]
  | 3, 6 => [(2 : Fin 8), (1 : Fin 8), (3 : Fin 8), (5 : Fin 8), (3 : Fin 8)]
  | 3, 7 => [(0 : Fin 8), (6 : Fin 8), (1 : Fin 8), (3 : Fin 8), (1 : Fin 8)]
  | 3, 8 => [(0 : Fin 8), (6 : Fin 8), (1 : Fin 8), (3 : Fin 8), (1 : Fin 8)]
  | 3, 9 => []
  | 3, 10 => [(2 : Fin 8), (1 : Fin 8), (3 : Fin 8), (5 : Fin 8), (3 : Fin 8)]
  | 3, 11 => [(0 : Fin 8), (1 : Fin 8), (0 : Fin 8), (2 : Fin 8), (1 : Fin 8)]
  | 3, 12 => [(2 : Fin 8), (1 : Fin 8), (3 : Fin 8), (5 : Fin 8), (3 : Fin 8)]
  | 3, 13 => []
  | 3, 14 => [(0 : Fin 8), (6 : Fin 8), (1 : Fin 8), (3 : Fin 8), (1 : Fin 8)]
  | 3, 15 => []
  | 3, 16 => []
  | 3, 17 => []
  | 3, 18 => [(1 : Fin 8), (2 : Fin 8)]
  | 3, 19 => []
  | 3, 20 => [(6 : Fin 8), (5 : Fin 8)]
  | 4, 0 => []
  | 4, 1 => []
  | 4, 2 => []
  | 4, 3 => []
  | 4, 4 => [(0 : Fin 8)]
  | 4, 5 => []
  | 4, 6 => []
  | 4, 7 => [(0 : Fin 8), (7 : Fin 8), (2 : Fin 8), (1 : Fin 8), (7 : Fin 8)]
  | 4, 8 => []
  | 4, 9 => []
  | 4, 10 => [(5 : Fin 8)]
  | 4, 11 => []
  | 4, 12 => [(1 : Fin 8), (3 : Fin 8), (2 : Fin 8), (5 : Fin 8)]
  | 4, 13 => []
  | 4, 14 => [(1 : Fin 8), (7 : Fin 8), (1 : Fin 8), (7 : Fin 8)]
  | 4, 15 => [(2 : Fin 8), (7 : Fin 8), (0 : Fin 8), (2 : Fin 8)]
  | 4, 16 => [(1 : Fin 8)]
  | 4, 17 => [(3 : Fin 8), (5 : Fin 8), (3 : Fin 8), (5 : Fin 8)]
  | 4, 18 => [(0 : Fin 8), (2 : Fin 8), (0 : Fin 8), (3 : Fin 8)]
  | 4, 19 => []
  | 4, 20 => []
  | 5, 0 => [(5 : Fin 8)]
  | 5, 1 => []
  | 5, 2 => []
  | 5, 3 => []
  | 5, 4 => []
  | 5, 5 => []
  | 5, 6 => []
  | 5, 7 => [(0 : Fin 8), (7 : Fin 8), (5 : Fin 8), (0 : Fin 8), (6 : Fin 8)]
  | 5, 8 => []
  | 5, 9 => []
  | 5, 10 => []
  | 5, 11 => [(0 : Fin 8), (7 : Fin 8), (5 : Fin 8), (0 : Fin 8), (6 : Fin 8)]
  | 5, 12 => []
  | 5, 13 => []
  | 5, 14 => []
  | 5, 15 => [(0 : Fin 8), (1 : Fin 8), (2 : Fin 8), (5 : Fin 8)]
  | 5, 16 => [(0 : Fin 8), (1 : Fin 8), (2 : Fin 8), (5 : Fin 8)]
  | 5, 17 => [(0 : Fin 8), (2 : Fin 8), (5 : Fin 8), (2 : Fin 8)]
  | 5, 18 => [(6 : Fin 8), (1 : Fin 8), (6 : Fin 8), (0 : Fin 8)]
  | 5, 19 => [(1 : Fin 8), (6 : Fin 8), (5 : Fin 8), (0 : Fin 8)]
  | 5, 20 => [(2 : Fin 8), (1 : Fin 8), (0 : Fin 8), (5 : Fin 8)]
  | _, _ => [(0 : Fin 8)]

public theorem m22L1RepBase : m22L1Rep (0 : Fin 21) = 1 := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

public theorem m22L1RepPoint : (r : Fin 21) -> m22L1Rep r (2 : Fin 22) = m22L1Point r := by
  intro r
  fin_cases r <;> rfl

@[reducible, expose]
public def m22L1PointInv : Fin 22 -> Fin 21
  | 0 => (1 : Fin 21)
  | 1 => (0 : Fin 21)
  | 2 => (0 : Fin 21)
  | 3 => (10 : Fin 21)
  | 4 => (7 : Fin 21)
  | 5 => (20 : Fin 21)
  | 6 => (18 : Fin 21)
  | 7 => (6 : Fin 21)
  | 8 => (3 : Fin 21)
  | 9 => (2 : Fin 21)
  | 10 => (12 : Fin 21)
  | 11 => (16 : Fin 21)
  | 12 => (15 : Fin 21)
  | 13 => (19 : Fin 21)
  | 14 => (17 : Fin 21)
  | 15 => (8 : Fin 21)
  | 16 => (9 : Fin 21)
  | 17 => (4 : Fin 21)
  | 18 => (14 : Fin 21)
  | 19 => (13 : Fin 21)
  | 20 => (11 : Fin 21)
  | 21 => (5 : Fin 21)
  | _ => (1 : Fin 21)

public theorem m22L1PointInv_left : (r : Fin 21) -> m22L1PointInv (m22L1Point r) = r := by
  intro r
  fin_cases r <;> rfl

public theorem m22L1Point_injective : Function.Injective m22L1Point := by
  intro x y h
  have hh := congrArg m22L1PointInv h
  simpa [m22L1PointInv_left] using hh

end Sporadic.Mathieu
