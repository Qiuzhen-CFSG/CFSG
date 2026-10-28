module

public import Theory.Mathieu.M22.Properties.OrderCertificate
import Mathlib.Tactic.FinCases

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise
@[reducible, expose]
public def m22L2R0To : Fin 22 -> Fin 22 := id

@[reducible, expose]
public def m22L2R0InvFun : Fin 22 -> Fin 22 := id

public theorem m22L2R0_left : forall x, m22L2R0InvFun (m22L2R0To x) = x := by
  intro x
  rfl

public theorem m22L2R0_right : forall x, m22L2R0To (m22L2R0InvFun x) = x := by
  intro x
  rfl

@[reducible, expose]
public def m22L2R0 : Equiv.Perm (Fin 22) := Equiv.refl _

@[reducible, expose]
public def m22L2R1To : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (0 : Fin 22)
  | 4 => (20 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (14 : Fin 22)
  | 7 => (10 : Fin 22)
  | 8 => (4 : Fin 22)
  | 9 => (7 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (13 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (18 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (15 : Fin 22)
  | 18 => (17 : Fin 22)
  | 19 => (6 : Fin 22)
  | 20 => (8 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R1InvFun : Fin 22 -> Fin 22
  | 0 => (3 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (8 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (19 : Fin 22)
  | 7 => (9 : Fin 22)
  | 8 => (20 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (7 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (11 : Fin 22)
  | 14 => (6 : Fin 22)
  | 15 => (17 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (18 : Fin 22)
  | 18 => (15 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (4 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R1_left : forall x, m22L2R1InvFun (m22L2R1To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R1_right : forall x, m22L2R1To (m22L2R1InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R1_left

@[reducible, expose]
public def m22L2R1 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R1To m22L2R1InvFun m22L2R1_left m22L2R1_right

@[reducible, expose]
public def m22L2R2To : Fin 22 -> Fin 22
  | 0 => (7 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (9 : Fin 22)
  | 4 => (20 : Fin 22)
  | 5 => (6 : Fin 22)
  | 6 => (19 : Fin 22)
  | 7 => (10 : Fin 22)
  | 8 => (15 : Fin 22)
  | 9 => (21 : Fin 22)
  | 10 => (0 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (16 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (14 : Fin 22)
  | 15 => (18 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (4 : Fin 22)
  | 18 => (8 : Fin 22)
  | 19 => (5 : Fin 22)
  | 20 => (17 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R2InvFun : Fin 22 -> Fin 22
  | 0 => (10 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (17 : Fin 22)
  | 5 => (19 : Fin 22)
  | 6 => (5 : Fin 22)
  | 7 => (0 : Fin 22)
  | 8 => (18 : Fin 22)
  | 9 => (3 : Fin 22)
  | 10 => (7 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (14 : Fin 22)
  | 15 => (8 : Fin 22)
  | 16 => (12 : Fin 22)
  | 17 => (20 : Fin 22)
  | 18 => (15 : Fin 22)
  | 19 => (6 : Fin 22)
  | 20 => (4 : Fin 22)
  | 21 => (9 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R2_left : forall x, m22L2R2InvFun (m22L2R2To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R2_right : forall x, m22L2R2To (m22L2R2InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R2_left

@[reducible, expose]
public def m22L2R2 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R2To m22L2R2InvFun m22L2R2_left m22L2R2_right

@[reducible, expose]
public def m22L2R3To : Fin 22 -> Fin 22 :=
  m22L2G1To

@[reducible, expose]
public def m22L2R3InvFun : Fin 22 -> Fin 22 :=
  m22L2G1InvFun

public theorem m22L2R3_left : forall x, m22L2R3InvFun (m22L2R3To x) = x :=
  m22L2G1_left

public theorem m22L2R3_right : forall x, m22L2R3To (m22L2R3InvFun x) = x :=
  m22L2G1_right

@[reducible, expose]
public def m22L2R3 : Equiv.Perm (Fin 22) :=
  m22L2G1

@[reducible, expose]
public def m22L2R4To : Fin 22 -> Fin 22
  | 0 => (10 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (7 : Fin 22)
  | 4 => (8 : Fin 22)
  | 5 => (14 : Fin 22)
  | 6 => (6 : Fin 22)
  | 7 => (9 : Fin 22)
  | 8 => (18 : Fin 22)
  | 9 => (3 : Fin 22)
  | 10 => (21 : Fin 22)
  | 11 => (13 : Fin 22)
  | 12 => (11 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (17 : Fin 22)
  | 16 => (16 : Fin 22)
  | 17 => (20 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (5 : Fin 22)
  | 20 => (15 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R4InvFun : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (9 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (19 : Fin 22)
  | 6 => (6 : Fin 22)
  | 7 => (3 : Fin 22)
  | 8 => (4 : Fin 22)
  | 9 => (7 : Fin 22)
  | 10 => (0 : Fin 22)
  | 11 => (12 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (11 : Fin 22)
  | 14 => (5 : Fin 22)
  | 15 => (20 : Fin 22)
  | 16 => (16 : Fin 22)
  | 17 => (15 : Fin 22)
  | 18 => (8 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (17 : Fin 22)
  | 21 => (10 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R4_left : forall x, m22L2R4InvFun (m22L2R4To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R4_right : forall x, m22L2R4To (m22L2R4InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R4_left

@[reducible, expose]
public def m22L2R4 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R4To m22L2R4InvFun m22L2R4_left m22L2R4_right

@[reducible, expose]
public def m22L2R5To : Fin 22 -> Fin 22
  | 0 => (9 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (10 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (19 : Fin 22)
  | 6 => (14 : Fin 22)
  | 7 => (7 : Fin 22)
  | 8 => (17 : Fin 22)
  | 9 => (0 : Fin 22)
  | 10 => (3 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (6 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (8 : Fin 22)
  | 18 => (20 : Fin 22)
  | 19 => (5 : Fin 22)
  | 20 => (18 : Fin 22)
  | 21 => (21 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R5InvFun : Fin 22 -> Fin 22
  | 0 => (9 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (10 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (19 : Fin 22)
  | 6 => (14 : Fin 22)
  | 7 => (7 : Fin 22)
  | 8 => (17 : Fin 22)
  | 9 => (0 : Fin 22)
  | 10 => (3 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (6 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (8 : Fin 22)
  | 18 => (20 : Fin 22)
  | 19 => (5 : Fin 22)
  | 20 => (18 : Fin 22)
  | 21 => (21 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R5_left : forall x, m22L2R5InvFun (m22L2R5To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R5_right : forall x, m22L2R5To (m22L2R5InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R5_left

@[reducible, expose]
public def m22L2R5 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R5To m22L2R5InvFun m22L2R5_left m22L2R5_right

@[reducible, expose]
public def m22L2R6To : Fin 22 -> Fin 22
  | 0 => (9 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (6 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (7 : Fin 22)
  | 6 => (21 : Fin 22)
  | 7 => (20 : Fin 22)
  | 8 => (0 : Fin 22)
  | 9 => (8 : Fin 22)
  | 10 => (14 : Fin 22)
  | 11 => (12 : Fin 22)
  | 12 => (16 : Fin 22)
  | 13 => (13 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (10 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (19 : Fin 22)
  | 19 => (4 : Fin 22)
  | 20 => (5 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R6InvFun : Fin 22 -> Fin 22
  | 0 => (8 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (19 : Fin 22)
  | 5 => (20 : Fin 22)
  | 6 => (3 : Fin 22)
  | 7 => (5 : Fin 22)
  | 8 => (9 : Fin 22)
  | 9 => (0 : Fin 22)
  | 10 => (15 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (11 : Fin 22)
  | 13 => (13 : Fin 22)
  | 14 => (10 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (12 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (18 : Fin 22)
  | 20 => (7 : Fin 22)
  | 21 => (6 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R6_left : forall x, m22L2R6InvFun (m22L2R6To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R6_right : forall x, m22L2R6To (m22L2R6InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R6_left

@[reducible, expose]
public def m22L2R6 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R6To m22L2R6InvFun m22L2R6_left m22L2R6_right

@[reducible, expose]
public def m22L2R7To : Fin 22 -> Fin 22
  | 0 => (8 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (14 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (15 : Fin 22)
  | 7 => (20 : Fin 22)
  | 8 => (17 : Fin 22)
  | 9 => (9 : Fin 22)
  | 10 => (6 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (21 : Fin 22)
  | 15 => (10 : Fin 22)
  | 16 => (12 : Fin 22)
  | 17 => (0 : Fin 22)
  | 18 => (5 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (19 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R7InvFun : Fin 22 -> Fin 22
  | 0 => (17 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (18 : Fin 22)
  | 6 => (10 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (0 : Fin 22)
  | 9 => (9 : Fin 22)
  | 10 => (15 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (16 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (3 : Fin 22)
  | 15 => (6 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (8 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (20 : Fin 22)
  | 20 => (7 : Fin 22)
  | 21 => (14 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R7_left : forall x, m22L2R7InvFun (m22L2R7To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R7_right : forall x, m22L2R7To (m22L2R7InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R7_left

@[reducible, expose]
public def m22L2R7 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R7To m22L2R7InvFun m22L2R7_left m22L2R7_right

@[reducible, expose]
public def m22L2R8To : Fin 22 -> Fin 22
  | 0 => (20 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (8 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (21 : Fin 22)
  | 6 => (4 : Fin 22)
  | 7 => (14 : Fin 22)
  | 8 => (10 : Fin 22)
  | 9 => (3 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (12 : Fin 22)
  | 12 => (11 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (18 : Fin 22)
  | 18 => (0 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (17 : Fin 22)
  | 21 => (6 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R8InvFun : Fin 22 -> Fin 22
  | 0 => (18 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (9 : Fin 22)
  | 4 => (6 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (21 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (3 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (8 : Fin 22)
  | 11 => (12 : Fin 22)
  | 12 => (11 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (7 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (20 : Fin 22)
  | 18 => (17 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (0 : Fin 22)
  | 21 => (5 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R8_left : forall x, m22L2R8InvFun (m22L2R8To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R8_right : forall x, m22L2R8To (m22L2R8InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R8_left

@[reducible, expose]
public def m22L2R8 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R8To m22L2R8InvFun m22L2R8_left m22L2R8_right

@[reducible, expose]
public def m22L2R9To : Fin 22 -> Fin 22
  | 0 => (19 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (20 : Fin 22)
  | 4 => (9 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (7 : Fin 22)
  | 7 => (17 : Fin 22)
  | 8 => (14 : Fin 22)
  | 9 => (5 : Fin 22)
  | 10 => (3 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (16 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (8 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (6 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (21 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R9InvFun : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (10 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (9 : Fin 22)
  | 6 => (17 : Fin 22)
  | 7 => (6 : Fin 22)
  | 8 => (15 : Fin 22)
  | 9 => (4 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (8 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (12 : Fin 22)
  | 17 => (7 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (0 : Fin 22)
  | 20 => (3 : Fin 22)
  | 21 => (19 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R9_left : forall x, m22L2R9InvFun (m22L2R9To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R9_right : forall x, m22L2R9To (m22L2R9InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R9_left

@[reducible, expose]
public def m22L2R9 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R9To m22L2R9InvFun m22L2R9_left m22L2R9_right

@[reducible, expose]
public def m22L2R10To : Fin 22 -> Fin 22
  | 0 => (0 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (5 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (21 : Fin 22)
  | 6 => (7 : Fin 22)
  | 7 => (20 : Fin 22)
  | 8 => (9 : Fin 22)
  | 9 => (17 : Fin 22)
  | 10 => (19 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (11 : Fin 22)
  | 14 => (4 : Fin 22)
  | 15 => (10 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (8 : Fin 22)
  | 18 => (14 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (6 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R10InvFun : Fin 22 -> Fin 22
  | 0 => (0 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (14 : Fin 22)
  | 5 => (3 : Fin 22)
  | 6 => (20 : Fin 22)
  | 7 => (6 : Fin 22)
  | 8 => (17 : Fin 22)
  | 9 => (8 : Fin 22)
  | 10 => (15 : Fin 22)
  | 11 => (13 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (18 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (9 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (10 : Fin 22)
  | 20 => (7 : Fin 22)
  | 21 => (5 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R10_left : forall x, m22L2R10InvFun (m22L2R10To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R10_right : forall x, m22L2R10To (m22L2R10InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R10_left

@[reducible, expose]
public def m22L2R10 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R10To m22L2R10InvFun m22L2R10_left m22L2R10_right

@[reducible, expose]
public def m22L2R11To : Fin 22 -> Fin 22
  | 0 => (14 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (4 : Fin 22)
  | 4 => (10 : Fin 22)
  | 5 => (8 : Fin 22)
  | 6 => (9 : Fin 22)
  | 7 => (18 : Fin 22)
  | 8 => (6 : Fin 22)
  | 9 => (5 : Fin 22)
  | 10 => (21 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (20 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (15 : Fin 22)
  | 19 => (0 : Fin 22)
  | 20 => (7 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R11InvFun : Fin 22 -> Fin 22
  | 0 => (19 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (3 : Fin 22)
  | 5 => (9 : Fin 22)
  | 6 => (8 : Fin 22)
  | 7 => (20 : Fin 22)
  | 8 => (5 : Fin 22)
  | 9 => (6 : Fin 22)
  | 10 => (4 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (0 : Fin 22)
  | 15 => (18 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (7 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (15 : Fin 22)
  | 21 => (10 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R11_left : forall x, m22L2R11InvFun (m22L2R11To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R11_right : forall x, m22L2R11To (m22L2R11InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R11_left

@[reducible, expose]
public def m22L2R11 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R11To m22L2R11InvFun m22L2R11_left m22L2R11_right

@[reducible, expose]
public def m22L2R12To : Fin 22 -> Fin 22
  | 0 => (15 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (19 : Fin 22)
  | 4 => (10 : Fin 22)
  | 5 => (11 : Fin 22)
  | 6 => (12 : Fin 22)
  | 7 => (18 : Fin 22)
  | 8 => (21 : Fin 22)
  | 9 => (7 : Fin 22)
  | 10 => (6 : Fin 22)
  | 11 => (0 : Fin 22)
  | 12 => (17 : Fin 22)
  | 13 => (9 : Fin 22)
  | 14 => (13 : Fin 22)
  | 15 => (20 : Fin 22)
  | 16 => (8 : Fin 22)
  | 17 => (4 : Fin 22)
  | 18 => (14 : Fin 22)
  | 19 => (16 : Fin 22)
  | 20 => (5 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R12InvFun : Fin 22 -> Fin 22
  | 0 => (11 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (17 : Fin 22)
  | 5 => (20 : Fin 22)
  | 6 => (10 : Fin 22)
  | 7 => (9 : Fin 22)
  | 8 => (16 : Fin 22)
  | 9 => (13 : Fin 22)
  | 10 => (4 : Fin 22)
  | 11 => (5 : Fin 22)
  | 12 => (6 : Fin 22)
  | 13 => (14 : Fin 22)
  | 14 => (18 : Fin 22)
  | 15 => (0 : Fin 22)
  | 16 => (19 : Fin 22)
  | 17 => (12 : Fin 22)
  | 18 => (7 : Fin 22)
  | 19 => (3 : Fin 22)
  | 20 => (15 : Fin 22)
  | 21 => (8 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R12_left : forall x, m22L2R12InvFun (m22L2R12To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R12_right : forall x, m22L2R12To (m22L2R12InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R12_left

@[reducible, expose]
public def m22L2R12 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R12To m22L2R12InvFun m22L2R12_left m22L2R12_right

@[reducible, expose]
public def m22L2R13To : Fin 22 -> Fin 22
  | 0 => (20 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (17 : Fin 22)
  | 4 => (6 : Fin 22)
  | 5 => (7 : Fin 22)
  | 6 => (15 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (10 : Fin 22)
  | 9 => (3 : Fin 22)
  | 10 => (0 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (4 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (18 : Fin 22)
  | 18 => (9 : Fin 22)
  | 19 => (21 : Fin 22)
  | 20 => (8 : Fin 22)
  | 21 => (5 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R13InvFun : Fin 22 -> Fin 22
  | 0 => (10 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (9 : Fin 22)
  | 4 => (14 : Fin 22)
  | 5 => (21 : Fin 22)
  | 6 => (4 : Fin 22)
  | 7 => (5 : Fin 22)
  | 8 => (20 : Fin 22)
  | 9 => (18 : Fin 22)
  | 10 => (8 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (6 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (3 : Fin 22)
  | 18 => (17 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (0 : Fin 22)
  | 21 => (19 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R13_left : forall x, m22L2R13InvFun (m22L2R13To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R13_right : forall x, m22L2R13To (m22L2R13InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R13_left

@[reducible, expose]
public def m22L2R13 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R13To m22L2R13InvFun m22L2R13_left m22L2R13_right

@[reducible, expose]
public def m22L2R14To : Fin 22 -> Fin 22
  | 0 => (19 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (18 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (12 : Fin 22)
  | 6 => (13 : Fin 22)
  | 7 => (15 : Fin 22)
  | 8 => (5 : Fin 22)
  | 9 => (6 : Fin 22)
  | 10 => (3 : Fin 22)
  | 11 => (17 : Fin 22)
  | 12 => (8 : Fin 22)
  | 13 => (9 : Fin 22)
  | 14 => (11 : Fin 22)
  | 15 => (21 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (10 : Fin 22)
  | 19 => (16 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (7 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R14InvFun : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (10 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (8 : Fin 22)
  | 6 => (9 : Fin 22)
  | 7 => (21 : Fin 22)
  | 8 => (12 : Fin 22)
  | 9 => (13 : Fin 22)
  | 10 => (18 : Fin 22)
  | 11 => (14 : Fin 22)
  | 12 => (5 : Fin 22)
  | 13 => (6 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (7 : Fin 22)
  | 16 => (19 : Fin 22)
  | 17 => (11 : Fin 22)
  | 18 => (3 : Fin 22)
  | 19 => (0 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (15 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R14_left : forall x, m22L2R14InvFun (m22L2R14To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R14_right : forall x, m22L2R14To (m22L2R14InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R14_left

@[reducible, expose]
public def m22L2R14 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R14To m22L2R14InvFun m22L2R14_left m22L2R14_right

@[reducible, expose]
public def m22L2R15To : Fin 22 -> Fin 22
  | 0 => (18 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (15 : Fin 22)
  | 4 => (14 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (11 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (20 : Fin 22)
  | 9 => (3 : Fin 22)
  | 10 => (7 : Fin 22)
  | 11 => (8 : Fin 22)
  | 12 => (0 : Fin 22)
  | 13 => (9 : Fin 22)
  | 14 => (12 : Fin 22)
  | 15 => (5 : Fin 22)
  | 16 => (17 : Fin 22)
  | 17 => (10 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (16 : Fin 22)
  | 20 => (21 : Fin 22)
  | 21 => (6 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R15InvFun : Fin 22 -> Fin 22
  | 0 => (12 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (9 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (15 : Fin 22)
  | 6 => (21 : Fin 22)
  | 7 => (10 : Fin 22)
  | 8 => (11 : Fin 22)
  | 9 => (13 : Fin 22)
  | 10 => (17 : Fin 22)
  | 11 => (6 : Fin 22)
  | 12 => (14 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (4 : Fin 22)
  | 15 => (3 : Fin 22)
  | 16 => (19 : Fin 22)
  | 17 => (16 : Fin 22)
  | 18 => (0 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (8 : Fin 22)
  | 21 => (20 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R15_left : forall x, m22L2R15InvFun (m22L2R15To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R15_right : forall x, m22L2R15To (m22L2R15InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R15_left

@[reducible, expose]
public def m22L2R15 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R15To m22L2R15InvFun m22L2R15_left m22L2R15_right

@[reducible, expose]
public def m22L2R16To : Fin 22 -> Fin 22
  | 0 => (19 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (11 : Fin 22)
  | 4 => (20 : Fin 22)
  | 5 => (15 : Fin 22)
  | 6 => (7 : Fin 22)
  | 7 => (10 : Fin 22)
  | 8 => (6 : Fin 22)
  | 9 => (14 : Fin 22)
  | 10 => (13 : Fin 22)
  | 11 => (9 : Fin 22)
  | 12 => (17 : Fin 22)
  | 13 => (8 : Fin 22)
  | 14 => (21 : Fin 22)
  | 15 => (18 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (5 : Fin 22)
  | 18 => (12 : Fin 22)
  | 19 => (4 : Fin 22)
  | 20 => (16 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R16InvFun : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (19 : Fin 22)
  | 5 => (17 : Fin 22)
  | 6 => (8 : Fin 22)
  | 7 => (6 : Fin 22)
  | 8 => (13 : Fin 22)
  | 9 => (11 : Fin 22)
  | 10 => (7 : Fin 22)
  | 11 => (3 : Fin 22)
  | 12 => (18 : Fin 22)
  | 13 => (10 : Fin 22)
  | 14 => (9 : Fin 22)
  | 15 => (5 : Fin 22)
  | 16 => (20 : Fin 22)
  | 17 => (12 : Fin 22)
  | 18 => (15 : Fin 22)
  | 19 => (0 : Fin 22)
  | 20 => (4 : Fin 22)
  | 21 => (14 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R16_left : forall x, m22L2R16InvFun (m22L2R16To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R16_right : forall x, m22L2R16To (m22L2R16InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R16_left

@[reducible, expose]
public def m22L2R16 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R16To m22L2R16InvFun m22L2R16_left m22L2R16_right

@[reducible, expose]
public def m22L2R17To : Fin 22 -> Fin 22
  | 0 => (14 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (13 : Fin 22)
  | 4 => (20 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (21 : Fin 22)
  | 7 => (10 : Fin 22)
  | 8 => (5 : Fin 22)
  | 9 => (19 : Fin 22)
  | 10 => (11 : Fin 22)
  | 11 => (0 : Fin 22)
  | 12 => (8 : Fin 22)
  | 13 => (17 : Fin 22)
  | 14 => (7 : Fin 22)
  | 15 => (18 : Fin 22)
  | 16 => (9 : Fin 22)
  | 17 => (6 : Fin 22)
  | 18 => (16 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (12 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R17InvFun : Fin 22 -> Fin 22
  | 0 => (11 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (8 : Fin 22)
  | 6 => (17 : Fin 22)
  | 7 => (14 : Fin 22)
  | 8 => (12 : Fin 22)
  | 9 => (16 : Fin 22)
  | 10 => (7 : Fin 22)
  | 11 => (10 : Fin 22)
  | 12 => (20 : Fin 22)
  | 13 => (3 : Fin 22)
  | 14 => (0 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (18 : Fin 22)
  | 17 => (13 : Fin 22)
  | 18 => (15 : Fin 22)
  | 19 => (9 : Fin 22)
  | 20 => (4 : Fin 22)
  | 21 => (6 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R17_left : forall x, m22L2R17InvFun (m22L2R17To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R17_right : forall x, m22L2R17To (m22L2R17InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R17_left

@[reducible, expose]
public def m22L2R17 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R17To m22L2R17InvFun m22L2R17_left m22L2R17_right

@[reducible, expose]
public def m22L2R18To : Fin 22 -> Fin 22
  | 0 => (6 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (20 : Fin 22)
  | 5 => (7 : Fin 22)
  | 6 => (15 : Fin 22)
  | 7 => (10 : Fin 22)
  | 8 => (19 : Fin 22)
  | 9 => (5 : Fin 22)
  | 10 => (12 : Fin 22)
  | 11 => (17 : Fin 22)
  | 12 => (9 : Fin 22)
  | 13 => (0 : Fin 22)
  | 14 => (4 : Fin 22)
  | 15 => (18 : Fin 22)
  | 16 => (8 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (13 : Fin 22)
  | 19 => (21 : Fin 22)
  | 20 => (11 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R18InvFun : Fin 22 -> Fin 22
  | 0 => (13 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (14 : Fin 22)
  | 5 => (9 : Fin 22)
  | 6 => (0 : Fin 22)
  | 7 => (5 : Fin 22)
  | 8 => (16 : Fin 22)
  | 9 => (12 : Fin 22)
  | 10 => (7 : Fin 22)
  | 11 => (20 : Fin 22)
  | 12 => (10 : Fin 22)
  | 13 => (18 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (6 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (11 : Fin 22)
  | 18 => (15 : Fin 22)
  | 19 => (8 : Fin 22)
  | 20 => (4 : Fin 22)
  | 21 => (19 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R18_left : forall x, m22L2R18InvFun (m22L2R18To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R18_right : forall x, m22L2R18To (m22L2R18InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R18_left

@[reducible, expose]
public def m22L2R18 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R18To m22L2R18InvFun m22L2R18_left m22L2R18_right

@[reducible, expose]
public def m22L2R19To : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (12 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (0 : Fin 22)
  | 6 => (9 : Fin 22)
  | 7 => (20 : Fin 22)
  | 8 => (7 : Fin 22)
  | 9 => (15 : Fin 22)
  | 10 => (11 : Fin 22)
  | 11 => (6 : Fin 22)
  | 12 => (5 : Fin 22)
  | 13 => (19 : Fin 22)
  | 14 => (8 : Fin 22)
  | 15 => (10 : Fin 22)
  | 16 => (14 : Fin 22)
  | 17 => (4 : Fin 22)
  | 18 => (13 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (16 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L2R19InvFun : Fin 22 -> Fin 22
  | 0 => (5 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (17 : Fin 22)
  | 5 => (12 : Fin 22)
  | 6 => (11 : Fin 22)
  | 7 => (8 : Fin 22)
  | 8 => (14 : Fin 22)
  | 9 => (6 : Fin 22)
  | 10 => (15 : Fin 22)
  | 11 => (10 : Fin 22)
  | 12 => (3 : Fin 22)
  | 13 => (18 : Fin 22)
  | 14 => (16 : Fin 22)
  | 15 => (9 : Fin 22)
  | 16 => (20 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (13 : Fin 22)
  | 20 => (7 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2R19_left : forall x, m22L2R19InvFun (m22L2R19To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2R19_right : forall x, m22L2R19To (m22L2R19InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2R19_left

@[reducible, expose]
public def m22L2R19 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2R19To m22L2R19InvFun m22L2R19_left m22L2R19_right

@[reducible, expose]
public def m22L2RepWord : Fin 20 -> List (Fin 8)
  | 0 => []
  | 1 => [(5 : Fin 8)]
  | 2 => [(0 : Fin 8), (5 : Fin 8)]
  | 3 => [(1 : Fin 8)]
  | 4 => [(0 : Fin 8), (1 : Fin 8), (0 : Fin 8)]
  | 5 => [(1 : Fin 8), (0 : Fin 8), (5 : Fin 8)]
  | 6 => [(6 : Fin 8), (5 : Fin 8)]
  | 7 => [(6 : Fin 8), (0 : Fin 8), (5 : Fin 8)]
  | 8 => [(6 : Fin 8), (0 : Fin 8), (1 : Fin 8), (0 : Fin 8)]
  | 9 => [(5 : Fin 8), (2 : Fin 8), (5 : Fin 8)]
  | 10 => [(0 : Fin 8), (6 : Fin 8), (5 : Fin 8)]
  | 11 => [(2 : Fin 8), (5 : Fin 8)]
  | 12 => [(7 : Fin 8), (0 : Fin 8), (5 : Fin 8)]
  | 13 => [(0 : Fin 8), (6 : Fin 8), (0 : Fin 8), (1 : Fin 8), (0 : Fin 8)]
  | 14 => [(7 : Fin 8), (1 : Fin 8), (0 : Fin 8), (5 : Fin 8)]
  | 15 => [(7 : Fin 8), (0 : Fin 8), (1 : Fin 8), (0 : Fin 8)]
  | 16 => [(2 : Fin 8), (3 : Fin 8), (5 : Fin 8)]
  | 17 => [(0 : Fin 8), (2 : Fin 8), (3 : Fin 8), (5 : Fin 8)]
  | 18 => [(2 : Fin 8), (0 : Fin 8), (3 : Fin 8), (5 : Fin 8)]
  | 19 => [(3 : Fin 8), (0 : Fin 8), (5 : Fin 8)]
  | _ => []

@[reducible, expose]
public def m22L2Rep : Fin 20 -> Equiv.Perm (Fin 22)
  | 0 => m22L2R0
  | 1 => m22L2R1
  | 2 => m22L2R2
  | 3 => m22L2R3
  | 4 => m22L2R4
  | 5 => m22L2R5
  | 6 => m22L2R6
  | 7 => m22L2R7
  | 8 => m22L2R8
  | 9 => m22L2R9
  | 10 => m22L2R10
  | 11 => m22L2R11
  | 12 => m22L2R12
  | 13 => m22L2R13
  | 14 => m22L2R14
  | 15 => m22L2R15
  | 16 => m22L2R16
  | 17 => m22L2R17
  | 18 => m22L2R18
  | 19 => m22L2R19
  | _ => m22L2R0

public theorem m22L2Rep_eq_word : (r : Fin 20) -> m22L2Rep r = evalWord m22L2Gen (m22L2RepWord r) := by
  intro r
  fin_cases r <;> apply Equiv.ext <;> intro x <;> fin_cases x <;> rfl

@[reducible, expose]
public def m22L2Point : Fin 20 -> Fin 22
  | 0 => (3 : Fin 22)
  | 1 => (0 : Fin 22)
  | 2 => (9 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (7 : Fin 22)
  | 5 => (10 : Fin 22)
  | 6 => (6 : Fin 22)
  | 7 => (14 : Fin 22)
  | 8 => (8 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (5 : Fin 22)
  | 11 => (4 : Fin 22)
  | 12 => (19 : Fin 22)
  | 13 => (17 : Fin 22)
  | 14 => (18 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (13 : Fin 22)
  | 18 => (16 : Fin 22)
  | 19 => (12 : Fin 22)
  | _ => (3 : Fin 22)

@[reducible, expose]
public def m22L2Act : Fin 8 -> Fin 20 -> Fin 20
  | 0, 0 => (0 : Fin 20)
  | 0, 1 => (2 : Fin 20)
  | 0, 2 => (1 : Fin 20)
  | 0, 3 => (4 : Fin 20)
  | 0, 4 => (3 : Fin 20)
  | 0, 5 => (5 : Fin 20)
  | 0, 6 => (10 : Fin 20)
  | 0, 7 => (12 : Fin 20)
  | 0, 8 => (13 : Fin 20)
  | 0, 9 => (9 : Fin 20)
  | 0, 10 => (6 : Fin 20)
  | 0, 11 => (15 : Fin 20)
  | 0, 12 => (7 : Fin 20)
  | 0, 13 => (8 : Fin 20)
  | 0, 14 => (14 : Fin 20)
  | 0, 15 => (11 : Fin 20)
  | 0, 16 => (17 : Fin 20)
  | 0, 17 => (16 : Fin 20)
  | 0, 18 => (19 : Fin 20)
  | 0, 19 => (18 : Fin 20)
  | 1, 0 => (3 : Fin 20)
  | 1, 1 => (0 : Fin 20)
  | 1, 2 => (5 : Fin 20)
  | 1, 3 => (1 : Fin 20)
  | 1, 4 => (2 : Fin 20)
  | 1, 5 => (4 : Fin 20)
  | 1, 6 => (12 : Fin 20)
  | 1, 7 => (6 : Fin 20)
  | 1, 8 => (9 : Fin 20)
  | 1, 9 => (11 : Fin 20)
  | 1, 10 => (10 : Fin 20)
  | 1, 11 => (8 : Fin 20)
  | 1, 12 => (7 : Fin 20)
  | 1, 13 => (14 : Fin 20)
  | 1, 14 => (15 : Fin 20)
  | 1, 15 => (13 : Fin 20)
  | 1, 16 => (18 : Fin 20)
  | 1, 17 => (16 : Fin 20)
  | 1, 18 => (17 : Fin 20)
  | 1, 19 => (19 : Fin 20)
  | 2, 0 => (0 : Fin 20)
  | 2, 1 => (11 : Fin 20)
  | 2, 2 => (3 : Fin 20)
  | 2, 3 => (7 : Fin 20)
  | 2, 4 => (10 : Fin 20)
  | 2, 5 => (14 : Fin 20)
  | 2, 6 => (1 : Fin 20)
  | 2, 7 => (2 : Fin 20)
  | 2, 8 => (4 : Fin 20)
  | 2, 9 => (5 : Fin 20)
  | 2, 10 => (8 : Fin 20)
  | 2, 11 => (6 : Fin 20)
  | 2, 12 => (13 : Fin 20)
  | 2, 13 => (15 : Fin 20)
  | 2, 14 => (9 : Fin 20)
  | 2, 15 => (12 : Fin 20)
  | 2, 16 => (16 : Fin 20)
  | 2, 17 => (18 : Fin 20)
  | 2, 18 => (19 : Fin 20)
  | 2, 19 => (17 : Fin 20)
  | 3, 0 => (0 : Fin 20)
  | 3, 1 => (16 : Fin 20)
  | 3, 2 => (19 : Fin 20)
  | 3, 3 => (15 : Fin 20)
  | 3, 4 => (3 : Fin 20)
  | 3, 5 => (9 : Fin 20)
  | 3, 6 => (1 : Fin 20)
  | 3, 7 => (8 : Fin 20)
  | 3, 8 => (17 : Fin 20)
  | 3, 9 => (14 : Fin 20)
  | 3, 10 => (13 : Fin 20)
  | 3, 11 => (11 : Fin 20)
  | 3, 12 => (2 : Fin 20)
  | 3, 13 => (18 : Fin 20)
  | 3, 14 => (5 : Fin 20)
  | 3, 15 => (4 : Fin 20)
  | 3, 16 => (6 : Fin 20)
  | 3, 17 => (7 : Fin 20)
  | 3, 18 => (10 : Fin 20)
  | 3, 19 => (12 : Fin 20)
  | 4, 0 => (0 : Fin 20)
  | 4, 1 => (2 : Fin 20)
  | 4, 2 => (1 : Fin 20)
  | 4, 3 => (4 : Fin 20)
  | 4, 4 => (3 : Fin 20)
  | 4, 5 => (5 : Fin 20)
  | 4, 6 => (10 : Fin 20)
  | 4, 7 => (12 : Fin 20)
  | 4, 8 => (13 : Fin 20)
  | 4, 9 => (9 : Fin 20)
  | 4, 10 => (6 : Fin 20)
  | 4, 11 => (15 : Fin 20)
  | 4, 12 => (7 : Fin 20)
  | 4, 13 => (8 : Fin 20)
  | 4, 14 => (14 : Fin 20)
  | 4, 15 => (11 : Fin 20)
  | 4, 16 => (17 : Fin 20)
  | 4, 17 => (16 : Fin 20)
  | 4, 18 => (19 : Fin 20)
  | 4, 19 => (18 : Fin 20)
  | 5, 0 => (1 : Fin 20)
  | 5, 1 => (3 : Fin 20)
  | 5, 2 => (4 : Fin 20)
  | 5, 3 => (0 : Fin 20)
  | 5, 4 => (5 : Fin 20)
  | 5, 5 => (2 : Fin 20)
  | 5, 6 => (7 : Fin 20)
  | 5, 7 => (12 : Fin 20)
  | 5, 8 => (11 : Fin 20)
  | 5, 9 => (8 : Fin 20)
  | 5, 10 => (10 : Fin 20)
  | 5, 11 => (9 : Fin 20)
  | 5, 12 => (6 : Fin 20)
  | 5, 13 => (15 : Fin 20)
  | 5, 14 => (13 : Fin 20)
  | 5, 15 => (14 : Fin 20)
  | 5, 16 => (17 : Fin 20)
  | 5, 17 => (18 : Fin 20)
  | 5, 18 => (16 : Fin 20)
  | 5, 19 => (19 : Fin 20)
  | 6, 0 => (0 : Fin 20)
  | 6, 1 => (6 : Fin 20)
  | 6, 2 => (7 : Fin 20)
  | 6, 3 => (2 : Fin 20)
  | 6, 4 => (8 : Fin 20)
  | 6, 5 => (9 : Fin 20)
  | 6, 6 => (11 : Fin 20)
  | 6, 7 => (3 : Fin 20)
  | 6, 8 => (10 : Fin 20)
  | 6, 9 => (14 : Fin 20)
  | 6, 10 => (4 : Fin 20)
  | 6, 11 => (1 : Fin 20)
  | 6, 12 => (15 : Fin 20)
  | 6, 13 => (12 : Fin 20)
  | 6, 14 => (5 : Fin 20)
  | 6, 15 => (13 : Fin 20)
  | 6, 16 => (16 : Fin 20)
  | 6, 17 => (19 : Fin 20)
  | 6, 18 => (17 : Fin 20)
  | 6, 19 => (18 : Fin 20)
  | 7, 0 => (0 : Fin 20)
  | 7, 1 => (6 : Fin 20)
  | 7, 2 => (12 : Fin 20)
  | 7, 3 => (4 : Fin 20)
  | 7, 4 => (15 : Fin 20)
  | 7, 5 => (14 : Fin 20)
  | 7, 6 => (16 : Fin 20)
  | 7, 7 => (17 : Fin 20)
  | 7, 8 => (7 : Fin 20)
  | 7, 9 => (5 : Fin 20)
  | 7, 10 => (18 : Fin 20)
  | 7, 11 => (11 : Fin 20)
  | 7, 12 => (19 : Fin 20)
  | 7, 13 => (10 : Fin 20)
  | 7, 14 => (9 : Fin 20)
  | 7, 15 => (3 : Fin 20)
  | 7, 16 => (1 : Fin 20)
  | 7, 17 => (8 : Fin 20)
  | 7, 18 => (13 : Fin 20)
  | 7, 19 => (2 : Fin 20)
  | _, _ => (0 : Fin 20)

@[reducible, expose]
public def m22L2Factor : Fin 8 -> Fin 20 -> List (Fin 6)
  | 0, 0 => [(0 : Fin 6)]
  | 0, 1 => []
  | 0, 2 => []
  | 0, 3 => [(0 : Fin 6)]
  | 0, 4 => [(0 : Fin 6)]
  | 0, 5 => [(0 : Fin 6)]
  | 0, 6 => []
  | 0, 7 => [(2 : Fin 6), (0 : Fin 6)]
  | 0, 8 => []
  | 0, 9 => [(1 : Fin 6), (0 : Fin 6), (4 : Fin 6)]
  | 0, 10 => []
  | 0, 11 => [(2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 0, 12 => [(0 : Fin 6), (5 : Fin 6)]
  | 0, 13 => []
  | 0, 14 => [(2 : Fin 6), (0 : Fin 6), (5 : Fin 6)]
  | 0, 15 => [(2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 0, 16 => []
  | 0, 17 => []
  | 0, 18 => [(2 : Fin 6), (0 : Fin 6)]
  | 0, 19 => [(0 : Fin 6), (5 : Fin 6)]
  | 1, 0 => []
  | 1, 1 => []
  | 1, 2 => []
  | 1, 3 => []
  | 1, 4 => []
  | 1, 5 => []
  | 1, 6 => [(2 : Fin 6), (1 : Fin 6)]
  | 1, 7 => [(0 : Fin 6), (1 : Fin 6), (0 : Fin 6)]
  | 1, 8 => [(0 : Fin 6), (4 : Fin 6)]
  | 1, 9 => []
  | 1, 10 => [(1 : Fin 6), (0 : Fin 6)]
  | 1, 11 => [(1 : Fin 6), (0 : Fin 6)]
  | 1, 12 => [(1 : Fin 6), (0 : Fin 6), (5 : Fin 6)]
  | 1, 13 => [(2 : Fin 6), (1 : Fin 6)]
  | 1, 14 => [(5 : Fin 6), (1 : Fin 6)]
  | 1, 15 => [(5 : Fin 6)]
  | 1, 16 => [(1 : Fin 6), (5 : Fin 6), (0 : Fin 6)]
  | 1, 17 => [(1 : Fin 6), (0 : Fin 6), (5 : Fin 6)]
  | 1, 18 => [(0 : Fin 6), (1 : Fin 6), (5 : Fin 6)]
  | 1, 19 => [(0 : Fin 6), (4 : Fin 6)]
  | 2, 0 => [(1 : Fin 6)]
  | 2, 1 => []
  | 2, 2 => [(0 : Fin 6), (4 : Fin 6)]
  | 2, 3 => [(1 : Fin 6), (0 : Fin 6)]
  | 2, 4 => [(1 : Fin 6)]
  | 2, 5 => [(0 : Fin 6), (2 : Fin 6), (1 : Fin 6)]
  | 2, 6 => []
  | 2, 7 => []
  | 2, 8 => []
  | 2, 9 => [(1 : Fin 6), (0 : Fin 6), (4 : Fin 6)]
  | 2, 10 => [(4 : Fin 6)]
  | 2, 11 => []
  | 2, 12 => [(2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 2, 13 => [(2 : Fin 6), (0 : Fin 6), (4 : Fin 6)]
  | 2, 14 => [(2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 2, 15 => [(0 : Fin 6), (5 : Fin 6), (1 : Fin 6)]
  | 2, 16 => [(2 : Fin 6), (0 : Fin 6)]
  | 2, 17 => [(2 : Fin 6), (0 : Fin 6)]
  | 2, 18 => [(0 : Fin 6), (5 : Fin 6)]
  | 2, 19 => []
  | 3, 0 => [(2 : Fin 6)]
  | 3, 1 => [(0 : Fin 6), (5 : Fin 6)]
  | 3, 2 => []
  | 3, 3 => [(0 : Fin 6), (1 : Fin 6), (5 : Fin 6)]
  | 3, 4 => [(2 : Fin 6), (4 : Fin 6), (0 : Fin 6)]
  | 3, 5 => [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | 3, 6 => [(2 : Fin 6), (0 : Fin 6)]
  | 3, 7 => [(4 : Fin 6), (2 : Fin 6), (0 : Fin 6)]
  | 3, 8 => [(0 : Fin 6), (5 : Fin 6), (1 : Fin 6)]
  | 3, 9 => [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | 3, 10 => [(4 : Fin 6), (2 : Fin 6), (0 : Fin 6)]
  | 3, 11 => [(0 : Fin 6), (5 : Fin 6)]
  | 3, 12 => []
  | 3, 13 => [(0 : Fin 6), (5 : Fin 6), (1 : Fin 6)]
  | 3, 14 => []
  | 3, 15 => []
  | 3, 16 => []
  | 3, 17 => []
  | 3, 18 => []
  | 3, 19 => []
  | 4, 0 => [(0 : Fin 6)]
  | 4, 1 => []
  | 4, 2 => []
  | 4, 3 => [(0 : Fin 6)]
  | 4, 4 => [(0 : Fin 6)]
  | 4, 5 => [(0 : Fin 6)]
  | 4, 6 => []
  | 4, 7 => [(2 : Fin 6), (0 : Fin 6)]
  | 4, 8 => []
  | 4, 9 => [(1 : Fin 6), (0 : Fin 6), (4 : Fin 6)]
  | 4, 10 => []
  | 4, 11 => [(2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 4, 12 => [(0 : Fin 6), (5 : Fin 6)]
  | 4, 13 => []
  | 4, 14 => [(2 : Fin 6), (0 : Fin 6), (5 : Fin 6)]
  | 4, 15 => [(2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 4, 16 => []
  | 4, 17 => []
  | 4, 18 => [(2 : Fin 6), (0 : Fin 6)]
  | 4, 19 => [(0 : Fin 6), (5 : Fin 6)]
  | 5, 0 => []
  | 5, 1 => []
  | 5, 2 => []
  | 5, 3 => []
  | 5, 4 => []
  | 5, 5 => []
  | 5, 6 => [(0 : Fin 6), (4 : Fin 6), (0 : Fin 6)]
  | 5, 7 => [(2 : Fin 6), (0 : Fin 6), (4 : Fin 6)]
  | 5, 8 => [(0 : Fin 6), (4 : Fin 6)]
  | 5, 9 => [(1 : Fin 6), (0 : Fin 6)]
  | 5, 10 => [(0 : Fin 6), (4 : Fin 6)]
  | 5, 11 => []
  | 5, 12 => [(2 : Fin 6), (1 : Fin 6)]
  | 5, 13 => [(2 : Fin 6)]
  | 5, 14 => [(2 : Fin 6), (1 : Fin 6)]
  | 5, 15 => [(4 : Fin 6), (2 : Fin 6)]
  | 5, 16 => [(2 : Fin 6), (0 : Fin 6), (4 : Fin 6)]
  | 5, 17 => [(2 : Fin 6), (4 : Fin 6), (0 : Fin 6)]
  | 5, 18 => [(0 : Fin 6), (2 : Fin 6), (4 : Fin 6)]
  | 5, 19 => [(1 : Fin 6), (0 : Fin 6)]
  | 6, 0 => [(4 : Fin 6)]
  | 6, 1 => []
  | 6, 2 => []
  | 6, 3 => [(1 : Fin 6), (0 : Fin 6)]
  | 6, 4 => []
  | 6, 5 => [(1 : Fin 6), (0 : Fin 6), (4 : Fin 6)]
  | 6, 6 => []
  | 6, 7 => [(0 : Fin 6), (4 : Fin 6)]
  | 6, 8 => [(1 : Fin 6)]
  | 6, 9 => [(2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 6, 10 => [(4 : Fin 6)]
  | 6, 11 => []
  | 6, 12 => [(4 : Fin 6), (2 : Fin 6), (0 : Fin 6)]
  | 6, 13 => [(2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 6, 14 => [(0 : Fin 6), (2 : Fin 6), (1 : Fin 6)]
  | 6, 15 => [(1 : Fin 6), (0 : Fin 6), (5 : Fin 6)]
  | 6, 16 => [(0 : Fin 6), (5 : Fin 6)]
  | 6, 17 => []
  | 6, 18 => [(0 : Fin 6), (5 : Fin 6)]
  | 6, 19 => [(2 : Fin 6), (0 : Fin 6)]
  | 7, 0 => [(5 : Fin 6)]
  | 7, 1 => [(0 : Fin 6), (5 : Fin 6)]
  | 7, 2 => []
  | 7, 3 => [(0 : Fin 6), (1 : Fin 6), (5 : Fin 6)]
  | 7, 4 => []
  | 7, 5 => []
  | 7, 6 => []
  | 7, 7 => []
  | 7, 8 => [(0 : Fin 6), (5 : Fin 6), (1 : Fin 6)]
  | 7, 9 => [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | 7, 10 => []
  | 7, 11 => [(2 : Fin 6), (0 : Fin 6)]
  | 7, 12 => []
  | 7, 13 => [(0 : Fin 6), (5 : Fin 6), (1 : Fin 6)]
  | 7, 14 => [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | 7, 15 => [(2 : Fin 6), (4 : Fin 6), (0 : Fin 6)]
  | 7, 16 => [(2 : Fin 6), (0 : Fin 6)]
  | 7, 17 => [(4 : Fin 6), (2 : Fin 6), (0 : Fin 6)]
  | 7, 18 => [(4 : Fin 6), (2 : Fin 6), (0 : Fin 6)]
  | 7, 19 => []
  | _, _ => [(0 : Fin 6)]

public theorem m22L2RepBase : m22L2Rep (0 : Fin 20) = 1 := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

public theorem m22L2RepPoint : (r : Fin 20) -> m22L2Rep r (3 : Fin 22) = m22L2Point r := by
  intro r
  fin_cases r <;> rfl

@[reducible, expose]
public def m22L2PointInv : Fin 22 -> Fin 20
  | 0 => (1 : Fin 20)
  | 1 => (0 : Fin 20)
  | 2 => (0 : Fin 20)
  | 3 => (0 : Fin 20)
  | 4 => (11 : Fin 20)
  | 5 => (10 : Fin 20)
  | 6 => (6 : Fin 20)
  | 7 => (4 : Fin 20)
  | 8 => (8 : Fin 20)
  | 9 => (2 : Fin 20)
  | 10 => (5 : Fin 20)
  | 11 => (16 : Fin 20)
  | 12 => (19 : Fin 20)
  | 13 => (17 : Fin 20)
  | 14 => (7 : Fin 20)
  | 15 => (15 : Fin 20)
  | 16 => (18 : Fin 20)
  | 17 => (13 : Fin 20)
  | 18 => (14 : Fin 20)
  | 19 => (12 : Fin 20)
  | 20 => (9 : Fin 20)
  | 21 => (3 : Fin 20)
  | _ => (1 : Fin 20)

public theorem m22L2PointInv_left : (r : Fin 20) -> m22L2PointInv (m22L2Point r) = r := by
  intro r
  fin_cases r <;> rfl

public theorem m22L2Point_injective : Function.Injective m22L2Point := by
  intro x y h
  have hh := congrArg m22L2PointInv h
  simpa [m22L2PointInv_left] using hh

end Sporadic.Mathieu
