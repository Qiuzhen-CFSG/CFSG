module

public import Theory.Mathieu.M22.Properties.OrderCertificate
import Mathlib.Tactic.FinCases

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise
@[reducible, expose]
public def m22L3R0To : Fin 22 -> Fin 22 := id

@[reducible, expose]
public def m22L3R0InvFun : Fin 22 -> Fin 22 := id

public theorem m22L3R0_left : forall x, m22L3R0InvFun (m22L3R0To x) = x := by
  intro x
  rfl

public theorem m22L3R0_right : forall x, m22L3R0To (m22L3R0InvFun x) = x := by
  intro x
  rfl

@[reducible, expose]
public def m22L3R0 : Equiv.Perm (Fin 22) := Equiv.refl _

@[reducible, expose]
public def m22L3R1To : Fin 22 -> Fin 22 :=
  m22L3G0To

@[reducible, expose]
public def m22L3R1InvFun : Fin 22 -> Fin 22 :=
  m22L3G0InvFun

public theorem m22L3R1_left : forall x, m22L3R1InvFun (m22L3R1To x) = x :=
  m22L3G0_left

public theorem m22L3R1_right : forall x, m22L3R1To (m22L3R1InvFun x) = x :=
  m22L3G0_right

@[reducible, expose]
public def m22L3R1 : Equiv.Perm (Fin 22) :=
  m22L3G0

@[reducible, expose]
public def m22L3R2To : Fin 22 -> Fin 22
  | 0 => (4 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (0 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (11 : Fin 22)
  | 7 => (17 : Fin 22)
  | 8 => (21 : Fin 22)
  | 9 => (15 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (6 : Fin 22)
  | 12 => (14 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (12 : Fin 22)
  | 15 => (9 : Fin 22)
  | 16 => (19 : Fin 22)
  | 17 => (7 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (16 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (8 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R2InvFun : Fin 22 -> Fin 22
  | 0 => (4 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (0 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (11 : Fin 22)
  | 7 => (17 : Fin 22)
  | 8 => (21 : Fin 22)
  | 9 => (15 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (6 : Fin 22)
  | 12 => (14 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (12 : Fin 22)
  | 15 => (9 : Fin 22)
  | 16 => (19 : Fin 22)
  | 17 => (7 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (16 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (8 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R2_left : forall x, m22L3R2InvFun (m22L3R2To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R2_right : forall x, m22L3R2To (m22L3R2InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R2_left

@[reducible, expose]
public def m22L3R2 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R2To m22L3R2InvFun m22L3R2_left m22L3R2_right

@[reducible, expose]
public def m22L3R3To : Fin 22 -> Fin 22
  | 0 => (7 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (17 : Fin 22)
  | 5 => (16 : Fin 22)
  | 6 => (12 : Fin 22)
  | 7 => (0 : Fin 22)
  | 8 => (15 : Fin 22)
  | 9 => (21 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (14 : Fin 22)
  | 12 => (6 : Fin 22)
  | 13 => (19 : Fin 22)
  | 14 => (11 : Fin 22)
  | 15 => (8 : Fin 22)
  | 16 => (5 : Fin 22)
  | 17 => (4 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (13 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (9 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R3InvFun : Fin 22 -> Fin 22
  | 0 => (7 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (17 : Fin 22)
  | 5 => (16 : Fin 22)
  | 6 => (12 : Fin 22)
  | 7 => (0 : Fin 22)
  | 8 => (15 : Fin 22)
  | 9 => (21 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (14 : Fin 22)
  | 12 => (6 : Fin 22)
  | 13 => (19 : Fin 22)
  | 14 => (11 : Fin 22)
  | 15 => (8 : Fin 22)
  | 16 => (5 : Fin 22)
  | 17 => (4 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (13 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (9 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R3_left : forall x, m22L3R3InvFun (m22L3R3To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R3_right : forall x, m22L3R3To (m22L3R3InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R3_left

@[reducible, expose]
public def m22L3R3 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R3To m22L3R3InvFun m22L3R3_left m22L3R3_right

@[reducible, expose]
public def m22L3R4To : Fin 22 -> Fin 22
  | 0 => (15 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (9 : Fin 22)
  | 5 => (11 : Fin 22)
  | 6 => (13 : Fin 22)
  | 7 => (8 : Fin 22)
  | 8 => (7 : Fin 22)
  | 9 => (4 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (5 : Fin 22)
  | 12 => (19 : Fin 22)
  | 13 => (6 : Fin 22)
  | 14 => (16 : Fin 22)
  | 15 => (0 : Fin 22)
  | 16 => (14 : Fin 22)
  | 17 => (21 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (12 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (17 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R4InvFun : Fin 22 -> Fin 22
  | 0 => (15 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (9 : Fin 22)
  | 5 => (11 : Fin 22)
  | 6 => (13 : Fin 22)
  | 7 => (8 : Fin 22)
  | 8 => (7 : Fin 22)
  | 9 => (4 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (5 : Fin 22)
  | 12 => (19 : Fin 22)
  | 13 => (6 : Fin 22)
  | 14 => (16 : Fin 22)
  | 15 => (0 : Fin 22)
  | 16 => (14 : Fin 22)
  | 17 => (21 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (12 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (17 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R4_left : forall x, m22L3R4InvFun (m22L3R4To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R4_right : forall x, m22L3R4To (m22L3R4InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R4_left

@[reducible, expose]
public def m22L3R4 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R4To m22L3R4InvFun m22L3R4_left m22L3R4_right

@[reducible, expose]
public def m22L3R5To : Fin 22 -> Fin 22
  | 0 => (11 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (6 : Fin 22)
  | 5 => (15 : Fin 22)
  | 6 => (4 : Fin 22)
  | 7 => (14 : Fin 22)
  | 8 => (16 : Fin 22)
  | 9 => (13 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (0 : Fin 22)
  | 12 => (17 : Fin 22)
  | 13 => (9 : Fin 22)
  | 14 => (7 : Fin 22)
  | 15 => (5 : Fin 22)
  | 16 => (8 : Fin 22)
  | 17 => (12 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (21 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (19 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R5InvFun : Fin 22 -> Fin 22
  | 0 => (11 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (6 : Fin 22)
  | 5 => (15 : Fin 22)
  | 6 => (4 : Fin 22)
  | 7 => (14 : Fin 22)
  | 8 => (16 : Fin 22)
  | 9 => (13 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (0 : Fin 22)
  | 12 => (17 : Fin 22)
  | 13 => (9 : Fin 22)
  | 14 => (7 : Fin 22)
  | 15 => (5 : Fin 22)
  | 16 => (8 : Fin 22)
  | 17 => (12 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (21 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (19 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R5_left : forall x, m22L3R5InvFun (m22L3R5To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R5_right : forall x, m22L3R5To (m22L3R5InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R5_left

@[reducible, expose]
public def m22L3R5 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R5To m22L3R5InvFun m22L3R5_left m22L3R5_right

@[reducible, expose]
public def m22L3R6To : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (8 : Fin 22)
  | 5 => (12 : Fin 22)
  | 6 => (16 : Fin 22)
  | 7 => (9 : Fin 22)
  | 8 => (4 : Fin 22)
  | 9 => (7 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (19 : Fin 22)
  | 12 => (5 : Fin 22)
  | 13 => (14 : Fin 22)
  | 14 => (13 : Fin 22)
  | 15 => (17 : Fin 22)
  | 16 => (6 : Fin 22)
  | 17 => (15 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (11 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R6InvFun : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (8 : Fin 22)
  | 5 => (12 : Fin 22)
  | 6 => (16 : Fin 22)
  | 7 => (9 : Fin 22)
  | 8 => (4 : Fin 22)
  | 9 => (7 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (19 : Fin 22)
  | 12 => (5 : Fin 22)
  | 13 => (14 : Fin 22)
  | 14 => (13 : Fin 22)
  | 15 => (17 : Fin 22)
  | 16 => (6 : Fin 22)
  | 17 => (15 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (11 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R6_left : forall x, m22L3R6InvFun (m22L3R6To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R6_right : forall x, m22L3R6To (m22L3R6InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R6_left

@[reducible, expose]
public def m22L3R6 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R6To m22L3R6InvFun m22L3R6_left m22L3R6_right

@[reducible, expose]
public def m22L3R7To : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (19 : Fin 22)
  | 5 => (7 : Fin 22)
  | 6 => (21 : Fin 22)
  | 7 => (5 : Fin 22)
  | 8 => (11 : Fin 22)
  | 9 => (12 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (8 : Fin 22)
  | 12 => (9 : Fin 22)
  | 13 => (17 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (13 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (4 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (6 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R7InvFun : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (19 : Fin 22)
  | 5 => (7 : Fin 22)
  | 6 => (21 : Fin 22)
  | 7 => (5 : Fin 22)
  | 8 => (11 : Fin 22)
  | 9 => (12 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (8 : Fin 22)
  | 12 => (9 : Fin 22)
  | 13 => (17 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (13 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (4 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (6 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R7_left : forall x, m22L3R7InvFun (m22L3R7To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R7_right : forall x, m22L3R7To (m22L3R7InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R7_left

@[reducible, expose]
public def m22L3R7 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R7To m22L3R7InvFun m22L3R7_left m22L3R7_right

@[reducible, expose]
public def m22L3R8To : Fin 22 -> Fin 22
  | 0 => (12 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (14 : Fin 22)
  | 5 => (21 : Fin 22)
  | 6 => (7 : Fin 22)
  | 7 => (6 : Fin 22)
  | 8 => (13 : Fin 22)
  | 9 => (16 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (17 : Fin 22)
  | 12 => (0 : Fin 22)
  | 13 => (8 : Fin 22)
  | 14 => (4 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (9 : Fin 22)
  | 17 => (11 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (5 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R8InvFun : Fin 22 -> Fin 22
  | 0 => (12 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (14 : Fin 22)
  | 5 => (21 : Fin 22)
  | 6 => (7 : Fin 22)
  | 7 => (6 : Fin 22)
  | 8 => (13 : Fin 22)
  | 9 => (16 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (17 : Fin 22)
  | 12 => (0 : Fin 22)
  | 13 => (8 : Fin 22)
  | 14 => (4 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (9 : Fin 22)
  | 17 => (11 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (5 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R8_left : forall x, m22L3R8InvFun (m22L3R8To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R8_right : forall x, m22L3R8To (m22L3R8InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R8_left

@[reducible, expose]
public def m22L3R8 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R8To m22L3R8InvFun m22L3R8_left m22L3R8_right

@[reducible, expose]
public def m22L3R9To : Fin 22 -> Fin 22
  | 0 => (13 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (15 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (12 : Fin 22)
  | 9 => (11 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (9 : Fin 22)
  | 12 => (8 : Fin 22)
  | 13 => (0 : Fin 22)
  | 14 => (21 : Fin 22)
  | 15 => (6 : Fin 22)
  | 16 => (17 : Fin 22)
  | 17 => (16 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (14 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R9InvFun : Fin 22 -> Fin 22
  | 0 => (13 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (15 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (12 : Fin 22)
  | 9 => (11 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (9 : Fin 22)
  | 12 => (8 : Fin 22)
  | 13 => (0 : Fin 22)
  | 14 => (21 : Fin 22)
  | 15 => (6 : Fin 22)
  | 16 => (17 : Fin 22)
  | 17 => (16 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (14 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R9_left : forall x, m22L3R9InvFun (m22L3R9To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R9_right : forall x, m22L3R9To (m22L3R9InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R9_left

@[reducible, expose]
public def m22L3R9 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R9To m22L3R9InvFun m22L3R9_left m22L3R9_right

@[reducible, expose]
public def m22L3R10To : Fin 22 -> Fin 22
  | 0 => (8 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (21 : Fin 22)
  | 5 => (14 : Fin 22)
  | 6 => (19 : Fin 22)
  | 7 => (15 : Fin 22)
  | 8 => (0 : Fin 22)
  | 9 => (17 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (5 : Fin 22)
  | 15 => (7 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (9 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (6 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (4 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R10InvFun : Fin 22 -> Fin 22
  | 0 => (8 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (21 : Fin 22)
  | 5 => (14 : Fin 22)
  | 6 => (19 : Fin 22)
  | 7 => (15 : Fin 22)
  | 8 => (0 : Fin 22)
  | 9 => (17 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (16 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (5 : Fin 22)
  | 15 => (7 : Fin 22)
  | 16 => (11 : Fin 22)
  | 17 => (9 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (6 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (4 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R10_left : forall x, m22L3R10InvFun (m22L3R10To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R10_right : forall x, m22L3R10To (m22L3R10InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R10_left

@[reducible, expose]
public def m22L3R10 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R10To m22L3R10InvFun m22L3R10_left m22L3R10_right

@[reducible, expose]
public def m22L3R11To : Fin 22 -> Fin 22
  | 0 => (17 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (7 : Fin 22)
  | 5 => (19 : Fin 22)
  | 6 => (14 : Fin 22)
  | 7 => (4 : Fin 22)
  | 8 => (9 : Fin 22)
  | 9 => (8 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (12 : Fin 22)
  | 12 => (11 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (6 : Fin 22)
  | 15 => (21 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (0 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (5 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (15 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R11InvFun : Fin 22 -> Fin 22
  | 0 => (17 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (7 : Fin 22)
  | 5 => (19 : Fin 22)
  | 6 => (14 : Fin 22)
  | 7 => (4 : Fin 22)
  | 8 => (9 : Fin 22)
  | 9 => (8 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (12 : Fin 22)
  | 12 => (11 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (6 : Fin 22)
  | 15 => (21 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (0 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (5 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (15 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R11_left : forall x, m22L3R11InvFun (m22L3R11To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R11_right : forall x, m22L3R11To (m22L3R11InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R11_left

@[reducible, expose]
public def m22L3R11 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R11To m22L3R11InvFun m22L3R11_left m22L3R11_right

@[reducible, expose]
public def m22L3R12To : Fin 22 -> Fin 22
  | 0 => (6 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (11 : Fin 22)
  | 5 => (9 : Fin 22)
  | 6 => (0 : Fin 22)
  | 7 => (12 : Fin 22)
  | 8 => (19 : Fin 22)
  | 9 => (5 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (4 : Fin 22)
  | 12 => (7 : Fin 22)
  | 13 => (15 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (13 : Fin 22)
  | 16 => (21 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (8 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (16 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R12InvFun : Fin 22 -> Fin 22
  | 0 => (6 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (11 : Fin 22)
  | 5 => (9 : Fin 22)
  | 6 => (0 : Fin 22)
  | 7 => (12 : Fin 22)
  | 8 => (19 : Fin 22)
  | 9 => (5 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (4 : Fin 22)
  | 12 => (7 : Fin 22)
  | 13 => (15 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (13 : Fin 22)
  | 16 => (21 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (8 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (16 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R12_left : forall x, m22L3R12InvFun (m22L3R12To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R12_right : forall x, m22L3R12To (m22L3R12InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R12_left

@[reducible, expose]
public def m22L3R12 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R12To m22L3R12InvFun m22L3R12_left m22L3R12_right

@[reducible, expose]
public def m22L3R13To : Fin 22 -> Fin 22
  | 0 => (14 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (12 : Fin 22)
  | 5 => (8 : Fin 22)
  | 6 => (17 : Fin 22)
  | 7 => (11 : Fin 22)
  | 8 => (5 : Fin 22)
  | 9 => (19 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (7 : Fin 22)
  | 12 => (4 : Fin 22)
  | 13 => (21 : Fin 22)
  | 14 => (0 : Fin 22)
  | 15 => (16 : Fin 22)
  | 16 => (15 : Fin 22)
  | 17 => (6 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (9 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (13 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R13InvFun : Fin 22 -> Fin 22
  | 0 => (14 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (12 : Fin 22)
  | 5 => (8 : Fin 22)
  | 6 => (17 : Fin 22)
  | 7 => (11 : Fin 22)
  | 8 => (5 : Fin 22)
  | 9 => (19 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (7 : Fin 22)
  | 12 => (4 : Fin 22)
  | 13 => (21 : Fin 22)
  | 14 => (0 : Fin 22)
  | 15 => (16 : Fin 22)
  | 16 => (15 : Fin 22)
  | 17 => (6 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (9 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (13 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R13_left : forall x, m22L3R13InvFun (m22L3R13To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R13_right : forall x, m22L3R13To (m22L3R13InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R13_left

@[reducible, expose]
public def m22L3R13 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R13To m22L3R13InvFun m22L3R13_left m22L3R13_right

@[reducible, expose]
public def m22L3R14To : Fin 22 -> Fin 22
  | 0 => (5 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (13 : Fin 22)
  | 5 => (0 : Fin 22)
  | 6 => (9 : Fin 22)
  | 7 => (16 : Fin 22)
  | 8 => (14 : Fin 22)
  | 9 => (6 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (15 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (4 : Fin 22)
  | 14 => (8 : Fin 22)
  | 15 => (11 : Fin 22)
  | 16 => (7 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R14InvFun : Fin 22 -> Fin 22
  | 0 => (5 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (13 : Fin 22)
  | 5 => (0 : Fin 22)
  | 6 => (9 : Fin 22)
  | 7 => (16 : Fin 22)
  | 8 => (14 : Fin 22)
  | 9 => (6 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (15 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (4 : Fin 22)
  | 14 => (8 : Fin 22)
  | 15 => (11 : Fin 22)
  | 16 => (7 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R14_left : forall x, m22L3R14InvFun (m22L3R14To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R14_right : forall x, m22L3R14To (m22L3R14InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R14_left

@[reducible, expose]
public def m22L3R14 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R14To m22L3R14InvFun m22L3R14_left m22L3R14_right

@[reducible, expose]
public def m22L3R15To : Fin 22 -> Fin 22
  | 0 => (19 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (16 : Fin 22)
  | 5 => (17 : Fin 22)
  | 6 => (8 : Fin 22)
  | 7 => (13 : Fin 22)
  | 8 => (6 : Fin 22)
  | 9 => (14 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (21 : Fin 22)
  | 12 => (15 : Fin 22)
  | 13 => (7 : Fin 22)
  | 14 => (9 : Fin 22)
  | 15 => (12 : Fin 22)
  | 16 => (4 : Fin 22)
  | 17 => (5 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (0 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (11 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L3R15InvFun : Fin 22 -> Fin 22
  | 0 => (19 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (16 : Fin 22)
  | 5 => (17 : Fin 22)
  | 6 => (8 : Fin 22)
  | 7 => (13 : Fin 22)
  | 8 => (6 : Fin 22)
  | 9 => (14 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (21 : Fin 22)
  | 12 => (15 : Fin 22)
  | 13 => (7 : Fin 22)
  | 14 => (9 : Fin 22)
  | 15 => (12 : Fin 22)
  | 16 => (4 : Fin 22)
  | 17 => (5 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (0 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (11 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L3R15_left : forall x, m22L3R15InvFun (m22L3R15To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L3R15_right : forall x, m22L3R15To (m22L3R15InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L3R15_left

@[reducible, expose]
public def m22L3R15 : Equiv.Perm (Fin 22) :=
  tablePerm m22L3R15To m22L3R15InvFun m22L3R15_left m22L3R15_right

@[reducible, expose]
public def m22L3RepWord : Fin 16 -> List (Fin 6)
  | 0 => []
  | 1 => [(0 : Fin 6)]
  | 2 => [(2 : Fin 6), (1 : Fin 6)]
  | 3 => [(2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 4 => [(0 : Fin 6), (2 : Fin 6), (1 : Fin 6)]
  | 5 => [(1 : Fin 6), (2 : Fin 6)]
  | 6 => [(0 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 7 => [(1 : Fin 6), (0 : Fin 6), (2 : Fin 6)]
  | 8 => [(0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (2 : Fin 6)]
  | 9 => [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | 10 => [(1 : Fin 6), (0 : Fin 6), (4 : Fin 6)]
  | 11 => [(2 : Fin 6), (0 : Fin 6), (5 : Fin 6)]
  | 12 => [(1 : Fin 6), (5 : Fin 6), (1 : Fin 6)]
  | 13 => [(1 : Fin 6), (5 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 14 => [(0 : Fin 6), (1 : Fin 6), (5 : Fin 6), (1 : Fin 6)]
  | 15 => [(1 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6)]
  | _ => []

@[reducible, expose]
public def m22L3Rep : Fin 16 -> Equiv.Perm (Fin 22)
  | 0 => m22L3R0
  | 1 => m22L3R1
  | 2 => m22L3R2
  | 3 => m22L3R3
  | 4 => m22L3R4
  | 5 => m22L3R5
  | 6 => m22L3R6
  | 7 => m22L3R7
  | 8 => m22L3R8
  | 9 => m22L3R9
  | 10 => m22L3R10
  | 11 => m22L3R11
  | 12 => m22L3R12
  | 13 => m22L3R13
  | 14 => m22L3R14
  | 15 => m22L3R15
  | _ => m22L3R0

public theorem m22L3Rep_eq_word : (r : Fin 16) -> m22L3Rep r = evalWord m22L3Gen (m22L3RepWord r) := by
  intro r
  fin_cases r <;> apply Equiv.ext <;> intro x <;> fin_cases x <;> rfl

@[reducible, expose]
public def m22L3Point : Fin 16 -> Fin 22
  | 0 => (4 : Fin 22)
  | 1 => (15 : Fin 22)
  | 2 => (0 : Fin 22)
  | 3 => (17 : Fin 22)
  | 4 => (9 : Fin 22)
  | 5 => (6 : Fin 22)
  | 6 => (8 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (14 : Fin 22)
  | 9 => (5 : Fin 22)
  | 10 => (21 : Fin 22)
  | 11 => (7 : Fin 22)
  | 12 => (11 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (13 : Fin 22)
  | 15 => (16 : Fin 22)
  | _ => (4 : Fin 22)

@[reducible, expose]
public def m22L3Act : Fin 6 -> Fin 16 -> Fin 16
  | 0, 0 => (1 : Fin 16)
  | 0, 1 => (0 : Fin 16)
  | 0, 2 => (4 : Fin 16)
  | 0, 3 => (6 : Fin 16)
  | 0, 4 => (2 : Fin 16)
  | 0, 5 => (9 : Fin 16)
  | 0, 6 => (3 : Fin 16)
  | 0, 7 => (8 : Fin 16)
  | 0, 8 => (7 : Fin 16)
  | 0, 9 => (5 : Fin 16)
  | 0, 10 => (11 : Fin 16)
  | 0, 11 => (10 : Fin 16)
  | 0, 12 => (14 : Fin 16)
  | 0, 13 => (15 : Fin 16)
  | 0, 14 => (12 : Fin 16)
  | 0, 15 => (13 : Fin 16)
  | 1, 0 => (5 : Fin 16)
  | 1, 1 => (7 : Fin 16)
  | 1, 2 => (0 : Fin 16)
  | 1, 3 => (1 : Fin 16)
  | 1, 4 => (10 : Fin 16)
  | 1, 5 => (2 : Fin 16)
  | 1, 6 => (11 : Fin 16)
  | 1, 7 => (3 : Fin 16)
  | 1, 8 => (4 : Fin 16)
  | 1, 9 => (6 : Fin 16)
  | 1, 10 => (8 : Fin 16)
  | 1, 11 => (9 : Fin 16)
  | 1, 12 => (12 : Fin 16)
  | 1, 13 => (14 : Fin 16)
  | 1, 14 => (15 : Fin 16)
  | 1, 15 => (13 : Fin 16)
  | 2, 0 => (0 : Fin 16)
  | 2, 1 => (11 : Fin 16)
  | 2, 2 => (12 : Fin 16)
  | 2, 3 => (15 : Fin 16)
  | 2, 4 => (13 : Fin 16)
  | 2, 5 => (2 : Fin 16)
  | 2, 6 => (14 : Fin 16)
  | 2, 7 => (4 : Fin 16)
  | 2, 8 => (6 : Fin 16)
  | 2, 9 => (3 : Fin 16)
  | 2, 10 => (1 : Fin 16)
  | 2, 11 => (10 : Fin 16)
  | 2, 12 => (5 : Fin 16)
  | 2, 13 => (7 : Fin 16)
  | 2, 14 => (8 : Fin 16)
  | 2, 15 => (9 : Fin 16)
  | 3, 0 => (1 : Fin 16)
  | 3, 1 => (0 : Fin 16)
  | 3, 2 => (4 : Fin 16)
  | 3, 3 => (6 : Fin 16)
  | 3, 4 => (2 : Fin 16)
  | 3, 5 => (9 : Fin 16)
  | 3, 6 => (3 : Fin 16)
  | 3, 7 => (8 : Fin 16)
  | 3, 8 => (7 : Fin 16)
  | 3, 9 => (5 : Fin 16)
  | 3, 10 => (11 : Fin 16)
  | 3, 11 => (10 : Fin 16)
  | 3, 12 => (14 : Fin 16)
  | 3, 13 => (15 : Fin 16)
  | 3, 14 => (12 : Fin 16)
  | 3, 15 => (13 : Fin 16)
  | 4, 0 => (2 : Fin 16)
  | 4, 1 => (3 : Fin 16)
  | 4, 2 => (5 : Fin 16)
  | 4, 3 => (7 : Fin 16)
  | 4, 4 => (8 : Fin 16)
  | 4, 5 => (0 : Fin 16)
  | 4, 6 => (9 : Fin 16)
  | 4, 7 => (1 : Fin 16)
  | 4, 8 => (10 : Fin 16)
  | 4, 9 => (11 : Fin 16)
  | 4, 10 => (4 : Fin 16)
  | 4, 11 => (6 : Fin 16)
  | 4, 12 => (12 : Fin 16)
  | 4, 13 => (15 : Fin 16)
  | 4, 14 => (13 : Fin 16)
  | 4, 15 => (14 : Fin 16)
  | 5, 0 => (0 : Fin 16)
  | 5, 1 => (10 : Fin 16)
  | 5, 2 => (5 : Fin 16)
  | 5, 3 => (9 : Fin 16)
  | 5, 4 => (7 : Fin 16)
  | 5, 5 => (12 : Fin 16)
  | 5, 6 => (8 : Fin 16)
  | 5, 7 => (13 : Fin 16)
  | 5, 8 => (14 : Fin 16)
  | 5, 9 => (15 : Fin 16)
  | 5, 10 => (11 : Fin 16)
  | 5, 11 => (1 : Fin 16)
  | 5, 12 => (2 : Fin 16)
  | 5, 13 => (4 : Fin 16)
  | 5, 14 => (6 : Fin 16)
  | 5, 15 => (3 : Fin 16)
  | _, _ => (1 : Fin 16)

@[reducible, expose]
public def m22L3Factor : Fin 6 -> Fin 16 -> List (Fin 2)
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
  | 1, 0 => [(1 : Fin 2)]
  | 1, 1 => [(1 : Fin 2)]
  | 1, 2 => [(1 : Fin 2)]
  | 1, 3 => [(1 : Fin 2)]
  | 1, 4 => [(1 : Fin 2)]
  | 1, 5 => [(1 : Fin 2)]
  | 1, 6 => [(1 : Fin 2)]
  | 1, 7 => [(1 : Fin 2)]
  | 1, 8 => [(1 : Fin 2)]
  | 1, 9 => [(1 : Fin 2)]
  | 1, 10 => [(1 : Fin 2)]
  | 1, 11 => [(1 : Fin 2)]
  | 1, 12 => [(1 : Fin 2)]
  | 1, 13 => [(1 : Fin 2)]
  | 1, 14 => [(1 : Fin 2)]
  | 1, 15 => [(1 : Fin 2)]
  | 2, 0 => [(0 : Fin 2)]
  | 2, 1 => [(0 : Fin 2)]
  | 2, 2 => [(0 : Fin 2)]
  | 2, 3 => [(0 : Fin 2)]
  | 2, 4 => [(0 : Fin 2)]
  | 2, 5 => [(0 : Fin 2)]
  | 2, 6 => [(0 : Fin 2)]
  | 2, 7 => [(0 : Fin 2)]
  | 2, 8 => [(0 : Fin 2)]
  | 2, 9 => [(0 : Fin 2)]
  | 2, 10 => [(0 : Fin 2)]
  | 2, 11 => [(0 : Fin 2)]
  | 2, 12 => [(0 : Fin 2)]
  | 2, 13 => [(0 : Fin 2)]
  | 2, 14 => [(0 : Fin 2)]
  | 2, 15 => [(0 : Fin 2)]
  | 3, 0 => []
  | 3, 1 => []
  | 3, 2 => []
  | 3, 3 => []
  | 3, 4 => []
  | 3, 5 => []
  | 3, 6 => []
  | 3, 7 => []
  | 3, 8 => []
  | 3, 9 => []
  | 3, 10 => []
  | 3, 11 => []
  | 3, 12 => []
  | 3, 13 => []
  | 3, 14 => []
  | 3, 15 => []
  | 4, 0 => [(0 : Fin 2)]
  | 4, 1 => [(0 : Fin 2)]
  | 4, 2 => [(0 : Fin 2)]
  | 4, 3 => [(0 : Fin 2)]
  | 4, 4 => [(0 : Fin 2)]
  | 4, 5 => [(0 : Fin 2)]
  | 4, 6 => [(0 : Fin 2)]
  | 4, 7 => [(0 : Fin 2)]
  | 4, 8 => [(0 : Fin 2)]
  | 4, 9 => [(0 : Fin 2)]
  | 4, 10 => [(0 : Fin 2)]
  | 4, 11 => [(0 : Fin 2)]
  | 4, 12 => [(0 : Fin 2)]
  | 4, 13 => [(0 : Fin 2)]
  | 4, 14 => [(0 : Fin 2)]
  | 4, 15 => [(0 : Fin 2)]
  | 5, 0 => [(1 : Fin 2)]
  | 5, 1 => [(1 : Fin 2)]
  | 5, 2 => [(1 : Fin 2)]
  | 5, 3 => [(1 : Fin 2)]
  | 5, 4 => [(1 : Fin 2)]
  | 5, 5 => [(1 : Fin 2)]
  | 5, 6 => [(1 : Fin 2)]
  | 5, 7 => [(1 : Fin 2)]
  | 5, 8 => [(1 : Fin 2)]
  | 5, 9 => [(1 : Fin 2)]
  | 5, 10 => [(1 : Fin 2)]
  | 5, 11 => [(1 : Fin 2)]
  | 5, 12 => [(1 : Fin 2)]
  | 5, 13 => [(1 : Fin 2)]
  | 5, 14 => [(1 : Fin 2)]
  | 5, 15 => [(1 : Fin 2)]
  | _, _ => []

public theorem m22L3RepBase : m22L3Rep (0 : Fin 16) = 1 := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

public theorem m22L3RepPoint : (r : Fin 16) -> m22L3Rep r (4 : Fin 22) = m22L3Point r := by
  intro r
  fin_cases r <;> rfl

@[reducible, expose]
public def m22L3PointInv : Fin 22 -> Fin 16
  | 0 => (2 : Fin 16)
  | 1 => (0 : Fin 16)
  | 2 => (0 : Fin 16)
  | 3 => (0 : Fin 16)
  | 4 => (0 : Fin 16)
  | 5 => (9 : Fin 16)
  | 6 => (5 : Fin 16)
  | 7 => (11 : Fin 16)
  | 8 => (6 : Fin 16)
  | 9 => (4 : Fin 16)
  | 10 => (0 : Fin 16)
  | 11 => (12 : Fin 16)
  | 12 => (13 : Fin 16)
  | 13 => (14 : Fin 16)
  | 14 => (8 : Fin 16)
  | 15 => (1 : Fin 16)
  | 16 => (15 : Fin 16)
  | 17 => (3 : Fin 16)
  | 18 => (0 : Fin 16)
  | 19 => (7 : Fin 16)
  | 20 => (0 : Fin 16)
  | 21 => (10 : Fin 16)
  | _ => (2 : Fin 16)

public theorem m22L3PointInv_left : (r : Fin 16) -> m22L3PointInv (m22L3Point r) = r := by
  intro r
  fin_cases r <;> rfl

public theorem m22L3Point_injective : Function.Injective m22L3Point := by
  intro x y h
  have hh := congrArg m22L3PointInv h
  simpa [m22L3PointInv_left] using hh

end Sporadic.Mathieu
