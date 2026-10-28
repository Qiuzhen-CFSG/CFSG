module

public import Theory.Mathieu.M22.Properties.OrderCertificate
import Mathlib.Tactic.FinCases

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise
@[reducible, expose]
public def m22L0R0To : Fin 22 -> Fin 22 := id

@[reducible, expose]
public def m22L0R0InvFun : Fin 22 -> Fin 22 := id

public theorem m22L0R0_left : forall x, m22L0R0InvFun (m22L0R0To x) = x := by
  intro x
  rfl

public theorem m22L0R0_right : forall x, m22L0R0To (m22L0R0InvFun x) = x := by
  intro x
  rfl

@[reducible, expose]
public def m22L0R0 : Equiv.Perm (Fin 22) := Equiv.refl _

@[reducible, expose]
public def m22L0R1To : Fin 22 -> Fin 22 :=
  m22L0G0To

@[reducible, expose]
public def m22L0R1InvFun : Fin 22 -> Fin 22 :=
  m22L0G0InvFun

public theorem m22L0R1_left : forall x, m22L0R1InvFun (m22L0R1To x) = x :=
  m22L0G0_left

public theorem m22L0R1_right : forall x, m22L0R1To (m22L0R1InvFun x) = x :=
  m22L0G0_right

@[reducible, expose]
public def m22L0R1 : Equiv.Perm (Fin 22) :=
  m22L0G0

@[reducible, expose]
public def m22L0R2To : Fin 22 -> Fin 22
  | 0 => (1 : Fin 22)
  | 1 => (21 : Fin 22)
  | 2 => (13 : Fin 22)
  | 3 => (0 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (12 : Fin 22)
  | 6 => (15 : Fin 22)
  | 7 => (11 : Fin 22)
  | 8 => (10 : Fin 22)
  | 9 => (9 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (6 : Fin 22)
  | 12 => (5 : Fin 22)
  | 13 => (4 : Fin 22)
  | 14 => (8 : Fin 22)
  | 15 => (7 : Fin 22)
  | 16 => (16 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (2 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (14 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R2InvFun : Fin 22 -> Fin 22
  | 0 => (3 : Fin 22)
  | 1 => (0 : Fin 22)
  | 2 => (18 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (13 : Fin 22)
  | 5 => (12 : Fin 22)
  | 6 => (11 : Fin 22)
  | 7 => (15 : Fin 22)
  | 8 => (14 : Fin 22)
  | 9 => (9 : Fin 22)
  | 10 => (8 : Fin 22)
  | 11 => (7 : Fin 22)
  | 12 => (5 : Fin 22)
  | 13 => (2 : Fin 22)
  | 14 => (20 : Fin 22)
  | 15 => (6 : Fin 22)
  | 16 => (16 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (1 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R2_left : forall x, m22L0R2InvFun (m22L0R2To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R2_right : forall x, m22L0R2To (m22L0R2InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R2_left

@[reducible, expose]
public def m22L0R2 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R2To m22L0R2InvFun m22L0R2_left m22L0R2_right

@[reducible, expose]
public def m22L0R3To : Fin 22 -> Fin 22
  | 0 => (15 : Fin 22)
  | 1 => (4 : Fin 22)
  | 2 => (10 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (12 : Fin 22)
  | 6 => (1 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (13 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (8 : Fin 22)
  | 12 => (18 : Fin 22)
  | 13 => (21 : Fin 22)
  | 14 => (6 : Fin 22)
  | 15 => (7 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (11 : Fin 22)
  | 18 => (2 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (14 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R3InvFun : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (6 : Fin 22)
  | 2 => (18 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (1 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (14 : Fin 22)
  | 7 => (15 : Fin 22)
  | 8 => (11 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (2 : Fin 22)
  | 11 => (17 : Fin 22)
  | 12 => (5 : Fin 22)
  | 13 => (8 : Fin 22)
  | 14 => (20 : Fin 22)
  | 15 => (0 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (12 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (13 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R3_left : forall x, m22L0R3InvFun (m22L0R3To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R3_right : forall x, m22L0R3To (m22L0R3InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R3_left

@[reducible, expose]
public def m22L0R3 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R3To m22L0R3InvFun m22L0R3_left m22L0R3_right

@[reducible, expose]
public def m22L0R4To : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (3 : Fin 22)
  | 2 => (4 : Fin 22)
  | 3 => (1 : Fin 22)
  | 4 => (2 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (7 : Fin 22)
  | 7 => (6 : Fin 22)
  | 8 => (20 : Fin 22)
  | 9 => (9 : Fin 22)
  | 10 => (14 : Fin 22)
  | 11 => (15 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (18 : Fin 22)
  | 14 => (10 : Fin 22)
  | 15 => (11 : Fin 22)
  | 16 => (16 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (13 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (8 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R4InvFun : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (3 : Fin 22)
  | 2 => (4 : Fin 22)
  | 3 => (1 : Fin 22)
  | 4 => (2 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (7 : Fin 22)
  | 7 => (6 : Fin 22)
  | 8 => (20 : Fin 22)
  | 9 => (9 : Fin 22)
  | 10 => (14 : Fin 22)
  | 11 => (15 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (18 : Fin 22)
  | 14 => (10 : Fin 22)
  | 15 => (11 : Fin 22)
  | 16 => (16 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (13 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (8 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R4_left : forall x, m22L0R4InvFun (m22L0R4To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R4_right : forall x, m22L0R4To (m22L0R4InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R4_left

@[reducible, expose]
public def m22L0R4 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R4To m22L0R4InvFun m22L0R4_left m22L0R4_right

@[reducible, expose]
public def m22L0R5To : Fin 22 -> Fin 22
  | 0 => (15 : Fin 22)
  | 1 => (12 : Fin 22)
  | 2 => (9 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (13 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (1 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (2 : Fin 22)
  | 12 => (18 : Fin 22)
  | 13 => (21 : Fin 22)
  | 14 => (0 : Fin 22)
  | 15 => (17 : Fin 22)
  | 16 => (6 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (8 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (11 : Fin 22)
  | 21 => (16 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R5InvFun : Fin 22 -> Fin 22
  | 0 => (14 : Fin 22)
  | 1 => (8 : Fin 22)
  | 2 => (11 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (16 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (18 : Fin 22)
  | 9 => (2 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (20 : Fin 22)
  | 12 => (1 : Fin 22)
  | 13 => (6 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (0 : Fin 22)
  | 16 => (21 : Fin 22)
  | 17 => (15 : Fin 22)
  | 18 => (12 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (13 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R5_left : forall x, m22L0R5InvFun (m22L0R5To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R5_right : forall x, m22L0R5To (m22L0R5InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R5_left

@[reducible, expose]
public def m22L0R5 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R5To m22L0R5InvFun m22L0R5_left m22L0R5_right

@[reducible, expose]
public def m22L0R6To : Fin 22 -> Fin 22
  | 0 => (7 : Fin 22)
  | 1 => (18 : Fin 22)
  | 2 => (20 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (12 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (21 : Fin 22)
  | 7 => (17 : Fin 22)
  | 8 => (4 : Fin 22)
  | 9 => (14 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (10 : Fin 22)
  | 12 => (2 : Fin 22)
  | 13 => (3 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (11 : Fin 22)
  | 16 => (1 : Fin 22)
  | 17 => (6 : Fin 22)
  | 18 => (13 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (8 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R6InvFun : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (16 : Fin 22)
  | 2 => (12 : Fin 22)
  | 3 => (13 : Fin 22)
  | 4 => (8 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (17 : Fin 22)
  | 7 => (0 : Fin 22)
  | 8 => (20 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (11 : Fin 22)
  | 11 => (15 : Fin 22)
  | 12 => (4 : Fin 22)
  | 13 => (18 : Fin 22)
  | 14 => (9 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (7 : Fin 22)
  | 18 => (1 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (2 : Fin 22)
  | 21 => (6 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R6_left : forall x, m22L0R6InvFun (m22L0R6To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R6_right : forall x, m22L0R6To (m22L0R6InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R6_left

@[reducible, expose]
public def m22L0R6 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R6To m22L0R6InvFun m22L0R6_left m22L0R6_right

@[reducible, expose]
public def m22L0R7To : Fin 22 -> Fin 22
  | 0 => (21 : Fin 22)
  | 1 => (16 : Fin 22)
  | 2 => (12 : Fin 22)
  | 3 => (13 : Fin 22)
  | 4 => (8 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (17 : Fin 22)
  | 7 => (0 : Fin 22)
  | 8 => (20 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (11 : Fin 22)
  | 11 => (15 : Fin 22)
  | 12 => (4 : Fin 22)
  | 13 => (18 : Fin 22)
  | 14 => (9 : Fin 22)
  | 15 => (14 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (7 : Fin 22)
  | 18 => (1 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (2 : Fin 22)
  | 21 => (6 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R7InvFun : Fin 22 -> Fin 22
  | 0 => (7 : Fin 22)
  | 1 => (18 : Fin 22)
  | 2 => (20 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (12 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (21 : Fin 22)
  | 7 => (17 : Fin 22)
  | 8 => (4 : Fin 22)
  | 9 => (14 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (10 : Fin 22)
  | 12 => (2 : Fin 22)
  | 13 => (3 : Fin 22)
  | 14 => (15 : Fin 22)
  | 15 => (11 : Fin 22)
  | 16 => (1 : Fin 22)
  | 17 => (6 : Fin 22)
  | 18 => (13 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (8 : Fin 22)
  | 21 => (0 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R7_left : forall x, m22L0R7InvFun (m22L0R7To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R7_right : forall x, m22L0R7To (m22L0R7InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R7_left

@[reducible, expose]
public def m22L0R7 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R7To m22L0R7InvFun m22L0R7_left m22L0R7_right

@[reducible, expose]
public def m22L0R8To : Fin 22 -> Fin 22 :=
  m22L0G1To

@[reducible, expose]
public def m22L0R8InvFun : Fin 22 -> Fin 22 :=
  m22L0G1InvFun

public theorem m22L0R8_left : forall x, m22L0R8InvFun (m22L0R8To x) = x :=
  m22L0G1_left

public theorem m22L0R8_right : forall x, m22L0R8To (m22L0R8InvFun x) = x :=
  m22L0G1_right

@[reducible, expose]
public def m22L0R8 : Equiv.Perm (Fin 22) :=
  m22L0G1

@[reducible, expose]
public def m22L0R9To : Fin 22 -> Fin 22
  | 0 => (7 : Fin 22)
  | 1 => (5 : Fin 22)
  | 2 => (9 : Fin 22)
  | 3 => (0 : Fin 22)
  | 4 => (12 : Fin 22)
  | 5 => (18 : Fin 22)
  | 6 => (4 : Fin 22)
  | 7 => (17 : Fin 22)
  | 8 => (21 : Fin 22)
  | 9 => (14 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (13 : Fin 22)
  | 12 => (2 : Fin 22)
  | 13 => (3 : Fin 22)
  | 14 => (1 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (15 : Fin 22)
  | 17 => (8 : Fin 22)
  | 18 => (10 : Fin 22)
  | 19 => (11 : Fin 22)
  | 20 => (6 : Fin 22)
  | 21 => (16 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R9InvFun : Fin 22 -> Fin 22
  | 0 => (3 : Fin 22)
  | 1 => (14 : Fin 22)
  | 2 => (12 : Fin 22)
  | 3 => (13 : Fin 22)
  | 4 => (6 : Fin 22)
  | 5 => (1 : Fin 22)
  | 6 => (20 : Fin 22)
  | 7 => (0 : Fin 22)
  | 8 => (17 : Fin 22)
  | 9 => (2 : Fin 22)
  | 10 => (18 : Fin 22)
  | 11 => (19 : Fin 22)
  | 12 => (4 : Fin 22)
  | 13 => (11 : Fin 22)
  | 14 => (9 : Fin 22)
  | 15 => (16 : Fin 22)
  | 16 => (21 : Fin 22)
  | 17 => (7 : Fin 22)
  | 18 => (5 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (8 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R9_left : forall x, m22L0R9InvFun (m22L0R9To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R9_right : forall x, m22L0R9To (m22L0R9InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R9_left

@[reducible, expose]
public def m22L0R9 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R9To m22L0R9InvFun m22L0R9_left m22L0R9_right

@[reducible, expose]
public def m22L0R10To : Fin 22 -> Fin 22
  | 0 => (11 : Fin 22)
  | 1 => (2 : Fin 22)
  | 2 => (14 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (12 : Fin 22)
  | 6 => (3 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (18 : Fin 22)
  | 9 => (8 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (20 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (0 : Fin 22)
  | 14 => (7 : Fin 22)
  | 15 => (6 : Fin 22)
  | 16 => (21 : Fin 22)
  | 17 => (15 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (1 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R10InvFun : Fin 22 -> Fin 22
  | 0 => (13 : Fin 22)
  | 1 => (21 : Fin 22)
  | 2 => (1 : Fin 22)
  | 3 => (6 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (15 : Fin 22)
  | 7 => (14 : Fin 22)
  | 8 => (9 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (0 : Fin 22)
  | 12 => (5 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (2 : Fin 22)
  | 15 => (17 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (8 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (11 : Fin 22)
  | 21 => (16 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R10_left : forall x, m22L0R10InvFun (m22L0R10To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R10_right : forall x, m22L0R10To (m22L0R10InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R10_left

@[reducible, expose]
public def m22L0R10 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R10To m22L0R10InvFun m22L0R10_left m22L0R10_right

@[reducible, expose]
public def m22L0R11To : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (6 : Fin 22)
  | 2 => (18 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (1 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (14 : Fin 22)
  | 7 => (15 : Fin 22)
  | 8 => (11 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (2 : Fin 22)
  | 11 => (17 : Fin 22)
  | 12 => (5 : Fin 22)
  | 13 => (8 : Fin 22)
  | 14 => (20 : Fin 22)
  | 15 => (0 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (12 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (13 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R11InvFun : Fin 22 -> Fin 22
  | 0 => (15 : Fin 22)
  | 1 => (4 : Fin 22)
  | 2 => (10 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (12 : Fin 22)
  | 6 => (1 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (13 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (8 : Fin 22)
  | 12 => (18 : Fin 22)
  | 13 => (21 : Fin 22)
  | 14 => (6 : Fin 22)
  | 15 => (7 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (11 : Fin 22)
  | 18 => (2 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (14 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R11_left : forall x, m22L0R11InvFun (m22L0R11To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R11_right : forall x, m22L0R11To (m22L0R11InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R11_left

@[reducible, expose]
public def m22L0R11 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R11To m22L0R11InvFun m22L0R11_left m22L0R11_right

@[reducible, expose]
public def m22L0R12To : Fin 22 -> Fin 22
  | 0 => (14 : Fin 22)
  | 1 => (8 : Fin 22)
  | 2 => (11 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (16 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (18 : Fin 22)
  | 9 => (2 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (20 : Fin 22)
  | 12 => (1 : Fin 22)
  | 13 => (6 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (0 : Fin 22)
  | 16 => (21 : Fin 22)
  | 17 => (15 : Fin 22)
  | 18 => (12 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (13 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R12InvFun : Fin 22 -> Fin 22
  | 0 => (15 : Fin 22)
  | 1 => (12 : Fin 22)
  | 2 => (9 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (13 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (1 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (2 : Fin 22)
  | 12 => (18 : Fin 22)
  | 13 => (21 : Fin 22)
  | 14 => (0 : Fin 22)
  | 15 => (17 : Fin 22)
  | 16 => (6 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (8 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (11 : Fin 22)
  | 21 => (16 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R12_left : forall x, m22L0R12InvFun (m22L0R12To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R12_right : forall x, m22L0R12To (m22L0R12InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R12_left

@[reducible, expose]
public def m22L0R12 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R12To m22L0R12InvFun m22L0R12_left m22L0R12_right

@[reducible, expose]
public def m22L0R13To : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (15 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (21 : Fin 22)
  | 5 => (18 : Fin 22)
  | 6 => (8 : Fin 22)
  | 7 => (7 : Fin 22)
  | 8 => (6 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (13 : Fin 22)
  | 11 => (19 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (10 : Fin 22)
  | 14 => (14 : Fin 22)
  | 15 => (1 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (5 : Fin 22)
  | 19 => (11 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (4 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R13InvFun : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (15 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (21 : Fin 22)
  | 5 => (18 : Fin 22)
  | 6 => (8 : Fin 22)
  | 7 => (7 : Fin 22)
  | 8 => (6 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (13 : Fin 22)
  | 11 => (19 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (10 : Fin 22)
  | 14 => (14 : Fin 22)
  | 15 => (1 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (5 : Fin 22)
  | 19 => (11 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (4 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R13_left : forall x, m22L0R13InvFun (m22L0R13To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R13_right : forall x, m22L0R13To (m22L0R13InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R13_left

@[reducible, expose]
public def m22L0R13 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R13To m22L0R13InvFun m22L0R13_left m22L0R13_right

@[reducible, expose]
public def m22L0R14To : Fin 22 -> Fin 22
  | 0 => (8 : Fin 22)
  | 1 => (10 : Fin 22)
  | 2 => (6 : Fin 22)
  | 3 => (0 : Fin 22)
  | 4 => (12 : Fin 22)
  | 5 => (18 : Fin 22)
  | 6 => (16 : Fin 22)
  | 7 => (17 : Fin 22)
  | 8 => (2 : Fin 22)
  | 9 => (13 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (14 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (15 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (1 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (7 : Fin 22)
  | 18 => (5 : Fin 22)
  | 19 => (11 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (4 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R14InvFun : Fin 22 -> Fin 22
  | 0 => (3 : Fin 22)
  | 1 => (15 : Fin 22)
  | 2 => (8 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (21 : Fin 22)
  | 5 => (18 : Fin 22)
  | 6 => (2 : Fin 22)
  | 7 => (17 : Fin 22)
  | 8 => (0 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (1 : Fin 22)
  | 11 => (19 : Fin 22)
  | 12 => (4 : Fin 22)
  | 13 => (9 : Fin 22)
  | 14 => (11 : Fin 22)
  | 15 => (13 : Fin 22)
  | 16 => (6 : Fin 22)
  | 17 => (7 : Fin 22)
  | 18 => (5 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R14_left : forall x, m22L0R14InvFun (m22L0R14To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R14_right : forall x, m22L0R14To (m22L0R14InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R14_left

@[reducible, expose]
public def m22L0R14 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R14To m22L0R14InvFun m22L0R14_left m22L0R14_right

@[reducible, expose]
public def m22L0R15To : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (7 : Fin 22)
  | 2 => (13 : Fin 22)
  | 3 => (0 : Fin 22)
  | 4 => (3 : Fin 22)
  | 5 => (2 : Fin 22)
  | 6 => (10 : Fin 22)
  | 7 => (11 : Fin 22)
  | 8 => (15 : Fin 22)
  | 9 => (14 : Fin 22)
  | 10 => (4 : Fin 22)
  | 11 => (17 : Fin 22)
  | 12 => (5 : Fin 22)
  | 13 => (20 : Fin 22)
  | 14 => (8 : Fin 22)
  | 15 => (21 : Fin 22)
  | 16 => (1 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (12 : Fin 22)
  | 19 => (6 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (18 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R15InvFun : Fin 22 -> Fin 22
  | 0 => (3 : Fin 22)
  | 1 => (16 : Fin 22)
  | 2 => (5 : Fin 22)
  | 3 => (4 : Fin 22)
  | 4 => (10 : Fin 22)
  | 5 => (12 : Fin 22)
  | 6 => (19 : Fin 22)
  | 7 => (1 : Fin 22)
  | 8 => (14 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (6 : Fin 22)
  | 11 => (7 : Fin 22)
  | 12 => (18 : Fin 22)
  | 13 => (2 : Fin 22)
  | 14 => (9 : Fin 22)
  | 15 => (8 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (11 : Fin 22)
  | 18 => (21 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (13 : Fin 22)
  | 21 => (15 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R15_left : forall x, m22L0R15InvFun (m22L0R15To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R15_right : forall x, m22L0R15To (m22L0R15InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R15_left

@[reducible, expose]
public def m22L0R15 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R15To m22L0R15InvFun m22L0R15_left m22L0R15_right

@[reducible, expose]
public def m22L0R16To : Fin 22 -> Fin 22
  | 0 => (2 : Fin 22)
  | 1 => (9 : Fin 22)
  | 2 => (0 : Fin 22)
  | 3 => (6 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (18 : Fin 22)
  | 6 => (3 : Fin 22)
  | 7 => (7 : Fin 22)
  | 8 => (8 : Fin 22)
  | 9 => (1 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (15 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (13 : Fin 22)
  | 16 => (16 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (5 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R16InvFun : Fin 22 -> Fin 22
  | 0 => (2 : Fin 22)
  | 1 => (9 : Fin 22)
  | 2 => (0 : Fin 22)
  | 3 => (6 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (18 : Fin 22)
  | 6 => (3 : Fin 22)
  | 7 => (7 : Fin 22)
  | 8 => (8 : Fin 22)
  | 9 => (1 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (21 : Fin 22)
  | 13 => (15 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (13 : Fin 22)
  | 16 => (16 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (5 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (12 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R16_left : forall x, m22L0R16InvFun (m22L0R16To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R16_right : forall x, m22L0R16To (m22L0R16InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R16_left

@[reducible, expose]
public def m22L0R16 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R16To m22L0R16InvFun m22L0R16_left m22L0R16_right

@[reducible, expose]
public def m22L0R17To : Fin 22 -> Fin 22
  | 0 => (10 : Fin 22)
  | 1 => (20 : Fin 22)
  | 2 => (15 : Fin 22)
  | 3 => (1 : Fin 22)
  | 4 => (5 : Fin 22)
  | 5 => (2 : Fin 22)
  | 6 => (16 : Fin 22)
  | 7 => (19 : Fin 22)
  | 8 => (13 : Fin 22)
  | 9 => (4 : Fin 22)
  | 10 => (14 : Fin 22)
  | 11 => (8 : Fin 22)
  | 12 => (3 : Fin 22)
  | 13 => (7 : Fin 22)
  | 14 => (17 : Fin 22)
  | 15 => (21 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (11 : Fin 22)
  | 18 => (12 : Fin 22)
  | 19 => (6 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (18 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R17InvFun : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (3 : Fin 22)
  | 2 => (5 : Fin 22)
  | 3 => (12 : Fin 22)
  | 4 => (9 : Fin 22)
  | 5 => (4 : Fin 22)
  | 6 => (19 : Fin 22)
  | 7 => (13 : Fin 22)
  | 8 => (11 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (0 : Fin 22)
  | 11 => (17 : Fin 22)
  | 12 => (18 : Fin 22)
  | 13 => (8 : Fin 22)
  | 14 => (10 : Fin 22)
  | 15 => (2 : Fin 22)
  | 16 => (6 : Fin 22)
  | 17 => (14 : Fin 22)
  | 18 => (21 : Fin 22)
  | 19 => (7 : Fin 22)
  | 20 => (1 : Fin 22)
  | 21 => (15 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R17_left : forall x, m22L0R17InvFun (m22L0R17To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R17_right : forall x, m22L0R17To (m22L0R17InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R17_left

@[reducible, expose]
public def m22L0R17 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R17To m22L0R17InvFun m22L0R17_left m22L0R17_right

@[reducible, expose]
public def m22L0R18To : Fin 22 -> Fin 22
  | 0 => (3 : Fin 22)
  | 1 => (17 : Fin 22)
  | 2 => (1 : Fin 22)
  | 3 => (6 : Fin 22)
  | 4 => (16 : Fin 22)
  | 5 => (8 : Fin 22)
  | 6 => (9 : Fin 22)
  | 7 => (14 : Fin 22)
  | 8 => (15 : Fin 22)
  | 9 => (11 : Fin 22)
  | 10 => (12 : Fin 22)
  | 11 => (7 : Fin 22)
  | 12 => (5 : Fin 22)
  | 13 => (20 : Fin 22)
  | 14 => (2 : Fin 22)
  | 15 => (21 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (4 : Fin 22)
  | 19 => (0 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (18 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R18InvFun : Fin 22 -> Fin 22
  | 0 => (19 : Fin 22)
  | 1 => (2 : Fin 22)
  | 2 => (14 : Fin 22)
  | 3 => (0 : Fin 22)
  | 4 => (18 : Fin 22)
  | 5 => (12 : Fin 22)
  | 6 => (3 : Fin 22)
  | 7 => (11 : Fin 22)
  | 8 => (5 : Fin 22)
  | 9 => (6 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (9 : Fin 22)
  | 12 => (10 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (7 : Fin 22)
  | 15 => (8 : Fin 22)
  | 16 => (4 : Fin 22)
  | 17 => (1 : Fin 22)
  | 18 => (21 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (13 : Fin 22)
  | 21 => (15 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R18_left : forall x, m22L0R18InvFun (m22L0R18To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R18_right : forall x, m22L0R18To (m22L0R18InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R18_left

@[reducible, expose]
public def m22L0R18 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R18To m22L0R18InvFun m22L0R18_left m22L0R18_right

@[reducible, expose]
public def m22L0R19To : Fin 22 -> Fin 22
  | 0 => (16 : Fin 22)
  | 1 => (11 : Fin 22)
  | 2 => (4 : Fin 22)
  | 3 => (1 : Fin 22)
  | 4 => (0 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (20 : Fin 22)
  | 7 => (6 : Fin 22)
  | 8 => (7 : Fin 22)
  | 9 => (8 : Fin 22)
  | 10 => (18 : Fin 22)
  | 11 => (19 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (14 : Fin 22)
  | 14 => (10 : Fin 22)
  | 15 => (3 : Fin 22)
  | 16 => (21 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (5 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (2 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R19InvFun : Fin 22 -> Fin 22
  | 0 => (4 : Fin 22)
  | 1 => (3 : Fin 22)
  | 2 => (21 : Fin 22)
  | 3 => (15 : Fin 22)
  | 4 => (2 : Fin 22)
  | 5 => (18 : Fin 22)
  | 6 => (7 : Fin 22)
  | 7 => (8 : Fin 22)
  | 8 => (9 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (14 : Fin 22)
  | 11 => (1 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (13 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (0 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (10 : Fin 22)
  | 19 => (11 : Fin 22)
  | 20 => (6 : Fin 22)
  | 21 => (16 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R19_left : forall x, m22L0R19InvFun (m22L0R19To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R19_right : forall x, m22L0R19To (m22L0R19InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R19_left

@[reducible, expose]
public def m22L0R19 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R19To m22L0R19InvFun m22L0R19_left m22L0R19_right

@[reducible, expose]
public def m22L0R20To : Fin 22 -> Fin 22
  | 0 => (20 : Fin 22)
  | 1 => (14 : Fin 22)
  | 2 => (7 : Fin 22)
  | 3 => (21 : Fin 22)
  | 4 => (12 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (16 : Fin 22)
  | 7 => (17 : Fin 22)
  | 8 => (4 : Fin 22)
  | 9 => (18 : Fin 22)
  | 10 => (8 : Fin 22)
  | 11 => (10 : Fin 22)
  | 12 => (0 : Fin 22)
  | 13 => (11 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (3 : Fin 22)
  | 16 => (1 : Fin 22)
  | 17 => (6 : Fin 22)
  | 18 => (5 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (9 : Fin 22)
  | 21 => (2 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R20InvFun : Fin 22 -> Fin 22
  | 0 => (12 : Fin 22)
  | 1 => (16 : Fin 22)
  | 2 => (21 : Fin 22)
  | 3 => (15 : Fin 22)
  | 4 => (8 : Fin 22)
  | 5 => (18 : Fin 22)
  | 6 => (17 : Fin 22)
  | 7 => (2 : Fin 22)
  | 8 => (10 : Fin 22)
  | 9 => (20 : Fin 22)
  | 10 => (11 : Fin 22)
  | 11 => (13 : Fin 22)
  | 12 => (4 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (1 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (6 : Fin 22)
  | 17 => (7 : Fin 22)
  | 18 => (9 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (0 : Fin 22)
  | 21 => (3 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R20_left : forall x, m22L0R20InvFun (m22L0R20To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R20_right : forall x, m22L0R20To (m22L0R20InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R20_left

@[reducible, expose]
public def m22L0R20 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R20To m22L0R20InvFun m22L0R20_left m22L0R20_right

@[reducible, expose]
public def m22L0R21To : Fin 22 -> Fin 22
  | 0 => (0 : Fin 22)
  | 1 => (19 : Fin 22)
  | 2 => (21 : Fin 22)
  | 3 => (15 : Fin 22)
  | 4 => (16 : Fin 22)
  | 5 => (10 : Fin 22)
  | 6 => (9 : Fin 22)
  | 7 => (8 : Fin 22)
  | 8 => (7 : Fin 22)
  | 9 => (6 : Fin 22)
  | 10 => (5 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (14 : Fin 22)
  | 14 => (13 : Fin 22)
  | 15 => (3 : Fin 22)
  | 16 => (4 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (1 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (2 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0R21InvFun : Fin 22 -> Fin 22
  | 0 => (0 : Fin 22)
  | 1 => (19 : Fin 22)
  | 2 => (21 : Fin 22)
  | 3 => (15 : Fin 22)
  | 4 => (16 : Fin 22)
  | 5 => (10 : Fin 22)
  | 6 => (9 : Fin 22)
  | 7 => (8 : Fin 22)
  | 8 => (7 : Fin 22)
  | 9 => (6 : Fin 22)
  | 10 => (5 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (14 : Fin 22)
  | 14 => (13 : Fin 22)
  | 15 => (3 : Fin 22)
  | 16 => (4 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (1 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (2 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0R21_left : forall x, m22L0R21InvFun (m22L0R21To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0R21_right : forall x, m22L0R21To (m22L0R21InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0R21_left

@[reducible, expose]
public def m22L0R21 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0R21To m22L0R21InvFun m22L0R21_left m22L0R21_right

@[reducible, expose]
public def m22L0RepWord : Fin 22 -> List (Fin 4)
  | 0 => []
  | 1 => [(0 : Fin 4)]
  | 2 => [(3 : Fin 4)]
  | 3 => [(3 : Fin 4), (0 : Fin 4)]
  | 4 => [(1 : Fin 4), (1 : Fin 4)]
  | 5 => [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4)]
  | 6 => [(1 : Fin 4), (1 : Fin 4), (0 : Fin 4)]
  | 7 => [(0 : Fin 4), (1 : Fin 4), (1 : Fin 4)]
  | 8 => [(1 : Fin 4)]
  | 9 => [(3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4)]
  | 10 => [(1 : Fin 4), (0 : Fin 4)]
  | 11 => [(0 : Fin 4), (1 : Fin 4)]
  | 12 => [(0 : Fin 4), (1 : Fin 4), (0 : Fin 4)]
  | 13 => [(3 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | 14 => [(3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4)]
  | 15 => [(1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | 16 => [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4)]
  | 17 => [(1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4)]
  | 18 => [(0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | 19 => [(1 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | 20 => [(1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4)]
  | 21 => [(3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | _ => []

@[reducible, expose]
public def m22L0Rep : Fin 22 -> Equiv.Perm (Fin 22)
  | 0 => m22L0R0
  | 1 => m22L0R1
  | 2 => m22L0R2
  | 3 => m22L0R3
  | 4 => m22L0R4
  | 5 => m22L0R5
  | 6 => m22L0R6
  | 7 => m22L0R7
  | 8 => m22L0R8
  | 9 => m22L0R9
  | 10 => m22L0R10
  | 11 => m22L0R11
  | 12 => m22L0R12
  | 13 => m22L0R13
  | 14 => m22L0R14
  | 15 => m22L0R15
  | 16 => m22L0R16
  | 17 => m22L0R17
  | 18 => m22L0R18
  | 19 => m22L0R19
  | 20 => m22L0R20
  | 21 => m22L0R21
  | _ => m22L0R0

public theorem m22L0Rep_eq_word : (r : Fin 22) -> m22L0Rep r = evalWord m22L0Gen (m22L0RepWord r) := by
  intro r
  fin_cases r <;> apply Equiv.ext <;> intro x <;> fin_cases x <;> rfl

@[reducible, expose]
public def m22L0Point : Fin 22 -> Fin 22
  | 0 => (1 : Fin 22)
  | 1 => (13 : Fin 22)
  | 2 => (21 : Fin 22)
  | 3 => (4 : Fin 22)
  | 4 => (3 : Fin 22)
  | 5 => (12 : Fin 22)
  | 6 => (18 : Fin 22)
  | 7 => (16 : Fin 22)
  | 8 => (0 : Fin 22)
  | 9 => (5 : Fin 22)
  | 10 => (2 : Fin 22)
  | 11 => (6 : Fin 22)
  | 12 => (8 : Fin 22)
  | 13 => (15 : Fin 22)
  | 14 => (10 : Fin 22)
  | 15 => (7 : Fin 22)
  | 16 => (9 : Fin 22)
  | 17 => (20 : Fin 22)
  | 18 => (17 : Fin 22)
  | 19 => (11 : Fin 22)
  | 20 => (14 : Fin 22)
  | 21 => (19 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0Act : Fin 4 -> Fin 22 -> Fin 22
  | 0, 0 => (1 : Fin 22)
  | 0, 1 => (0 : Fin 22)
  | 0, 2 => (2 : Fin 22)
  | 0, 3 => (5 : Fin 22)
  | 0, 4 => (7 : Fin 22)
  | 0, 5 => (3 : Fin 22)
  | 0, 6 => (6 : Fin 22)
  | 0, 7 => (4 : Fin 22)
  | 0, 8 => (11 : Fin 22)
  | 0, 9 => (9 : Fin 22)
  | 0, 10 => (12 : Fin 22)
  | 0, 11 => (8 : Fin 22)
  | 0, 12 => (10 : Fin 22)
  | 0, 13 => (13 : Fin 22)
  | 0, 14 => (16 : Fin 22)
  | 0, 15 => (18 : Fin 22)
  | 0, 16 => (14 : Fin 22)
  | 0, 17 => (17 : Fin 22)
  | 0, 18 => (15 : Fin 22)
  | 0, 19 => (20 : Fin 22)
  | 0, 20 => (19 : Fin 22)
  | 0, 21 => (21 : Fin 22)
  | 1, 0 => (8 : Fin 22)
  | 1, 1 => (10 : Fin 22)
  | 1, 2 => (0 : Fin 22)
  | 1, 3 => (1 : Fin 22)
  | 1, 4 => (2 : Fin 22)
  | 1, 5 => (9 : Fin 22)
  | 1, 6 => (3 : Fin 22)
  | 1, 7 => (7 : Fin 22)
  | 1, 8 => (4 : Fin 22)
  | 1, 9 => (5 : Fin 22)
  | 1, 10 => (6 : Fin 22)
  | 1, 11 => (19 : Fin 22)
  | 1, 12 => (20 : Fin 22)
  | 1, 13 => (11 : Fin 22)
  | 1, 14 => (12 : Fin 22)
  | 1, 15 => (13 : Fin 22)
  | 1, 16 => (16 : Fin 22)
  | 1, 17 => (14 : Fin 22)
  | 1, 18 => (21 : Fin 22)
  | 1, 19 => (15 : Fin 22)
  | 1, 20 => (17 : Fin 22)
  | 1, 21 => (18 : Fin 22)
  | 2, 0 => (1 : Fin 22)
  | 2, 1 => (0 : Fin 22)
  | 2, 2 => (2 : Fin 22)
  | 2, 3 => (5 : Fin 22)
  | 2, 4 => (7 : Fin 22)
  | 2, 5 => (3 : Fin 22)
  | 2, 6 => (6 : Fin 22)
  | 2, 7 => (4 : Fin 22)
  | 2, 8 => (11 : Fin 22)
  | 2, 9 => (9 : Fin 22)
  | 2, 10 => (12 : Fin 22)
  | 2, 11 => (8 : Fin 22)
  | 2, 12 => (10 : Fin 22)
  | 2, 13 => (13 : Fin 22)
  | 2, 14 => (16 : Fin 22)
  | 2, 15 => (18 : Fin 22)
  | 2, 16 => (14 : Fin 22)
  | 2, 17 => (17 : Fin 22)
  | 2, 18 => (15 : Fin 22)
  | 2, 19 => (20 : Fin 22)
  | 2, 20 => (19 : Fin 22)
  | 2, 21 => (21 : Fin 22)
  | 3, 0 => (2 : Fin 22)
  | 3, 1 => (3 : Fin 22)
  | 3, 2 => (4 : Fin 22)
  | 3, 3 => (6 : Fin 22)
  | 3, 4 => (8 : Fin 22)
  | 3, 5 => (9 : Fin 22)
  | 3, 6 => (10 : Fin 22)
  | 3, 7 => (7 : Fin 22)
  | 3, 8 => (0 : Fin 22)
  | 3, 9 => (5 : Fin 22)
  | 3, 10 => (1 : Fin 22)
  | 3, 11 => (13 : Fin 22)
  | 3, 12 => (14 : Fin 22)
  | 3, 13 => (15 : Fin 22)
  | 3, 14 => (17 : Fin 22)
  | 3, 15 => (19 : Fin 22)
  | 3, 16 => (16 : Fin 22)
  | 3, 17 => (20 : Fin 22)
  | 3, 18 => (21 : Fin 22)
  | 3, 19 => (11 : Fin 22)
  | 3, 20 => (12 : Fin 22)
  | 3, 21 => (18 : Fin 22)
  | _, _ => (1 : Fin 22)

@[reducible, expose]
public def m22L0Factor : Fin 4 -> Fin 22 -> List (Fin 6)
  | 0, 0 => []
  | 0, 1 => []
  | 0, 2 => [(1 : Fin 6)]
  | 0, 3 => []
  | 0, 4 => []
  | 0, 5 => []
  | 0, 6 => [(2 : Fin 6), (1 : Fin 6), (0 : Fin 6), (5 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6), (5 : Fin 6)]
  | 0, 7 => []
  | 0, 8 => []
  | 0, 9 => [(0 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6), (0 : Fin 6), (5 : Fin 6), (0 : Fin 6)]
  | 0, 10 => []
  | 0, 11 => []
  | 0, 12 => []
  | 0, 13 => [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (1 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (1 : Fin 6), (5 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | 0, 14 => []
  | 0, 15 => []
  | 0, 16 => []
  | 0, 17 => [(1 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 0, 18 => []
  | 0, 19 => [(5 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6)]
  | 0, 20 => [(0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | 0, 21 => [(0 : Fin 6)]
  | 1, 0 => []
  | 1, 1 => []
  | 1, 2 => []
  | 1, 3 => []
  | 1, 4 => []
  | 1, 5 => [(1 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 1, 6 => []
  | 1, 7 => [(2 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6), (5 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 1, 8 => []
  | 1, 9 => []
  | 1, 10 => []
  | 1, 11 => []
  | 1, 12 => []
  | 1, 13 => []
  | 1, 14 => []
  | 1, 15 => []
  | 1, 16 => [(0 : Fin 6), (2 : Fin 6), (1 : Fin 6), (5 : Fin 6), (0 : Fin 6), (1 : Fin 6), (5 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (1 : Fin 6)]
  | 1, 17 => []
  | 1, 18 => [(1 : Fin 6)]
  | 1, 19 => []
  | 1, 20 => []
  | 1, 21 => []
  | 2, 0 => []
  | 2, 1 => []
  | 2, 2 => [(1 : Fin 6)]
  | 2, 3 => []
  | 2, 4 => []
  | 2, 5 => []
  | 2, 6 => [(2 : Fin 6), (1 : Fin 6), (0 : Fin 6), (5 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6), (5 : Fin 6)]
  | 2, 7 => []
  | 2, 8 => []
  | 2, 9 => [(0 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6), (0 : Fin 6), (5 : Fin 6), (0 : Fin 6)]
  | 2, 10 => []
  | 2, 11 => []
  | 2, 12 => []
  | 2, 13 => [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (1 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (1 : Fin 6), (5 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | 2, 14 => []
  | 2, 15 => []
  | 2, 16 => []
  | 2, 17 => [(1 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 2, 18 => []
  | 2, 19 => [(5 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6)]
  | 2, 20 => [(0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | 2, 21 => [(0 : Fin 6)]
  | 3, 0 => []
  | 3, 1 => []
  | 3, 2 => []
  | 3, 3 => []
  | 3, 4 => []
  | 3, 5 => []
  | 3, 6 => []
  | 3, 7 => [(1 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (1 : Fin 6), (2 : Fin 6), (0 : Fin 6), (5 : Fin 6)]
  | 3, 8 => []
  | 3, 9 => [(1 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 3, 10 => []
  | 3, 11 => []
  | 3, 12 => []
  | 3, 13 => []
  | 3, 14 => []
  | 3, 15 => []
  | 3, 16 => [(0 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (1 : Fin 6), (2 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6), (5 : Fin 6)]
  | 3, 17 => []
  | 3, 18 => []
  | 3, 19 => []
  | 3, 20 => []
  | 3, 21 => [(1 : Fin 6)]
  | _, _ => []

public theorem m22L0RepBase : m22L0Rep (0 : Fin 22) = 1 := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

public theorem m22L0RepPoint : (r : Fin 22) -> m22L0Rep r (1 : Fin 22) = m22L0Point r := by
  intro r
  fin_cases r <;> rfl

@[reducible, expose]
public def m22L0PointInv : Fin 22 -> Fin 22
  | 0 => (8 : Fin 22)
  | 1 => (0 : Fin 22)
  | 2 => (10 : Fin 22)
  | 3 => (4 : Fin 22)
  | 4 => (3 : Fin 22)
  | 5 => (9 : Fin 22)
  | 6 => (11 : Fin 22)
  | 7 => (15 : Fin 22)
  | 8 => (12 : Fin 22)
  | 9 => (16 : Fin 22)
  | 10 => (14 : Fin 22)
  | 11 => (19 : Fin 22)
  | 12 => (5 : Fin 22)
  | 13 => (1 : Fin 22)
  | 14 => (20 : Fin 22)
  | 15 => (13 : Fin 22)
  | 16 => (7 : Fin 22)
  | 17 => (18 : Fin 22)
  | 18 => (6 : Fin 22)
  | 19 => (21 : Fin 22)
  | 20 => (17 : Fin 22)
  | 21 => (2 : Fin 22)
  | _ => (8 : Fin 22)

public theorem m22L0PointInv_left : (r : Fin 22) -> m22L0PointInv (m22L0Point r) = r := by
  intro r
  fin_cases r <;> rfl

public theorem m22L0Point_injective : Function.Injective m22L0Point := by
  intro x y h
  have hh := congrArg m22L0PointInv h
  simpa [m22L0PointInv_left] using hh

end Sporadic.Mathieu
