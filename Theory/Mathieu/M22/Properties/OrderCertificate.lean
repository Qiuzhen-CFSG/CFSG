module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
public import Theory.Mathieu.M22.Block
public import Theory.Mathieu.WordSubgroup

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000



set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise
/-! GAP-exported reflected table Schreier--Sims certificate for M22. -/

@[reducible, expose] public def m22L0G0To : Fin 22 -> Fin 22
  | 0 => (6 : Fin 22)
  | 1 => (13 : Fin 22)
  | 2 => (8 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (12 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (0 : Fin 22)
  | 7 => (17 : Fin 22)
  | 8 => (2 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (14 : Fin 22)
  | 12 => (4 : Fin 22)
  | 13 => (1 : Fin 22)
  | 14 => (11 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (7 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (21 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose] public def m22L0G0InvFun : Fin 22 -> Fin 22
  | 0 => (6 : Fin 22)
  | 1 => (13 : Fin 22)
  | 2 => (8 : Fin 22)
  | 3 => (16 : Fin 22)
  | 4 => (12 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (0 : Fin 22)
  | 7 => (17 : Fin 22)
  | 8 => (2 : Fin 22)
  | 9 => (10 : Fin 22)
  | 10 => (9 : Fin 22)
  | 11 => (14 : Fin 22)
  | 12 => (4 : Fin 22)
  | 13 => (1 : Fin 22)
  | 14 => (11 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (3 : Fin 22)
  | 17 => (7 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (21 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L0G0_left : forall x, m22L0G0InvFun (m22L0G0To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0G0_right : forall x, m22L0G0To (m22L0G0InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0G0_left

@[reducible, expose] public def m22L0G0 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0G0To m22L0G0InvFun m22L0G0_left m22L0G0_right

@[reducible, expose] public def m22L0G1To : Fin 22 -> Fin 22
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

@[reducible, expose] public def m22L0G1InvFun : Fin 22 -> Fin 22
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

public theorem m22L0G1_left : forall x, m22L0G1InvFun (m22L0G1To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L0G1_right : forall x, m22L0G1To (m22L0G1InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L0G1_left

@[reducible, expose] public def m22L0G1 : Equiv.Perm (Fin 22) :=
  tablePerm m22L0G1To m22L0G1InvFun m22L0G1_left m22L0G1_right

@[reducible, expose] public def m22L0Gen : Fin 4 -> Equiv.Perm (Fin 22)
  | 0 => m22L0G0
  | 1 => m22L0G1
  | 2 => Inv.inv m22L0G0
  | 3 => Inv.inv m22L0G1
  | _ => m22L0G0

@[reducible, expose] public def m22L0Inv : Fin 4 -> Fin 4
  | 0 => (2 : Fin 4)
  | 1 => (3 : Fin 4)
  | 2 => (0 : Fin 4)
  | 3 => (1 : Fin 4)
  | _ => (0 : Fin 4)

public theorem m22L0Inv_spec : (i : Fin 4) -> m22L0Gen (m22L0Inv i) = Inv.inv (m22L0Gen i) := by
  intro i
  fin_cases i <;> simp [m22L0Gen, m22L0Inv]

public theorem m22GeneratorA_eq_m22L0G0 : m22GeneratorA = m22L0G0 := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

public theorem m22GeneratorB_eq_m22L0G1 : m22GeneratorB = m22L0G1 := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise
@[reducible, expose] public def m22L1G0To : Fin 22 -> Fin 22
  | 0 => (9 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (15 : Fin 22)
  | 5 => (6 : Fin 22)
  | 6 => (5 : Fin 22)
  | 7 => (21 : Fin 22)
  | 8 => (17 : Fin 22)
  | 9 => (0 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (13 : Fin 22)
  | 12 => (16 : Fin 22)
  | 13 => (11 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (4 : Fin 22)
  | 16 => (12 : Fin 22)
  | 17 => (8 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (7 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose] public def m22L1G0InvFun : Fin 22 -> Fin 22
  | 0 => (9 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (15 : Fin 22)
  | 5 => (6 : Fin 22)
  | 6 => (5 : Fin 22)
  | 7 => (21 : Fin 22)
  | 8 => (17 : Fin 22)
  | 9 => (0 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (13 : Fin 22)
  | 12 => (16 : Fin 22)
  | 13 => (11 : Fin 22)
  | 14 => (19 : Fin 22)
  | 15 => (4 : Fin 22)
  | 16 => (12 : Fin 22)
  | 17 => (8 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (14 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (7 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1G0_left : forall x, m22L1G0InvFun (m22L1G0To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1G0_right : forall x, m22L1G0To (m22L1G0InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1G0_left

@[reducible, expose] public def m22L1G0 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1G0To m22L1G0InvFun m22L1G0_left m22L1G0_right

@[reducible, expose] public def m22L1G1To : Fin 22 -> Fin 22
  | 0 => (2 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (0 : Fin 22)
  | 3 => (11 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (6 : Fin 22)
  | 7 => (20 : Fin 22)
  | 8 => (9 : Fin 22)
  | 9 => (8 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (3 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (18 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (21 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (14 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (7 : Fin 22)
  | 21 => (16 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose] public def m22L1G1InvFun : Fin 22 -> Fin 22
  | 0 => (2 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (0 : Fin 22)
  | 3 => (11 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (13 : Fin 22)
  | 6 => (6 : Fin 22)
  | 7 => (20 : Fin 22)
  | 8 => (9 : Fin 22)
  | 9 => (8 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (3 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (5 : Fin 22)
  | 14 => (18 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (21 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (14 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (7 : Fin 22)
  | 21 => (16 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L1G1_left : forall x, m22L1G1InvFun (m22L1G1To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1G1_right : forall x, m22L1G1To (m22L1G1InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1G1_left

@[reducible, expose] public def m22L1G1 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1G1To m22L1G1InvFun m22L1G1_left m22L1G1_right

@[reducible, expose] public def m22L1G2To : Fin 22 -> Fin 22
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

@[reducible, expose] public def m22L1G2InvFun : Fin 22 -> Fin 22
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

public theorem m22L1G2_left : forall x, m22L1G2InvFun (m22L1G2To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L1G2_right : forall x, m22L1G2To (m22L1G2InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L1G2_left

@[reducible, expose] public def m22L1G2 : Equiv.Perm (Fin 22) :=
  tablePerm m22L1G2To m22L1G2InvFun m22L1G2_left m22L1G2_right

@[reducible, expose] public def m22L1Gen : Fin 6 -> Equiv.Perm (Fin 22)
  | 0 => m22L1G0
  | 1 => m22L1G1
  | 2 => m22L1G2
  | 3 => Inv.inv m22L1G0
  | 4 => Inv.inv m22L1G1
  | 5 => Inv.inv m22L1G2
  | _ => m22L1G0

@[reducible, expose] public def m22L1Inv : Fin 6 -> Fin 6
  | 0 => (3 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (5 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (1 : Fin 6)
  | 5 => (2 : Fin 6)
  | _ => (0 : Fin 6)

public theorem m22L1Inv_spec : (i : Fin 6) -> m22L1Gen (m22L1Inv i) = Inv.inv (m22L1Gen i) := by
  intro i
  fin_cases i <;> simp [m22L1Gen, m22L1Inv]

@[reducible, expose] public def m22L1GenWord : Fin 6 -> List (Fin 4)
  | 0 => [(3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | 1 => [(1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | 2 => [(3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4)]
  | 3 => [(3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | 4 => [(1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | 5 => [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | _ => [(3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4)]

public theorem m22L1Gen_eq_word : (i : Fin 6) -> m22L1Gen i = evalWord m22L0Gen (m22L1GenWord i) := by
  intro i
  fin_cases i <;> apply Equiv.ext <;> intro x <;> fin_cases x <;> rfl

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise
@[reducible, expose] public def m22L2G0To : Fin 22 -> Fin 22 :=
  m22L1G0To

@[reducible, expose] public def m22L2G0InvFun : Fin 22 -> Fin 22 :=
  m22L1G0InvFun

public theorem m22L2G0_left : forall x, m22L2G0InvFun (m22L2G0To x) = x :=
  m22L1G0_left

public theorem m22L2G0_right : forall x, m22L2G0To (m22L2G0InvFun x) = x :=
  m22L1G0_right

@[reducible, expose] public def m22L2G0 : Equiv.Perm (Fin 22) :=
  m22L1G0
@[reducible, expose] public def m22L2G1To : Fin 22 -> Fin 22 :=
  m22L1G2To

@[reducible, expose] public def m22L2G1InvFun : Fin 22 -> Fin 22 :=
  m22L1G2InvFun

public theorem m22L2G1_left : forall x, m22L2G1InvFun (m22L2G1To x) = x :=
  m22L1G2_left

public theorem m22L2G1_right : forall x, m22L2G1To (m22L2G1InvFun x) = x :=
  m22L1G2_right

@[reducible, expose] public def m22L2G1 : Equiv.Perm (Fin 22) :=
  m22L1G2
@[reducible, expose] public def m22L2G2To : Fin 22 -> Fin 22
  | 0 => (4 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (6 : Fin 22)
  | 5 => (8 : Fin 22)
  | 6 => (0 : Fin 22)
  | 7 => (5 : Fin 22)
  | 8 => (7 : Fin 22)
  | 9 => (21 : Fin 22)
  | 10 => (18 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (13 : Fin 22)
  | 13 => (16 : Fin 22)
  | 14 => (9 : Fin 22)
  | 15 => (19 : Fin 22)
  | 16 => (12 : Fin 22)
  | 17 => (15 : Fin 22)
  | 18 => (20 : Fin 22)
  | 19 => (17 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (14 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose] public def m22L2G2InvFun : Fin 22 -> Fin 22
  | 0 => (6 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (0 : Fin 22)
  | 5 => (7 : Fin 22)
  | 6 => (4 : Fin 22)
  | 7 => (8 : Fin 22)
  | 8 => (5 : Fin 22)
  | 9 => (14 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (16 : Fin 22)
  | 13 => (12 : Fin 22)
  | 14 => (21 : Fin 22)
  | 15 => (17 : Fin 22)
  | 16 => (13 : Fin 22)
  | 17 => (19 : Fin 22)
  | 18 => (10 : Fin 22)
  | 19 => (15 : Fin 22)
  | 20 => (18 : Fin 22)
  | 21 => (9 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2G2_left : forall x, m22L2G2InvFun (m22L2G2To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2G2_right : forall x, m22L2G2To (m22L2G2InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2G2_left

@[reducible, expose] public def m22L2G2 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2G2To m22L2G2InvFun m22L2G2_left m22L2G2_right

@[reducible, expose] public def m22L2G3To : Fin 22 -> Fin 22
  | 0 => (11 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (17 : Fin 22)
  | 6 => (0 : Fin 22)
  | 7 => (21 : Fin 22)
  | 8 => (13 : Fin 22)
  | 9 => (12 : Fin 22)
  | 10 => (20 : Fin 22)
  | 11 => (6 : Fin 22)
  | 12 => (19 : Fin 22)
  | 13 => (14 : Fin 22)
  | 14 => (8 : Fin 22)
  | 15 => (7 : Fin 22)
  | 16 => (5 : Fin 22)
  | 17 => (16 : Fin 22)
  | 18 => (10 : Fin 22)
  | 19 => (9 : Fin 22)
  | 20 => (18 : Fin 22)
  | 21 => (15 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible, expose] public def m22L2G3InvFun : Fin 22 -> Fin 22
  | 0 => (6 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (16 : Fin 22)
  | 6 => (11 : Fin 22)
  | 7 => (15 : Fin 22)
  | 8 => (14 : Fin 22)
  | 9 => (19 : Fin 22)
  | 10 => (18 : Fin 22)
  | 11 => (0 : Fin 22)
  | 12 => (9 : Fin 22)
  | 13 => (8 : Fin 22)
  | 14 => (13 : Fin 22)
  | 15 => (21 : Fin 22)
  | 16 => (17 : Fin 22)
  | 17 => (5 : Fin 22)
  | 18 => (20 : Fin 22)
  | 19 => (12 : Fin 22)
  | 20 => (10 : Fin 22)
  | 21 => (7 : Fin 22)
  | _ => (1 : Fin 22)

public theorem m22L2G3_left : forall x, m22L2G3InvFun (m22L2G3To x) = x := by
  intro x
  fin_cases x <;> rfl

public theorem m22L2G3_right : forall x, m22L2G3To (m22L2G3InvFun x) = x :=
  rightInverse_of_leftInverse_fin m22L2G3_left

@[reducible, expose] public def m22L2G3 : Equiv.Perm (Fin 22) :=
  tablePerm m22L2G3To m22L2G3InvFun m22L2G3_left m22L2G3_right

@[reducible, expose] public def m22L2Gen : Fin 8 -> Equiv.Perm (Fin 22)
  | 0 => m22L2G0
  | 1 => m22L2G1
  | 2 => m22L2G2
  | 3 => m22L2G3
  | 4 => Inv.inv m22L2G0
  | 5 => Inv.inv m22L2G1
  | 6 => Inv.inv m22L2G2
  | 7 => Inv.inv m22L2G3
  | _ => m22L2G0

@[reducible, expose] public def m22L2Inv : Fin 8 -> Fin 8
  | 0 => (4 : Fin 8)
  | 1 => (5 : Fin 8)
  | 2 => (6 : Fin 8)
  | 3 => (7 : Fin 8)
  | 4 => (0 : Fin 8)
  | 5 => (1 : Fin 8)
  | 6 => (2 : Fin 8)
  | 7 => (3 : Fin 8)
  | _ => (0 : Fin 8)

public theorem m22L2Inv_spec : (i : Fin 8) -> m22L2Gen (m22L2Inv i) = Inv.inv (m22L2Gen i) := by
  intro i
  fin_cases i <;> simp [m22L2Gen, m22L2Inv]

@[reducible, expose] public def m22L2GenWord : Fin 8 -> List (Fin 6)
  | 0 => [(0 : Fin 6)]
  | 1 => [(2 : Fin 6)]
  | 2 => [(0 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6), (5 : Fin 6), (1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (1 : Fin 6), (5 : Fin 6), (1 : Fin 6), (2 : Fin 6)]
  | 3 => [(2 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6), (5 : Fin 6), (1 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6), (0 : Fin 6)]
  | 4 => [(0 : Fin 6)]
  | 5 => [(5 : Fin 6)]
  | 6 => [(2 : Fin 6), (1 : Fin 6), (2 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6), (5 : Fin 6), (0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6)]
  | 7 => [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (1 : Fin 6), (0 : Fin 6), (1 : Fin 6), (5 : Fin 6)]
  | _ => [(0 : Fin 6)]

public theorem m22L2Gen_eq_word : (i : Fin 8) -> m22L2Gen i = evalWord m22L1Gen (m22L2GenWord i) := by
  intro i
  fin_cases i <;> apply Equiv.ext <;> intro x <;> fin_cases x <;> rfl

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise
@[reducible, expose] public def m22L3G0To : Fin 22 -> Fin 22 :=
  m22L1G0To

@[reducible, expose] public def m22L3G0InvFun : Fin 22 -> Fin 22 :=
  m22L1G0InvFun

public theorem m22L3G0_left : forall x, m22L3G0InvFun (m22L3G0To x) = x :=
  m22L1G0_left

public theorem m22L3G0_right : forall x, m22L3G0To (m22L3G0InvFun x) = x :=
  m22L1G0_right

@[reducible, expose] public def m22L3G0 : Equiv.Perm (Fin 22) :=
  m22L1G0
@[reducible, expose] public def m22L3G1To : Fin 22 -> Fin 22 :=
  m22L2G2To

@[reducible, expose] public def m22L3G1InvFun : Fin 22 -> Fin 22 :=
  m22L2G2InvFun

public theorem m22L3G1_left : forall x, m22L3G1InvFun (m22L3G1To x) = x :=
  m22L2G2_left

public theorem m22L3G1_right : forall x, m22L3G1To (m22L3G1InvFun x) = x :=
  m22L2G2_right

@[reducible, expose] public def m22L3G1 : Equiv.Perm (Fin 22) :=
  m22L2G2
@[reducible, expose] public def m22L3G2To : Fin 22 -> Fin 22 :=
  m22L2G3To

@[reducible, expose] public def m22L3G2InvFun : Fin 22 -> Fin 22 :=
  m22L2G3InvFun

public theorem m22L3G2_left : forall x, m22L3G2InvFun (m22L3G2To x) = x :=
  m22L2G3_left

public theorem m22L3G2_right : forall x, m22L3G2To (m22L3G2InvFun x) = x :=
  m22L2G3_right

@[reducible, expose] public def m22L3G2 : Equiv.Perm (Fin 22) :=
  m22L2G3
@[reducible, expose] public def m22L3Gen : Fin 6 -> Equiv.Perm (Fin 22)
  | 0 => m22L3G0
  | 1 => m22L3G1
  | 2 => m22L3G2
  | 3 => Inv.inv m22L3G0
  | 4 => Inv.inv m22L3G1
  | 5 => Inv.inv m22L3G2
  | _ => m22L3G0

@[reducible, expose] public def m22L3Inv : Fin 6 -> Fin 6
  | 0 => (3 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (5 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (1 : Fin 6)
  | 5 => (2 : Fin 6)
  | _ => (0 : Fin 6)

public theorem m22L3Inv_spec : (i : Fin 6) -> m22L3Gen (m22L3Inv i) = Inv.inv (m22L3Gen i) := by
  intro i
  fin_cases i <;> simp [m22L3Gen, m22L3Inv]

@[reducible, expose] public def m22L3GenWord : Fin 6 -> List (Fin 8)
  | 0 => [(0 : Fin 8)]
  | 1 => [(2 : Fin 8)]
  | 2 => [(3 : Fin 8)]
  | 3 => [(0 : Fin 8)]
  | 4 => [(6 : Fin 8)]
  | 5 => [(7 : Fin 8)]
  | _ => [(0 : Fin 8)]

public theorem m22L3Gen_eq_word : (i : Fin 6) -> m22L3Gen i = evalWord m22L2Gen (m22L3GenWord i) := by
  intro i
  fin_cases i <;> apply Equiv.ext <;> intro x <;> fin_cases x <;> rfl

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise
@[reducible, expose] public def m22L4G0To : Fin 22 -> Fin 22 :=
  m22L2G3To

@[reducible, expose] public def m22L4G0InvFun : Fin 22 -> Fin 22 :=
  m22L2G3InvFun

public theorem m22L4G0_left : forall x, m22L4G0InvFun (m22L4G0To x) = x :=
  m22L2G3_left

public theorem m22L4G0_right : forall x, m22L4G0To (m22L4G0InvFun x) = x :=
  m22L2G3_right

@[reducible, expose] public def m22L4G0 : Equiv.Perm (Fin 22) :=
  m22L2G3
@[reducible, expose] public def m22L4Gen : Fin 2 -> Equiv.Perm (Fin 22)
  | 0 => m22L4G0
  | 1 => Inv.inv m22L4G0
  | _ => m22L4G0

@[reducible, expose] public def m22L4Inv : Fin 2 -> Fin 2
  | 0 => (1 : Fin 2)
  | 1 => (0 : Fin 2)
  | _ => (0 : Fin 2)

public theorem m22L4Inv_spec : (i : Fin 2) -> m22L4Gen (m22L4Inv i) = Inv.inv (m22L4Gen i) := by
  intro i
  fin_cases i <;> simp [m22L4Gen, m22L4Inv]

@[reducible, expose] public def m22L4GenWord : Fin 2 -> List (Fin 6)
  | 0 => [(2 : Fin 6)]
  | 1 => [(5 : Fin 6)]
  | _ => [(2 : Fin 6)]

public theorem m22L4Gen_eq_word : (i : Fin 2) -> m22L4Gen i = evalWord m22L3Gen (m22L4GenWord i) := by
  intro i
  fin_cases i <;> apply Equiv.ext <;> intro x <;> fin_cases x <;> rfl

@[reducible, expose] public def m22L5Gen : Fin 0 -> Equiv.Perm (Fin 22) := fun i => nomatch i

@[reducible, expose] public def m22L5Inv : Fin 0 -> Fin 0 := fun i => nomatch i

public theorem m22L5Inv_spec : (i : Fin 0) -> m22L5Gen (m22L5Inv i) = Inv.inv (m22L5Gen i) := by
  intro i
  exact Fin.elim0 i

end Sporadic.Mathieu
