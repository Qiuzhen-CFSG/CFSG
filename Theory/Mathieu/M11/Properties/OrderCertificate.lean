module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Theory.Mathieu.M11.Generators
public import Theory.Mathieu.M11.Block
public import Theory.Mathieu.M11.Basic
public import Theory.GroupTheory.WordSubgroup

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace M11OrderCertificate
/-! GAP-exported reflected table Schreier--Sims certificate for M11. -/

@[expose, reducible]
public def m11L0G0To : Fin 11 -> Fin 11
  | 0 => (4 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (10 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (0 : Fin 11)
  | 5 => (7 : Fin 11)
  | 6 => (6 : Fin 11)
  | 7 => (5 : Fin 11)
  | 8 => (9 : Fin 11)
  | 9 => (8 : Fin 11)
  | 10 => (2 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0G0InvFun : Fin 11 -> Fin 11 := m11L0G0To

public theorem m11L0G0_left : forall x, m11L0G0InvFun (m11L0G0To x) = x := by decide +kernel

public theorem m11L0G0_right : forall x, m11L0G0To (m11L0G0InvFun x) = x :=
  m11L0G0_left

@[expose, reducible]
public def m11L0G0 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0G0To m11L0G0InvFun m11L0G0_left m11L0G0_right

@[expose, reducible]
public def m11L0G1To : Fin 11 -> Fin 11
  | 0 => (0 : Fin 11)
  | 1 => (4 : Fin 11)
  | 2 => (5 : Fin 11)
  | 3 => (8 : Fin 11)
  | 4 => (3 : Fin 11)
  | 5 => (6 : Fin 11)
  | 6 => (9 : Fin 11)
  | 7 => (7 : Fin 11)
  | 8 => (1 : Fin 11)
  | 9 => (2 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0G1InvFun : Fin 11 -> Fin 11
  | 0 => (0 : Fin 11)
  | 1 => (8 : Fin 11)
  | 2 => (9 : Fin 11)
  | 3 => (4 : Fin 11)
  | 4 => (1 : Fin 11)
  | 5 => (2 : Fin 11)
  | 6 => (5 : Fin 11)
  | 7 => (7 : Fin 11)
  | 8 => (3 : Fin 11)
  | 9 => (6 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L0G1_left : forall x, m11L0G1InvFun (m11L0G1To x) = x := by decide +kernel

public theorem m11L0G1_right : forall x, m11L0G1To (m11L0G1InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L0G1_left

@[expose, reducible]
public def m11L0G1 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0G1To m11L0G1InvFun m11L0G1_left m11L0G1_right

@[expose, reducible]
public def m11L0Gen : Fin 4 -> Equiv.Perm (Fin 11)
  | 0 => m11L0G0
  | 1 => m11L0G1
  | 2 => Inv.inv m11L0G0
  | 3 => Inv.inv m11L0G1
  | _ => m11L0G0

@[expose, reducible]
public def m11L0Inv : Fin 4 -> Fin 4
  | 0 => (2 : Fin 4)
  | 1 => (3 : Fin 4)
  | 2 => (0 : Fin 4)
  | 3 => (1 : Fin 4)
  | _ => (0 : Fin 4)

public theorem m11L0Inv_spec : (i : Fin 4) -> m11L0Gen (m11L0Inv i) = Inv.inv (m11L0Gen i) := by
  intro i
  fin_cases i <;> ext x <;> fin_cases x <;> rfl

public theorem m11GeneratorA_eq_m11L0G0 : m11GeneratorA = m11L0G0 := by
  ext x
  fin_cases x <;> rfl

public theorem m11GeneratorB_eq_m11L0G1 : m11GeneratorB = m11L0G1 := by
  ext x
  fin_cases x <;> rfl

@[expose, reducible]
public def m11L1G0To : Fin 11 -> Fin 11 := m11L0G0To

@[expose, reducible]
public def m11L1G0InvFun : Fin 11 -> Fin 11 := m11L0G0InvFun

public theorem m11L1G0_left : forall x, m11L1G0InvFun (m11L1G0To x) = x :=
  m11L0G0_left

public theorem m11L1G0_right : forall x, m11L1G0To (m11L1G0InvFun x) = x :=
  m11L0G0_right

@[expose, reducible]
public def m11L1G0 : Equiv.Perm (Fin 11) := m11L0G0

@[expose, reducible]
public def m11L1G1To : Fin 11 -> Fin 11
  | 0 => (3 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (9 : Fin 11)
  | 3 => (2 : Fin 11)
  | 4 => (4 : Fin 11)
  | 5 => (8 : Fin 11)
  | 6 => (5 : Fin 11)
  | 7 => (6 : Fin 11)
  | 8 => (7 : Fin 11)
  | 9 => (0 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L1G1InvFun : Fin 11 -> Fin 11
  | 0 => (9 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (3 : Fin 11)
  | 3 => (0 : Fin 11)
  | 4 => (4 : Fin 11)
  | 5 => (6 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (8 : Fin 11)
  | 8 => (5 : Fin 11)
  | 9 => (2 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L1G1_left : forall x, m11L1G1InvFun (m11L1G1To x) = x := by decide +kernel

public theorem m11L1G1_right : forall x, m11L1G1To (m11L1G1InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L1G1_left

@[expose, reducible]
public def m11L1G1 : Equiv.Perm (Fin 11) :=
  tablePerm m11L1G1To m11L1G1InvFun m11L1G1_left m11L1G1_right

@[expose, reducible]
public def m11L1Gen : Fin 4 -> Equiv.Perm (Fin 11)
  | 0 => m11L1G0
  | 1 => m11L1G1
  | 2 => Inv.inv m11L1G0
  | 3 => Inv.inv m11L1G1
  | _ => m11L1G0

@[expose, reducible]
public def m11L1Inv : Fin 4 -> Fin 4 := m11L0Inv

public theorem m11L1Inv_spec : (i : Fin 4) -> m11L1Gen (m11L1Inv i) = Inv.inv (m11L1Gen i) := by
  intro i
  fin_cases i <;> ext x <;> fin_cases x <;> rfl

@[expose, reducible]
public def m11L1GenWord : Fin 4 -> List (Fin 4)
  | 0 => [(0 : Fin 4)]
  | 1 => [(1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | 2 => [(0 : Fin 4)]
  | 3 => [(1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | _ => [(0 : Fin 4)]

public theorem m11L1Gen_eq_word : (i : Fin 4) -> m11L1Gen i = evalWord m11L0Gen (m11L1GenWord i) := by
  intro i
  fin_cases i <;> ext x <;> fin_cases x <;> rfl

@[expose, reducible]
public def m11L2G0To : Fin 11 -> Fin 11
  | 0 => (7 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (4 : Fin 11)
  | 4 => (3 : Fin 11)
  | 5 => (5 : Fin 11)
  | 6 => (8 : Fin 11)
  | 7 => (0 : Fin 11)
  | 8 => (6 : Fin 11)
  | 9 => (10 : Fin 11)
  | 10 => (9 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L2G0InvFun : Fin 11 -> Fin 11 := m11L2G0To

public theorem m11L2G0_left : forall x, m11L2G0InvFun (m11L2G0To x) = x := by decide +kernel

public theorem m11L2G0_right : forall x, m11L2G0To (m11L2G0InvFun x) = x :=
  m11L2G0_left

@[expose, reducible]
public def m11L2G0 : Equiv.Perm (Fin 11) :=
  tablePerm m11L2G0To m11L2G0InvFun m11L2G0_left m11L2G0_right

@[expose, reducible]
public def m11L2G1To : Fin 11 -> Fin 11
  | 0 => (3 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (5 : Fin 11)
  | 4 => (10 : Fin 11)
  | 5 => (9 : Fin 11)
  | 6 => (8 : Fin 11)
  | 7 => (7 : Fin 11)
  | 8 => (4 : Fin 11)
  | 9 => (0 : Fin 11)
  | 10 => (6 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L2G1InvFun : Fin 11 -> Fin 11
  | 0 => (9 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (0 : Fin 11)
  | 4 => (8 : Fin 11)
  | 5 => (3 : Fin 11)
  | 6 => (10 : Fin 11)
  | 7 => (7 : Fin 11)
  | 8 => (6 : Fin 11)
  | 9 => (5 : Fin 11)
  | 10 => (4 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L2G1_left : forall x, m11L2G1InvFun (m11L2G1To x) = x := by decide +kernel

public theorem m11L2G1_right : forall x, m11L2G1To (m11L2G1InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L2G1_left

@[expose, reducible]
public def m11L2G1 : Equiv.Perm (Fin 11) :=
  tablePerm m11L2G1To m11L2G1InvFun m11L2G1_left m11L2G1_right

@[expose, reducible]
public def m11L2G2To : Fin 11 -> Fin 11
  | 0 => (9 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (10 : Fin 11)
  | 5 => (6 : Fin 11)
  | 6 => (4 : Fin 11)
  | 7 => (0 : Fin 11)
  | 8 => (7 : Fin 11)
  | 9 => (8 : Fin 11)
  | 10 => (5 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L2G2InvFun : Fin 11 -> Fin 11
  | 0 => (7 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (6 : Fin 11)
  | 5 => (10 : Fin 11)
  | 6 => (5 : Fin 11)
  | 7 => (8 : Fin 11)
  | 8 => (9 : Fin 11)
  | 9 => (0 : Fin 11)
  | 10 => (4 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L2G2_left : forall x, m11L2G2InvFun (m11L2G2To x) = x := by decide +kernel

public theorem m11L2G2_right : forall x, m11L2G2To (m11L2G2InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L2G2_left

@[expose, reducible]
public def m11L2G2 : Equiv.Perm (Fin 11) :=
  tablePerm m11L2G2To m11L2G2InvFun m11L2G2_left m11L2G2_right

@[expose, reducible]
public def m11L2Gen : Fin 6 -> Equiv.Perm (Fin 11)
  | 0 => m11L2G0
  | 1 => m11L2G1
  | 2 => m11L2G2
  | 3 => Inv.inv m11L2G0
  | 4 => Inv.inv m11L2G1
  | 5 => Inv.inv m11L2G2
  | _ => m11L2G0

@[expose, reducible]
public def m11L2Inv : Fin 6 -> Fin 6
  | 0 => (3 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (5 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (1 : Fin 6)
  | 5 => (2 : Fin 6)
  | _ => (0 : Fin 6)

public theorem m11L2Inv_spec : (i : Fin 6) -> m11L2Gen (m11L2Inv i) = Inv.inv (m11L2Gen i) := by
  intro i
  fin_cases i <;> ext x <;> fin_cases x <;> rfl

@[expose, reducible]
public def m11L2GenWord : Fin 6 -> List (Fin 4)
  | 0 => [(1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | 1 => [(3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | 2 => [(0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | 3 => [(1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | 4 => [(3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | 5 => [(1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4)]
  | _ => [(1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]

public theorem m11L2Gen_eq_word : (i : Fin 6) -> m11L2Gen i = evalWord m11L1Gen (m11L2GenWord i) := by
  intro i
  fin_cases i <;> ext x <;> fin_cases x <;> rfl

@[expose, reducible]
public def m11L3G0To : Fin 11 -> Fin 11
  | 0 => (8 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (5 : Fin 11)
  | 5 => (4 : Fin 11)
  | 6 => (10 : Fin 11)
  | 7 => (9 : Fin 11)
  | 8 => (0 : Fin 11)
  | 9 => (7 : Fin 11)
  | 10 => (6 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L3G0InvFun : Fin 11 -> Fin 11 := m11L3G0To

public theorem m11L3G0_left : forall x, m11L3G0InvFun (m11L3G0To x) = x := by decide +kernel

public theorem m11L3G0_right : forall x, m11L3G0To (m11L3G0InvFun x) = x :=
  m11L3G0_left

@[expose, reducible]
public def m11L3G0 : Equiv.Perm (Fin 11) :=
  tablePerm m11L3G0To m11L3G0InvFun m11L3G0_left m11L3G0_right

@[expose, reducible]
public def m11L3G1To : Fin 11 -> Fin 11
  | 0 => (4 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (8 : Fin 11)
  | 5 => (0 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (10 : Fin 11)
  | 8 => (5 : Fin 11)
  | 9 => (6 : Fin 11)
  | 10 => (9 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L3G1InvFun : Fin 11 -> Fin 11
  | 0 => (5 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (0 : Fin 11)
  | 5 => (8 : Fin 11)
  | 6 => (9 : Fin 11)
  | 7 => (6 : Fin 11)
  | 8 => (4 : Fin 11)
  | 9 => (10 : Fin 11)
  | 10 => (7 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L3G1_left : forall x, m11L3G1InvFun (m11L3G1To x) = x := by decide +kernel

public theorem m11L3G1_right : forall x, m11L3G1To (m11L3G1InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L3G1_left

@[expose, reducible]
public def m11L3G1 : Equiv.Perm (Fin 11) :=
  tablePerm m11L3G1To m11L3G1InvFun m11L3G1_left m11L3G1_right

@[expose, reducible]
public def m11L3G2To : Fin 11 -> Fin 11 := m11L2G2To

@[expose, reducible]
public def m11L3G2InvFun : Fin 11 -> Fin 11 := m11L2G2InvFun

public theorem m11L3G2_left : forall x, m11L3G2InvFun (m11L3G2To x) = x :=
  m11L2G2_left

public theorem m11L3G2_right : forall x, m11L3G2To (m11L3G2InvFun x) = x :=
  m11L2G2_right

@[expose, reducible]
public def m11L3G2 : Equiv.Perm (Fin 11) := m11L2G2

@[expose, reducible]
public def m11L3Gen : Fin 6 -> Equiv.Perm (Fin 11)
  | 0 => m11L3G0
  | 1 => m11L3G1
  | 2 => m11L3G2
  | 3 => Inv.inv m11L3G0
  | 4 => Inv.inv m11L3G1
  | 5 => Inv.inv m11L3G2
  | _ => m11L3G0

@[expose, reducible]
public def m11L3Inv : Fin 6 -> Fin 6 := m11L2Inv

public theorem m11L3Inv_spec : (i : Fin 6) -> m11L3Gen (m11L3Inv i) = Inv.inv (m11L3Gen i) := by
  intro i
  fin_cases i <;> ext x <;> fin_cases x <;> rfl

@[expose, reducible]
public def m11L3GenWord : Fin 6 -> List (Fin 6)
  | 0 => [(2 : Fin 6), (2 : Fin 6)]
  | 1 => [(0 : Fin 6), (2 : Fin 6), (2 : Fin 6), (1 : Fin 6)]
  | 2 => [(2 : Fin 6)]
  | 3 => [(2 : Fin 6), (2 : Fin 6)]
  | 4 => [(4 : Fin 6), (2 : Fin 6), (2 : Fin 6), (0 : Fin 6)]
  | 5 => [(5 : Fin 6)]
  | _ => [(2 : Fin 6), (2 : Fin 6)]

public theorem m11L3Gen_eq_word : (i : Fin 6) -> m11L3Gen i = evalWord m11L2Gen (m11L3GenWord i) := by
  intro i
  fin_cases i <;> ext x <;> fin_cases x <;> rfl

@[expose, reducible]
public def m11L4Gen : Fin 0 -> Equiv.Perm (Fin 11) := fun i => nomatch i

@[expose, reducible]
public def m11L4Inv : Fin 0 -> Fin 0 := fun i => nomatch i

public theorem m11L4Inv_spec : (i : Fin 0) -> m11L4Gen (m11L4Inv i) = Inv.inv (m11L4Gen i) := by
  intro i
  exact Fin.elim0 i
end M11OrderCertificate

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace M11OrderCertificate
@[expose, reducible]
public def m11L0R0To : Fin 11 -> Fin 11
  | 0 => (0 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (4 : Fin 11)
  | 5 => (5 : Fin 11)
  | 6 => (6 : Fin 11)
  | 7 => (7 : Fin 11)
  | 8 => (8 : Fin 11)
  | 9 => (9 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0R0InvFun : Fin 11 -> Fin 11 := m11L0R0To

public theorem m11L0R0_left : forall x, m11L0R0InvFun (m11L0R0To x) = x := by decide +kernel

public theorem m11L0R0_right : forall x, m11L0R0To (m11L0R0InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L0R0_left

@[expose, reducible]
public def m11L0R0 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0R0To m11L0R0InvFun m11L0R0_left m11L0R0_right

@[expose, reducible]
public def m11L0R1To : Fin 11 -> Fin 11
  | 0 => (0 : Fin 11)
  | 1 => (8 : Fin 11)
  | 2 => (9 : Fin 11)
  | 3 => (4 : Fin 11)
  | 4 => (1 : Fin 11)
  | 5 => (2 : Fin 11)
  | 6 => (5 : Fin 11)
  | 7 => (7 : Fin 11)
  | 8 => (3 : Fin 11)
  | 9 => (6 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0R1InvFun : Fin 11 -> Fin 11
  | 0 => (0 : Fin 11)
  | 1 => (4 : Fin 11)
  | 2 => (5 : Fin 11)
  | 3 => (8 : Fin 11)
  | 4 => (3 : Fin 11)
  | 5 => (6 : Fin 11)
  | 6 => (9 : Fin 11)
  | 7 => (7 : Fin 11)
  | 8 => (1 : Fin 11)
  | 9 => (2 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L0R1_left : forall x, m11L0R1InvFun (m11L0R1To x) = x := by decide +kernel

public theorem m11L0R1_right : forall x, m11L0R1To (m11L0R1InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L0R1_left

@[expose, reducible]
public def m11L0R1 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0R1To m11L0R1InvFun m11L0R1_left m11L0R1_right

@[expose, reducible]
public def m11L0R2To : Fin 11 -> Fin 11
  | 0 => (4 : Fin 11)
  | 1 => (9 : Fin 11)
  | 2 => (8 : Fin 11)
  | 3 => (0 : Fin 11)
  | 4 => (1 : Fin 11)
  | 5 => (10 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (5 : Fin 11)
  | 8 => (3 : Fin 11)
  | 9 => (6 : Fin 11)
  | 10 => (2 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0R2InvFun : Fin 11 -> Fin 11
  | 0 => (3 : Fin 11)
  | 1 => (4 : Fin 11)
  | 2 => (10 : Fin 11)
  | 3 => (8 : Fin 11)
  | 4 => (0 : Fin 11)
  | 5 => (7 : Fin 11)
  | 6 => (9 : Fin 11)
  | 7 => (6 : Fin 11)
  | 8 => (2 : Fin 11)
  | 9 => (1 : Fin 11)
  | 10 => (5 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L0R2_left : forall x, m11L0R2InvFun (m11L0R2To x) = x := by decide +kernel

public theorem m11L0R2_right : forall x, m11L0R2To (m11L0R2InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L0R2_left

@[expose, reducible]
public def m11L0R2 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0R2To m11L0R2InvFun m11L0R2_left m11L0R2_right

@[expose, reducible]
public def m11L0R3To : Fin 11 -> Fin 11
  | 0 => (0 : Fin 11)
  | 1 => (3 : Fin 11)
  | 2 => (6 : Fin 11)
  | 3 => (1 : Fin 11)
  | 4 => (8 : Fin 11)
  | 5 => (9 : Fin 11)
  | 6 => (2 : Fin 11)
  | 7 => (7 : Fin 11)
  | 8 => (4 : Fin 11)
  | 9 => (5 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0R3InvFun : Fin 11 -> Fin 11 := m11L0R3To

public theorem m11L0R3_left : forall x, m11L0R3InvFun (m11L0R3To x) = x := by decide +kernel

public theorem m11L0R3_right : forall x, m11L0R3To (m11L0R3InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L0R3_left

@[expose, reducible]
public def m11L0R3 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0R3To m11L0R3InvFun m11L0R3_left m11L0R3_right

@[expose, reducible]
public def m11L0R4To : Fin 11 -> Fin 11
  | 0 => (1 : Fin 11)
  | 1 => (6 : Fin 11)
  | 2 => (3 : Fin 11)
  | 3 => (0 : Fin 11)
  | 4 => (8 : Fin 11)
  | 5 => (10 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (2 : Fin 11)
  | 8 => (4 : Fin 11)
  | 9 => (5 : Fin 11)
  | 10 => (9 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0R4InvFun : Fin 11 -> Fin 11
  | 0 => (3 : Fin 11)
  | 1 => (0 : Fin 11)
  | 2 => (7 : Fin 11)
  | 3 => (2 : Fin 11)
  | 4 => (8 : Fin 11)
  | 5 => (9 : Fin 11)
  | 6 => (1 : Fin 11)
  | 7 => (6 : Fin 11)
  | 8 => (4 : Fin 11)
  | 9 => (10 : Fin 11)
  | 10 => (5 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L0R4_left : forall x, m11L0R4InvFun (m11L0R4To x) = x := by decide +kernel

public theorem m11L0R4_right : forall x, m11L0R4To (m11L0R4InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L0R4_left

@[expose, reducible]
public def m11L0R4 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0R4To m11L0R4InvFun m11L0R4_left m11L0R4_right

@[expose, reducible]
public def m11L0R5To : Fin 11 -> Fin 11 := m11L0R1InvFun

@[expose, reducible]
public def m11L0R5InvFun : Fin 11 -> Fin 11 := m11L0R1To

public theorem m11L0R5_left : forall x, m11L0R5InvFun (m11L0R5To x) = x :=
  m11L0R1_right

public theorem m11L0R5_right : forall x, m11L0R5To (m11L0R5InvFun x) = x :=
  m11L0R1_left

@[expose, reducible]
public def m11L0R5 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0R5To m11L0R5InvFun m11L0R5_left m11L0R5_right

@[expose, reducible]
public def m11L0R6To : Fin 11 -> Fin 11
  | 0 => (8 : Fin 11)
  | 1 => (5 : Fin 11)
  | 2 => (4 : Fin 11)
  | 3 => (0 : Fin 11)
  | 4 => (3 : Fin 11)
  | 5 => (10 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (9 : Fin 11)
  | 8 => (1 : Fin 11)
  | 9 => (2 : Fin 11)
  | 10 => (6 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0R6InvFun : Fin 11 -> Fin 11
  | 0 => (3 : Fin 11)
  | 1 => (8 : Fin 11)
  | 2 => (9 : Fin 11)
  | 3 => (4 : Fin 11)
  | 4 => (2 : Fin 11)
  | 5 => (1 : Fin 11)
  | 6 => (10 : Fin 11)
  | 7 => (6 : Fin 11)
  | 8 => (0 : Fin 11)
  | 9 => (7 : Fin 11)
  | 10 => (5 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L0R6_left : forall x, m11L0R6InvFun (m11L0R6To x) = x := by decide +kernel

public theorem m11L0R6_right : forall x, m11L0R6To (m11L0R6InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L0R6_left

@[expose, reducible]
public def m11L0R6 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0R6To m11L0R6InvFun m11L0R6_left m11L0R6_right

@[expose, reducible]
public def m11L0R7To : Fin 11 -> Fin 11
  | 0 => (4 : Fin 11)
  | 1 => (0 : Fin 11)
  | 2 => (7 : Fin 11)
  | 3 => (9 : Fin 11)
  | 4 => (3 : Fin 11)
  | 5 => (6 : Fin 11)
  | 6 => (8 : Fin 11)
  | 7 => (5 : Fin 11)
  | 8 => (1 : Fin 11)
  | 9 => (10 : Fin 11)
  | 10 => (2 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0R7InvFun : Fin 11 -> Fin 11
  | 0 => (1 : Fin 11)
  | 1 => (8 : Fin 11)
  | 2 => (10 : Fin 11)
  | 3 => (4 : Fin 11)
  | 4 => (0 : Fin 11)
  | 5 => (7 : Fin 11)
  | 6 => (5 : Fin 11)
  | 7 => (2 : Fin 11)
  | 8 => (6 : Fin 11)
  | 9 => (3 : Fin 11)
  | 10 => (9 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L0R7_left : forall x, m11L0R7InvFun (m11L0R7To x) = x := by decide +kernel

public theorem m11L0R7_right : forall x, m11L0R7To (m11L0R7InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L0R7_left

@[expose, reducible]
public def m11L0R7 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0R7To m11L0R7InvFun m11L0R7_left m11L0R7_right

@[expose, reducible]
public def m11L0R8To : Fin 11 -> Fin 11
  | 0 => (9 : Fin 11)
  | 1 => (7 : Fin 11)
  | 2 => (0 : Fin 11)
  | 3 => (4 : Fin 11)
  | 4 => (3 : Fin 11)
  | 5 => (2 : Fin 11)
  | 6 => (5 : Fin 11)
  | 7 => (8 : Fin 11)
  | 8 => (1 : Fin 11)
  | 9 => (10 : Fin 11)
  | 10 => (6 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0R8InvFun : Fin 11 -> Fin 11
  | 0 => (2 : Fin 11)
  | 1 => (8 : Fin 11)
  | 2 => (5 : Fin 11)
  | 3 => (4 : Fin 11)
  | 4 => (3 : Fin 11)
  | 5 => (6 : Fin 11)
  | 6 => (10 : Fin 11)
  | 7 => (1 : Fin 11)
  | 8 => (7 : Fin 11)
  | 9 => (0 : Fin 11)
  | 10 => (9 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L0R8_left : forall x, m11L0R8InvFun (m11L0R8To x) = x := by decide +kernel

public theorem m11L0R8_right : forall x, m11L0R8To (m11L0R8InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L0R8_left

@[expose, reducible]
public def m11L0R8 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0R8To m11L0R8InvFun m11L0R8_left m11L0R8_right

@[expose, reducible]
public def m11L0R9To : Fin 11 -> Fin 11
  | 0 => (3 : Fin 11)
  | 1 => (2 : Fin 11)
  | 2 => (1 : Fin 11)
  | 3 => (0 : Fin 11)
  | 4 => (4 : Fin 11)
  | 5 => (10 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (6 : Fin 11)
  | 8 => (8 : Fin 11)
  | 9 => (9 : Fin 11)
  | 10 => (5 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0R9InvFun : Fin 11 -> Fin 11 := m11L0R9To

public theorem m11L0R9_left : forall x, m11L0R9InvFun (m11L0R9To x) = x := by decide +kernel

public theorem m11L0R9_right : forall x, m11L0R9To (m11L0R9InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L0R9_left

@[expose, reducible]
public def m11L0R9 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0R9To m11L0R9InvFun m11L0R9_left m11L0R9_right

@[expose, reducible]
public def m11L0R10To : Fin 11 -> Fin 11
  | 0 => (3 : Fin 11)
  | 1 => (10 : Fin 11)
  | 2 => (1 : Fin 11)
  | 3 => (4 : Fin 11)
  | 4 => (0 : Fin 11)
  | 5 => (2 : Fin 11)
  | 6 => (5 : Fin 11)
  | 7 => (6 : Fin 11)
  | 8 => (9 : Fin 11)
  | 9 => (8 : Fin 11)
  | 10 => (7 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0R10InvFun : Fin 11 -> Fin 11
  | 0 => (4 : Fin 11)
  | 1 => (2 : Fin 11)
  | 2 => (5 : Fin 11)
  | 3 => (0 : Fin 11)
  | 4 => (3 : Fin 11)
  | 5 => (6 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (10 : Fin 11)
  | 8 => (9 : Fin 11)
  | 9 => (8 : Fin 11)
  | 10 => (1 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L0R10_left : forall x, m11L0R10InvFun (m11L0R10To x) = x := by decide +kernel

public theorem m11L0R10_right : forall x, m11L0R10To (m11L0R10InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L0R10_left

@[expose, reducible]
public def m11L0R10 : Equiv.Perm (Fin 11) :=
  tablePerm m11L0R10To m11L0R10InvFun m11L0R10_left m11L0R10_right

@[expose, reducible]
public def m11L0RepWord : Fin 11 -> List (Fin 4)
  | 0 => []
  | 1 => [(3 : Fin 4)]
  | 2 => [(0 : Fin 4), (3 : Fin 4)]
  | 3 => [(1 : Fin 4), (1 : Fin 4)]
  | 4 => [(3 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | 5 => [(1 : Fin 4)]
  | 6 => [(1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | 7 => [(0 : Fin 4), (1 : Fin 4)]
  | 8 => [(0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | 9 => [(1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | 10 => [(0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | _ => []

@[expose, reducible]
public def m11L0Rep : Fin 11 -> Equiv.Perm (Fin 11)
  | 0 => m11L0R0
  | 1 => m11L0R1
  | 2 => m11L0R2
  | 3 => m11L0R3
  | 4 => m11L0R4
  | 5 => m11L0R5
  | 6 => m11L0R6
  | 7 => m11L0R7
  | 8 => m11L0R8
  | 9 => m11L0R9
  | 10 => m11L0R10
  | _ => m11L0R0

public theorem m11L0Rep_eq_word : (r : Fin 11) -> m11L0Rep r = evalWord m11L0Gen (m11L0RepWord r) := by decide +kernel

@[expose, reducible]
public def m11L0Point : Fin 11 -> Fin 11
  | 0 => (1 : Fin 11)
  | 1 => (8 : Fin 11)
  | 2 => (9 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (6 : Fin 11)
  | 5 => (4 : Fin 11)
  | 6 => (5 : Fin 11)
  | 7 => (0 : Fin 11)
  | 8 => (7 : Fin 11)
  | 9 => (2 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L0Act : Fin 4 -> Fin 11 -> Fin 11
  | 0, 0 => (0 : Fin 11)
  | 0, 1 => (2 : Fin 11)
  | 0, 2 => (1 : Fin 11)
  | 0, 3 => (3 : Fin 11)
  | 0, 4 => (4 : Fin 11)
  | 0, 5 => (7 : Fin 11)
  | 0, 6 => (8 : Fin 11)
  | 0, 7 => (5 : Fin 11)
  | 0, 8 => (6 : Fin 11)
  | 0, 9 => (10 : Fin 11)
  | 0, 10 => (9 : Fin 11)
  | 1, 0 => (5 : Fin 11)
  | 1, 1 => (0 : Fin 11)
  | 1, 2 => (9 : Fin 11)
  | 1, 3 => (1 : Fin 11)
  | 1, 4 => (2 : Fin 11)
  | 1, 5 => (3 : Fin 11)
  | 1, 6 => (4 : Fin 11)
  | 1, 7 => (7 : Fin 11)
  | 1, 8 => (8 : Fin 11)
  | 1, 9 => (6 : Fin 11)
  | 1, 10 => (10 : Fin 11)
  | 2, 0 => (0 : Fin 11)
  | 2, 1 => (2 : Fin 11)
  | 2, 2 => (1 : Fin 11)
  | 2, 3 => (3 : Fin 11)
  | 2, 4 => (4 : Fin 11)
  | 2, 5 => (7 : Fin 11)
  | 2, 6 => (8 : Fin 11)
  | 2, 7 => (5 : Fin 11)
  | 2, 8 => (6 : Fin 11)
  | 2, 9 => (10 : Fin 11)
  | 2, 10 => (9 : Fin 11)
  | 3, 0 => (1 : Fin 11)
  | 3, 1 => (3 : Fin 11)
  | 3, 2 => (4 : Fin 11)
  | 3, 3 => (5 : Fin 11)
  | 3, 4 => (6 : Fin 11)
  | 3, 5 => (0 : Fin 11)
  | 3, 6 => (9 : Fin 11)
  | 3, 7 => (7 : Fin 11)
  | 3, 8 => (8 : Fin 11)
  | 3, 9 => (2 : Fin 11)
  | 3, 10 => (10 : Fin 11)
  | _, _ => (0 : Fin 11)

@[expose, reducible]
public def m11L0Factor : Fin 4 -> Fin 11 -> List (Fin 4)
  | 0, 0 => [(0 : Fin 4)]
  | 0, 1 => []
  | 0, 2 => []
  | 0, 3 => [(3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | 0, 4 => [(0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4)]
  | 0, 5 => []
  | 0, 6 => []
  | 0, 7 => []
  | 0, 8 => []
  | 0, 9 => []
  | 0, 10 => []
  | 1, 0 => []
  | 1, 1 => []
  | 1, 2 => []
  | 1, 3 => []
  | 1, 4 => []
  | 1, 5 => []
  | 1, 6 => []
  | 1, 7 => [(0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]
  | 1, 8 => [(0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4)]
  | 1, 9 => []
  | 1, 10 => [(3 : Fin 4)]
  | 2, 0 => [(0 : Fin 4)]
  | 2, 1 => []
  | 2, 2 => []
  | 2, 3 => [(3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | 2, 4 => [(0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4)]
  | 2, 5 => []
  | 2, 6 => []
  | 2, 7 => []
  | 2, 8 => []
  | 2, 9 => []
  | 2, 10 => []
  | 3, 0 => []
  | 3, 1 => []
  | 3, 2 => []
  | 3, 3 => []
  | 3, 4 => []
  | 3, 5 => []
  | 3, 6 => []
  | 3, 7 => [(1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4)]
  | 3, 8 => [(0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4)]
  | 3, 9 => []
  | 3, 10 => [(1 : Fin 4)]
  | _, _ => [(0 : Fin 4)]

public theorem m11L0RepBase : m11L0Rep (0 : Fin 11) = 1 := by decide +kernel

public theorem m11L0RepPoint : (r : Fin 11) -> m11L0Rep r (1 : Fin 11) = m11L0Point r := by decide +kernel

@[expose, reducible]
public def m11L0PointInv : Fin 11 -> Fin 11
  | 0 => (7 : Fin 11)
  | 1 => (0 : Fin 11)
  | 2 => (9 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (5 : Fin 11)
  | 5 => (6 : Fin 11)
  | 6 => (4 : Fin 11)
  | 7 => (8 : Fin 11)
  | 8 => (1 : Fin 11)
  | 9 => (2 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (7 : Fin 11)

public theorem m11L0PointInv_left : (r : Fin 11) -> m11L0PointInv (m11L0Point r) = r := by decide +kernel

public theorem m11L0Point_injective : Function.Injective m11L0Point := by
  intro x y h
  have hh := congrArg m11L0PointInv h
  simpa [m11L0PointInv_left] using hh

public theorem m11L0Step : (i : Fin 4) -> (r : Fin 11) -> m11L0Gen i * m11L0Rep r = m11L0Rep (m11L0Act i r) * evalWord m11L1Gen (m11L0Factor i r) := by decide +kernel

public theorem m11L0_card :
    Nat.card (wordSubgroup m11L0Gen m11L0Inv m11L0Inv_spec) =
      11 * Nat.card (wordSubgroup m11L1Gen m11L1Inv m11L1Inv_spec) :=
  wordSubgroup_card_eq_mul_next
    m11L0Gen m11L0Inv m11L0Inv_spec
    m11L1Gen m11L1Inv m11L1Inv_spec
    m11L0Rep m11L0Act m11L0Factor (1 : Fin 11) m11L0Point (0 : Fin 11)
    (fun r => by rw [m11L0Rep_eq_word r]; exact evalWord_mem_wordSubgroup m11L0Gen m11L0Inv m11L0Inv_spec (m11L0RepWord r))
    (wordSubgroup_le_of_gen_mem (fun i => by rw [m11L1Gen_eq_word i]; exact evalWord_mem_wordSubgroup m11L0Gen m11L0Inv m11L0Inv_spec (m11L1GenWord i)))
    m11L0RepBase m11L0RepPoint m11L0Point_injective
    (wordSubgroup_fix_of_gen_fix m11L1Gen m11L1Inv m11L1Inv_spec (by decide +kernel))
    m11L0Step

end M11OrderCertificate

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace M11OrderCertificate
@[expose, reducible]
public def m11L1R0To : Fin 11 -> Fin 11 := m11L0R0To

@[expose, reducible]
public def m11L1R0InvFun : Fin 11 -> Fin 11 := m11L0R0InvFun

public theorem m11L1R0_left : forall x, m11L1R0InvFun (m11L1R0To x) = x :=
  m11L0R0_left

public theorem m11L1R0_right : forall x, m11L1R0To (m11L1R0InvFun x) = x :=
  m11L0R0_right

@[expose, reducible]
public def m11L1R0 : Equiv.Perm (Fin 11) := m11L0R0

@[expose, reducible]
public def m11L1R1To : Fin 11 -> Fin 11
  | 0 => (4 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (10 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (0 : Fin 11)
  | 5 => (7 : Fin 11)
  | 6 => (6 : Fin 11)
  | 7 => (5 : Fin 11)
  | 8 => (9 : Fin 11)
  | 9 => (8 : Fin 11)
  | 10 => (2 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L1R1InvFun : Fin 11 -> Fin 11 := m11L1R1To

public theorem m11L1R1_left : forall x, m11L1R1InvFun (m11L1R1To x) = x := by decide +kernel

public theorem m11L1R1_right : forall x, m11L1R1To (m11L1R1InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L1R1_left

@[expose, reducible]
public def m11L1R1 : Equiv.Perm (Fin 11) :=
  tablePerm m11L1R1To m11L1R1InvFun m11L1R1_left m11L1R1_right

@[expose, reducible]
public def m11L1R2To : Fin 11 -> Fin 11
  | 0 => (9 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (3 : Fin 11)
  | 3 => (0 : Fin 11)
  | 4 => (4 : Fin 11)
  | 5 => (6 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (8 : Fin 11)
  | 8 => (5 : Fin 11)
  | 9 => (2 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L1R2InvFun : Fin 11 -> Fin 11
  | 0 => (3 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (9 : Fin 11)
  | 3 => (2 : Fin 11)
  | 4 => (4 : Fin 11)
  | 5 => (8 : Fin 11)
  | 6 => (5 : Fin 11)
  | 7 => (6 : Fin 11)
  | 8 => (7 : Fin 11)
  | 9 => (0 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L1R2_left : forall x, m11L1R2InvFun (m11L1R2To x) = x := by decide +kernel

public theorem m11L1R2_right : forall x, m11L1R2To (m11L1R2InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L1R2_left

@[expose, reducible]
public def m11L1R2 : Equiv.Perm (Fin 11) :=
  tablePerm m11L1R2To m11L1R2InvFun m11L1R2_left m11L1R2_right

@[expose, reducible]
public def m11L1R3To : Fin 11 -> Fin 11
  | 0 => (2 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (0 : Fin 11)
  | 3 => (9 : Fin 11)
  | 4 => (4 : Fin 11)
  | 5 => (7 : Fin 11)
  | 6 => (8 : Fin 11)
  | 7 => (5 : Fin 11)
  | 8 => (6 : Fin 11)
  | 9 => (3 : Fin 11)
  | 10 => (10 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L1R3InvFun : Fin 11 -> Fin 11 := m11L1R3To

public theorem m11L1R3_left : forall x, m11L1R3InvFun (m11L1R3To x) = x := by decide +kernel

public theorem m11L1R3_right : forall x, m11L1R3To (m11L1R3InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L1R3_left

@[expose, reducible]
public def m11L1R3 : Equiv.Perm (Fin 11) :=
  tablePerm m11L1R3To m11L1R3InvFun m11L1R3_left m11L1R3_right

@[expose, reducible]
public def m11L1R4To : Fin 11 -> Fin 11
  | 0 => (10 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (4 : Fin 11)
  | 3 => (8 : Fin 11)
  | 4 => (0 : Fin 11)
  | 5 => (5 : Fin 11)
  | 6 => (9 : Fin 11)
  | 7 => (7 : Fin 11)
  | 8 => (6 : Fin 11)
  | 9 => (3 : Fin 11)
  | 10 => (2 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L1R4InvFun : Fin 11 -> Fin 11
  | 0 => (4 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (10 : Fin 11)
  | 3 => (9 : Fin 11)
  | 4 => (2 : Fin 11)
  | 5 => (5 : Fin 11)
  | 6 => (8 : Fin 11)
  | 7 => (7 : Fin 11)
  | 8 => (3 : Fin 11)
  | 9 => (6 : Fin 11)
  | 10 => (0 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L1R4_left : forall x, m11L1R4InvFun (m11L1R4To x) = x := by decide +kernel

public theorem m11L1R4_right : forall x, m11L1R4To (m11L1R4InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L1R4_left

@[expose, reducible]
public def m11L1R4 : Equiv.Perm (Fin 11) :=
  tablePerm m11L1R4To m11L1R4InvFun m11L1R4_left m11L1R4_right

@[expose, reducible]
public def m11L1R5To : Fin 11 -> Fin 11 := m11L1R2InvFun

@[expose, reducible]
public def m11L1R5InvFun : Fin 11 -> Fin 11 := m11L1R2To

public theorem m11L1R5_left : forall x, m11L1R5InvFun (m11L1R5To x) = x :=
  m11L1R2_right

public theorem m11L1R5_right : forall x, m11L1R5To (m11L1R5InvFun x) = x :=
  m11L1R2_left

@[expose, reducible]
public def m11L1R5 : Equiv.Perm (Fin 11) :=
  tablePerm m11L1R5To m11L1R5InvFun m11L1R5_left m11L1R5_right

@[expose, reducible]
public def m11L1R6To : Fin 11 -> Fin 11
  | 0 => (3 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (8 : Fin 11)
  | 3 => (10 : Fin 11)
  | 4 => (0 : Fin 11)
  | 5 => (9 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (6 : Fin 11)
  | 8 => (5 : Fin 11)
  | 9 => (4 : Fin 11)
  | 10 => (2 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L1R6InvFun : Fin 11 -> Fin 11
  | 0 => (4 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (10 : Fin 11)
  | 3 => (0 : Fin 11)
  | 4 => (9 : Fin 11)
  | 5 => (8 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (6 : Fin 11)
  | 8 => (2 : Fin 11)
  | 9 => (5 : Fin 11)
  | 10 => (3 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L1R6_left : forall x, m11L1R6InvFun (m11L1R6To x) = x := by decide +kernel

public theorem m11L1R6_right : forall x, m11L1R6To (m11L1R6InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L1R6_left

@[expose, reducible]
public def m11L1R6 : Equiv.Perm (Fin 11) :=
  tablePerm m11L1R6To m11L1R6InvFun m11L1R6_left m11L1R6_right

@[expose, reducible]
public def m11L1R7To : Fin 11 -> Fin 11
  | 0 => (0 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (5 : Fin 11)
  | 3 => (10 : Fin 11)
  | 4 => (9 : Fin 11)
  | 5 => (2 : Fin 11)
  | 6 => (8 : Fin 11)
  | 7 => (7 : Fin 11)
  | 8 => (6 : Fin 11)
  | 9 => (4 : Fin 11)
  | 10 => (3 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L1R7InvFun : Fin 11 -> Fin 11 := m11L1R7To

public theorem m11L1R7_left : forall x, m11L1R7InvFun (m11L1R7To x) = x := by decide +kernel

public theorem m11L1R7_right : forall x, m11L1R7To (m11L1R7InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L1R7_left

@[expose, reducible]
public def m11L1R7 : Equiv.Perm (Fin 11) :=
  tablePerm m11L1R7To m11L1R7InvFun m11L1R7_left m11L1R7_right

@[expose, reducible]
public def m11L1R8To : Fin 11 -> Fin 11
  | 0 => (4 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (7 : Fin 11)
  | 3 => (2 : Fin 11)
  | 4 => (8 : Fin 11)
  | 5 => (10 : Fin 11)
  | 6 => (9 : Fin 11)
  | 7 => (5 : Fin 11)
  | 8 => (6 : Fin 11)
  | 9 => (0 : Fin 11)
  | 10 => (3 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L1R8InvFun : Fin 11 -> Fin 11
  | 0 => (9 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (3 : Fin 11)
  | 3 => (10 : Fin 11)
  | 4 => (0 : Fin 11)
  | 5 => (7 : Fin 11)
  | 6 => (8 : Fin 11)
  | 7 => (2 : Fin 11)
  | 8 => (4 : Fin 11)
  | 9 => (6 : Fin 11)
  | 10 => (5 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L1R8_left : forall x, m11L1R8InvFun (m11L1R8To x) = x := by decide +kernel

public theorem m11L1R8_right : forall x, m11L1R8To (m11L1R8InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L1R8_left

@[expose, reducible]
public def m11L1R8 : Equiv.Perm (Fin 11) :=
  tablePerm m11L1R8To m11L1R8InvFun m11L1R8_left m11L1R8_right

@[expose, reducible]
public def m11L1R9To : Fin 11 -> Fin 11
  | 0 => (9 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (6 : Fin 11)
  | 3 => (10 : Fin 11)
  | 4 => (2 : Fin 11)
  | 5 => (3 : Fin 11)
  | 6 => (5 : Fin 11)
  | 7 => (8 : Fin 11)
  | 8 => (7 : Fin 11)
  | 9 => (4 : Fin 11)
  | 10 => (0 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L1R9InvFun : Fin 11 -> Fin 11
  | 0 => (10 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (4 : Fin 11)
  | 3 => (5 : Fin 11)
  | 4 => (9 : Fin 11)
  | 5 => (6 : Fin 11)
  | 6 => (2 : Fin 11)
  | 7 => (8 : Fin 11)
  | 8 => (7 : Fin 11)
  | 9 => (0 : Fin 11)
  | 10 => (3 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L1R9_left : forall x, m11L1R9InvFun (m11L1R9To x) = x := by decide +kernel

public theorem m11L1R9_right : forall x, m11L1R9To (m11L1R9InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L1R9_left

@[expose, reducible]
public def m11L1R9 : Equiv.Perm (Fin 11) :=
  tablePerm m11L1R9To m11L1R9InvFun m11L1R9_left m11L1R9_right

@[expose, reducible]
public def m11L1RepWord : Fin 10 -> List (Fin 4)
  | 0 => []
  | 1 => [(0 : Fin 4)]
  | 2 => [(3 : Fin 4)]
  | 3 => [(1 : Fin 4), (1 : Fin 4)]
  | 4 => [(0 : Fin 4), (1 : Fin 4), (1 : Fin 4)]
  | 5 => [(1 : Fin 4)]
  | 6 => [(0 : Fin 4), (1 : Fin 4)]
  | 7 => [(3 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | 8 => [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | 9 => [(1 : Fin 4), (1 : Fin 4), (0 : Fin 4), (1 : Fin 4)]
  | _ => []

@[expose, reducible]
public def m11L1Rep : Fin 10 -> Equiv.Perm (Fin 11)
  | 0 => m11L1R0
  | 1 => m11L1R1
  | 2 => m11L1R2
  | 3 => m11L1R3
  | 4 => m11L1R4
  | 5 => m11L1R5
  | 6 => m11L1R6
  | 7 => m11L1R7
  | 8 => m11L1R8
  | 9 => m11L1R9
  | _ => m11L1R0

public theorem m11L1Rep_eq_word : (r : Fin 10) -> m11L1Rep r = evalWord m11L1Gen (m11L1RepWord r) := by decide +kernel

@[expose, reducible]
public def m11L1Point : Fin 10 -> Fin 11
  | 0 => (2 : Fin 11)
  | 1 => (10 : Fin 11)
  | 2 => (3 : Fin 11)
  | 3 => (0 : Fin 11)
  | 4 => (4 : Fin 11)
  | 5 => (9 : Fin 11)
  | 6 => (8 : Fin 11)
  | 7 => (5 : Fin 11)
  | 8 => (7 : Fin 11)
  | 9 => (6 : Fin 11)
  | _ => (2 : Fin 11)

@[expose, reducible]
public def m11L1Act : Fin 4 -> Fin 10 -> Fin 10
  | 0, 0 => (1 : Fin 10)
  | 0, 1 => (0 : Fin 10)
  | 0, 2 => (2 : Fin 10)
  | 0, 3 => (4 : Fin 10)
  | 0, 4 => (3 : Fin 10)
  | 0, 5 => (6 : Fin 10)
  | 0, 6 => (5 : Fin 10)
  | 0, 7 => (8 : Fin 10)
  | 0, 8 => (7 : Fin 10)
  | 0, 9 => (9 : Fin 10)
  | 1, 0 => (5 : Fin 10)
  | 1, 1 => (1 : Fin 10)
  | 1, 2 => (0 : Fin 10)
  | 1, 3 => (2 : Fin 10)
  | 1, 4 => (4 : Fin 10)
  | 1, 5 => (3 : Fin 10)
  | 1, 6 => (8 : Fin 10)
  | 1, 7 => (6 : Fin 10)
  | 1, 8 => (9 : Fin 10)
  | 1, 9 => (7 : Fin 10)
  | 2, 0 => (1 : Fin 10)
  | 2, 1 => (0 : Fin 10)
  | 2, 2 => (2 : Fin 10)
  | 2, 3 => (4 : Fin 10)
  | 2, 4 => (3 : Fin 10)
  | 2, 5 => (6 : Fin 10)
  | 2, 6 => (5 : Fin 10)
  | 2, 7 => (8 : Fin 10)
  | 2, 8 => (7 : Fin 10)
  | 2, 9 => (9 : Fin 10)
  | 3, 0 => (2 : Fin 10)
  | 3, 1 => (1 : Fin 10)
  | 3, 2 => (3 : Fin 10)
  | 3, 3 => (5 : Fin 10)
  | 3, 4 => (4 : Fin 10)
  | 3, 5 => (0 : Fin 10)
  | 3, 6 => (7 : Fin 10)
  | 3, 7 => (9 : Fin 10)
  | 3, 8 => (6 : Fin 10)
  | 3, 9 => (8 : Fin 10)
  | _, _ => (1 : Fin 10)

@[expose, reducible]
public def m11L1Factor : Fin 4 -> Fin 10 -> List (Fin 6)
  | 0, 0 => []
  | 0, 1 => []
  | 0, 2 => [(0 : Fin 6)]
  | 0, 3 => []
  | 0, 4 => []
  | 0, 5 => []
  | 0, 6 => []
  | 0, 7 => []
  | 0, 8 => []
  | 0, 9 => [(0 : Fin 6)]
  | 1, 0 => []
  | 1, 1 => [(2 : Fin 6), (0 : Fin 6)]
  | 1, 2 => []
  | 1, 3 => []
  | 1, 4 => [(5 : Fin 6), (4 : Fin 6)]
  | 1, 5 => []
  | 1, 6 => [(1 : Fin 6)]
  | 1, 7 => []
  | 1, 8 => [(4 : Fin 6)]
  | 1, 9 => []
  | 2, 0 => []
  | 2, 1 => []
  | 2, 2 => [(0 : Fin 6)]
  | 2, 3 => []
  | 2, 4 => []
  | 2, 5 => []
  | 2, 6 => []
  | 2, 7 => []
  | 2, 8 => []
  | 2, 9 => [(0 : Fin 6)]
  | 3, 0 => []
  | 3, 1 => [(0 : Fin 6), (5 : Fin 6)]
  | 3, 2 => []
  | 3, 3 => []
  | 3, 4 => [(1 : Fin 6), (2 : Fin 6)]
  | 3, 5 => []
  | 3, 6 => []
  | 3, 7 => []
  | 3, 8 => [(4 : Fin 6)]
  | 3, 9 => [(1 : Fin 6)]
  | _, _ => []

public theorem m11L1RepBase : m11L1Rep (0 : Fin 10) = 1 := by decide +kernel

public theorem m11L1RepPoint : (r : Fin 10) -> m11L1Rep r (2 : Fin 11) = m11L1Point r := by decide +kernel

@[expose, reducible]
public def m11L1PointInv : Fin 11 -> Fin 10
  | 0 => (3 : Fin 10)
  | 1 => (0 : Fin 10)
  | 2 => (0 : Fin 10)
  | 3 => (2 : Fin 10)
  | 4 => (4 : Fin 10)
  | 5 => (7 : Fin 10)
  | 6 => (9 : Fin 10)
  | 7 => (8 : Fin 10)
  | 8 => (6 : Fin 10)
  | 9 => (5 : Fin 10)
  | 10 => (1 : Fin 10)
  | _ => (3 : Fin 10)

public theorem m11L1PointInv_left : (r : Fin 10) -> m11L1PointInv (m11L1Point r) = r := by decide +kernel

public theorem m11L1Point_injective : Function.Injective m11L1Point := by
  intro x y h
  have hh := congrArg m11L1PointInv h
  simpa [m11L1PointInv_left] using hh

public theorem m11L1Step : (i : Fin 4) -> (r : Fin 10) -> m11L1Gen i * m11L1Rep r = m11L1Rep (m11L1Act i r) * evalWord m11L2Gen (m11L1Factor i r) := by decide +kernel

public theorem m11L1_card :
    Nat.card (wordSubgroup m11L1Gen m11L1Inv m11L1Inv_spec) =
      10 * Nat.card (wordSubgroup m11L2Gen m11L2Inv m11L2Inv_spec) :=
  wordSubgroup_card_eq_mul_next
    m11L1Gen m11L1Inv m11L1Inv_spec
    m11L2Gen m11L2Inv m11L2Inv_spec
    m11L1Rep m11L1Act m11L1Factor (2 : Fin 11) m11L1Point (0 : Fin 10)
    (fun r => by rw [m11L1Rep_eq_word r]; exact evalWord_mem_wordSubgroup m11L1Gen m11L1Inv m11L1Inv_spec (m11L1RepWord r))
    (wordSubgroup_le_of_gen_mem (fun i => by rw [m11L2Gen_eq_word i]; exact evalWord_mem_wordSubgroup m11L1Gen m11L1Inv m11L1Inv_spec (m11L2GenWord i)))
    m11L1RepBase m11L1RepPoint m11L1Point_injective
    (wordSubgroup_fix_of_gen_fix m11L2Gen m11L2Inv m11L2Inv_spec (by decide +kernel))
    m11L1Step

end M11OrderCertificate

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace M11OrderCertificate
@[expose, reducible]
public def m11L2R0To : Fin 11 -> Fin 11 := m11L0R0To

@[expose, reducible]
public def m11L2R0InvFun : Fin 11 -> Fin 11 := m11L0R0InvFun

public theorem m11L2R0_left : forall x, m11L2R0InvFun (m11L2R0To x) = x :=
  m11L0R0_left

public theorem m11L2R0_right : forall x, m11L2R0To (m11L2R0InvFun x) = x :=
  m11L0R0_right

@[expose, reducible]
public def m11L2R0 : Equiv.Perm (Fin 11) := m11L0R0

@[expose, reducible]
public def m11L2R1To : Fin 11 -> Fin 11
  | 0 => (6 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (4 : Fin 11)
  | 4 => (5 : Fin 11)
  | 5 => (3 : Fin 11)
  | 6 => (9 : Fin 11)
  | 7 => (10 : Fin 11)
  | 8 => (7 : Fin 11)
  | 9 => (0 : Fin 11)
  | 10 => (8 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L2R1InvFun : Fin 11 -> Fin 11
  | 0 => (9 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (5 : Fin 11)
  | 4 => (3 : Fin 11)
  | 5 => (4 : Fin 11)
  | 6 => (0 : Fin 11)
  | 7 => (8 : Fin 11)
  | 8 => (10 : Fin 11)
  | 9 => (6 : Fin 11)
  | 10 => (7 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L2R1_left : forall x, m11L2R1InvFun (m11L2R1To x) = x := by decide +kernel

public theorem m11L2R1_right : forall x, m11L2R1To (m11L2R1InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L2R1_left

@[expose, reducible]
public def m11L2R1 : Equiv.Perm (Fin 11) :=
  tablePerm m11L2R1To m11L2R1InvFun m11L2R1_left m11L2R1_right

@[expose, reducible]
public def m11L2R2To : Fin 11 -> Fin 11
  | 0 => (8 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (0 : Fin 11)
  | 4 => (6 : Fin 11)
  | 5 => (9 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (4 : Fin 11)
  | 8 => (3 : Fin 11)
  | 9 => (10 : Fin 11)
  | 10 => (5 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L2R2InvFun : Fin 11 -> Fin 11
  | 0 => (3 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (8 : Fin 11)
  | 4 => (7 : Fin 11)
  | 5 => (10 : Fin 11)
  | 6 => (4 : Fin 11)
  | 7 => (6 : Fin 11)
  | 8 => (0 : Fin 11)
  | 9 => (5 : Fin 11)
  | 10 => (9 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L2R2_left : forall x, m11L2R2InvFun (m11L2R2To x) = x := by decide +kernel

public theorem m11L2R2_right : forall x, m11L2R2To (m11L2R2InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L2R2_left

@[expose, reducible]
public def m11L2R2 : Equiv.Perm (Fin 11) :=
  tablePerm m11L2R2To m11L2R2InvFun m11L2R2_left m11L2R2_right

@[expose, reducible]
public def m11L2R3To : Fin 11 -> Fin 11 := m11L2R2InvFun

@[expose, reducible]
public def m11L2R3InvFun : Fin 11 -> Fin 11 := m11L2R2To

public theorem m11L2R3_left : forall x, m11L2R3InvFun (m11L2R3To x) = x :=
  m11L2R2_right

public theorem m11L2R3_right : forall x, m11L2R3To (m11L2R3InvFun x) = x :=
  m11L2R2_left

@[expose, reducible]
public def m11L2R3 : Equiv.Perm (Fin 11) :=
  tablePerm m11L2R3To m11L2R3InvFun m11L2R3_left m11L2R3_right

@[expose, reducible]
public def m11L2R4To : Fin 11 -> Fin 11
  | 0 => (4 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (7 : Fin 11)
  | 4 => (10 : Fin 11)
  | 5 => (8 : Fin 11)
  | 6 => (5 : Fin 11)
  | 7 => (9 : Fin 11)
  | 8 => (6 : Fin 11)
  | 9 => (3 : Fin 11)
  | 10 => (0 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L2R4InvFun : Fin 11 -> Fin 11
  | 0 => (10 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (9 : Fin 11)
  | 4 => (0 : Fin 11)
  | 5 => (6 : Fin 11)
  | 6 => (8 : Fin 11)
  | 7 => (3 : Fin 11)
  | 8 => (5 : Fin 11)
  | 9 => (7 : Fin 11)
  | 10 => (4 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L2R4_left : forall x, m11L2R4InvFun (m11L2R4To x) = x := by decide +kernel

public theorem m11L2R4_right : forall x, m11L2R4To (m11L2R4InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L2R4_left

@[expose, reducible]
public def m11L2R4 : Equiv.Perm (Fin 11) :=
  tablePerm m11L2R4To m11L2R4InvFun m11L2R4_left m11L2R4_right

@[expose, reducible]
public def m11L2R5To : Fin 11 -> Fin 11 := m11L2R4InvFun

@[expose, reducible]
public def m11L2R5InvFun : Fin 11 -> Fin 11 := m11L2R4To

public theorem m11L2R5_left : forall x, m11L2R5InvFun (m11L2R5To x) = x :=
  m11L2R4_right

public theorem m11L2R5_right : forall x, m11L2R5To (m11L2R5InvFun x) = x :=
  m11L2R4_left

@[expose, reducible]
public def m11L2R5 : Equiv.Perm (Fin 11) :=
  tablePerm m11L2R5To m11L2R5InvFun m11L2R5_left m11L2R5_right

@[expose, reducible]
public def m11L2R6To : Fin 11 -> Fin 11
  | 0 => (7 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (6 : Fin 11)
  | 4 => (9 : Fin 11)
  | 5 => (0 : Fin 11)
  | 6 => (10 : Fin 11)
  | 7 => (5 : Fin 11)
  | 8 => (4 : Fin 11)
  | 9 => (8 : Fin 11)
  | 10 => (3 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L2R6InvFun : Fin 11 -> Fin 11
  | 0 => (5 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (10 : Fin 11)
  | 4 => (8 : Fin 11)
  | 5 => (7 : Fin 11)
  | 6 => (3 : Fin 11)
  | 7 => (0 : Fin 11)
  | 8 => (9 : Fin 11)
  | 9 => (4 : Fin 11)
  | 10 => (6 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L2R6_left : forall x, m11L2R6InvFun (m11L2R6To x) = x := by decide +kernel

public theorem m11L2R6_right : forall x, m11L2R6To (m11L2R6InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L2R6_left

@[expose, reducible]
public def m11L2R6 : Equiv.Perm (Fin 11) :=
  tablePerm m11L2R6To m11L2R6InvFun m11L2R6_left m11L2R6_right

@[expose, reducible]
public def m11L2R7To : Fin 11 -> Fin 11 := m11L2R6InvFun

@[expose, reducible]
public def m11L2R7InvFun : Fin 11 -> Fin 11 := m11L2R6To

public theorem m11L2R7_left : forall x, m11L2R7InvFun (m11L2R7To x) = x :=
  m11L2R6_right

public theorem m11L2R7_right : forall x, m11L2R7To (m11L2R7InvFun x) = x :=
  m11L2R6_left

@[expose, reducible]
public def m11L2R7 : Equiv.Perm (Fin 11) :=
  tablePerm m11L2R7To m11L2R7InvFun m11L2R7_left m11L2R7_right

@[expose, reducible]
public def m11L2R8To : Fin 11 -> Fin 11 := m11L2R1InvFun

@[expose, reducible]
public def m11L2R8InvFun : Fin 11 -> Fin 11 := m11L2R1To

public theorem m11L2R8_left : forall x, m11L2R8InvFun (m11L2R8To x) = x :=
  m11L2R1_right

public theorem m11L2R8_right : forall x, m11L2R8To (m11L2R8InvFun x) = x :=
  m11L2R1_left

@[expose, reducible]
public def m11L2R8 : Equiv.Perm (Fin 11) :=
  tablePerm m11L2R8To m11L2R8InvFun m11L2R8_left m11L2R8_right

@[expose, reducible]
public def m11L2RepWord : Fin 9 -> List (Fin 6)
  | 0 => []
  | 1 => [(0 : Fin 6), (2 : Fin 6), (2 : Fin 6)]
  | 2 => [(0 : Fin 6), (1 : Fin 6), (0 : Fin 6), (4 : Fin 6)]
  | 3 => [(0 : Fin 6), (5 : Fin 6), (0 : Fin 6), (2 : Fin 6)]
  | 4 => [(4 : Fin 6), (0 : Fin 6), (4 : Fin 6)]
  | 5 => [(1 : Fin 6), (0 : Fin 6), (1 : Fin 6)]
  | 6 => [(1 : Fin 6), (1 : Fin 6), (0 : Fin 6)]
  | 7 => [(0 : Fin 6), (1 : Fin 6), (1 : Fin 6)]
  | 8 => [(2 : Fin 6), (2 : Fin 6), (0 : Fin 6)]
  | _ => []

@[expose, reducible]
public def m11L2Rep : Fin 9 -> Equiv.Perm (Fin 11)
  | 0 => m11L2R0
  | 1 => m11L2R1
  | 2 => m11L2R2
  | 3 => m11L2R3
  | 4 => m11L2R4
  | 5 => m11L2R5
  | 6 => m11L2R6
  | 7 => m11L2R7
  | 8 => m11L2R8
  | _ => m11L2R0

public theorem m11L2Rep_eq_word : (r : Fin 9) -> m11L2Rep r = evalWord m11L2Gen (m11L2RepWord r) := by decide +kernel

@[expose, reducible]
public def m11L2Point : Fin 9 -> Fin 11
  | 0 => (3 : Fin 11)
  | 1 => (4 : Fin 11)
  | 2 => (0 : Fin 11)
  | 3 => (8 : Fin 11)
  | 4 => (7 : Fin 11)
  | 5 => (9 : Fin 11)
  | 6 => (6 : Fin 11)
  | 7 => (10 : Fin 11)
  | 8 => (5 : Fin 11)
  | _ => (3 : Fin 11)

@[expose, reducible]
public def m11L2Act : Fin 6 -> Fin 9 -> Fin 9
  | 0, 0 => (1 : Fin 9)
  | 0, 1 => (0 : Fin 9)
  | 0, 2 => (4 : Fin 9)
  | 0, 3 => (6 : Fin 9)
  | 0, 4 => (2 : Fin 9)
  | 0, 5 => (7 : Fin 9)
  | 0, 6 => (3 : Fin 9)
  | 0, 7 => (5 : Fin 9)
  | 0, 8 => (8 : Fin 9)
  | 1, 0 => (8 : Fin 9)
  | 1, 1 => (7 : Fin 9)
  | 1, 2 => (0 : Fin 9)
  | 1, 3 => (1 : Fin 9)
  | 1, 4 => (4 : Fin 9)
  | 1, 5 => (2 : Fin 9)
  | 1, 6 => (3 : Fin 9)
  | 1, 7 => (6 : Fin 9)
  | 1, 8 => (5 : Fin 9)
  | 2, 0 => (0 : Fin 9)
  | 2, 1 => (7 : Fin 9)
  | 2, 2 => (5 : Fin 9)
  | 2, 3 => (4 : Fin 9)
  | 2, 4 => (2 : Fin 9)
  | 2, 5 => (3 : Fin 9)
  | 2, 6 => (1 : Fin 9)
  | 2, 7 => (8 : Fin 9)
  | 2, 8 => (6 : Fin 9)
  | 3, 0 => (1 : Fin 9)
  | 3, 1 => (0 : Fin 9)
  | 3, 2 => (4 : Fin 9)
  | 3, 3 => (6 : Fin 9)
  | 3, 4 => (2 : Fin 9)
  | 3, 5 => (7 : Fin 9)
  | 3, 6 => (3 : Fin 9)
  | 3, 7 => (5 : Fin 9)
  | 3, 8 => (8 : Fin 9)
  | 4, 0 => (2 : Fin 9)
  | 4, 1 => (3 : Fin 9)
  | 4, 2 => (5 : Fin 9)
  | 4, 3 => (6 : Fin 9)
  | 4, 4 => (4 : Fin 9)
  | 4, 5 => (8 : Fin 9)
  | 4, 6 => (7 : Fin 9)
  | 4, 7 => (1 : Fin 9)
  | 4, 8 => (0 : Fin 9)
  | 5, 0 => (0 : Fin 9)
  | 5, 1 => (6 : Fin 9)
  | 5, 2 => (4 : Fin 9)
  | 5, 3 => (5 : Fin 9)
  | 5, 4 => (3 : Fin 9)
  | 5, 5 => (2 : Fin 9)
  | 5, 6 => (8 : Fin 9)
  | 5, 7 => (1 : Fin 9)
  | 5, 8 => (7 : Fin 9)
  | _, _ => (1 : Fin 9)

@[expose, reducible]
public def m11L2Factor : Fin 6 -> Fin 9 -> List (Fin 6)
  | 0, _ => [(0 : Fin 6)]
  | 1, _ => [(1 : Fin 6)]
  | 2, _ => [(2 : Fin 6)]
  | 3, _ => [(0 : Fin 6)]
  | 4, _ => [(4 : Fin 6)]
  | 5, _ => [(5 : Fin 6)]
  | _, _ => [(0 : Fin 6)]

public theorem m11L2RepBase : m11L2Rep (0 : Fin 9) = 1 := by decide +kernel

public theorem m11L2RepPoint : (r : Fin 9) -> m11L2Rep r (3 : Fin 11) = m11L2Point r := by decide +kernel

@[expose, reducible]
public def m11L2PointInv : Fin 11 -> Fin 9
  | 0 => (2 : Fin 9)
  | 1 => (0 : Fin 9)
  | 2 => (0 : Fin 9)
  | 3 => (0 : Fin 9)
  | 4 => (1 : Fin 9)
  | 5 => (8 : Fin 9)
  | 6 => (6 : Fin 9)
  | 7 => (4 : Fin 9)
  | 8 => (3 : Fin 9)
  | 9 => (5 : Fin 9)
  | 10 => (7 : Fin 9)
  | _ => (2 : Fin 9)

public theorem m11L2PointInv_left : (r : Fin 9) -> m11L2PointInv (m11L2Point r) = r := by decide +kernel

public theorem m11L2Point_injective : Function.Injective m11L2Point := by
  intro x y h
  have hh := congrArg m11L2PointInv h
  simpa [m11L2PointInv_left] using hh

public theorem m11L2Step : (i : Fin 6) -> (r : Fin 9) -> m11L2Gen i * m11L2Rep r = m11L2Rep (m11L2Act i r) * evalWord m11L3Gen (m11L2Factor i r) := by decide +kernel

public theorem m11L2_card :
    Nat.card (wordSubgroup m11L2Gen m11L2Inv m11L2Inv_spec) =
      9 * Nat.card (wordSubgroup m11L3Gen m11L3Inv m11L3Inv_spec) :=
  wordSubgroup_card_eq_mul_next
    m11L2Gen m11L2Inv m11L2Inv_spec
    m11L3Gen m11L3Inv m11L3Inv_spec
    m11L2Rep m11L2Act m11L2Factor (3 : Fin 11) m11L2Point (0 : Fin 9)
    (fun r => by rw [m11L2Rep_eq_word r]; exact evalWord_mem_wordSubgroup m11L2Gen m11L2Inv m11L2Inv_spec (m11L2RepWord r))
    (wordSubgroup_le_of_gen_mem (fun i => by rw [m11L3Gen_eq_word i]; exact evalWord_mem_wordSubgroup m11L2Gen m11L2Inv m11L2Inv_spec (m11L3GenWord i)))
    m11L2RepBase m11L2RepPoint m11L2Point_injective
    (wordSubgroup_fix_of_gen_fix m11L3Gen m11L3Inv m11L3Inv_spec (by decide +kernel))
    m11L2Step

end M11OrderCertificate

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace M11OrderCertificate
@[expose, reducible]
public def m11L3R0To : Fin 11 -> Fin 11 := m11L0R0To

@[expose, reducible]
public def m11L3R0InvFun : Fin 11 -> Fin 11 := m11L0R0InvFun

public theorem m11L3R0_left : forall x, m11L3R0InvFun (m11L3R0To x) = x :=
  m11L0R0_left

public theorem m11L3R0_right : forall x, m11L3R0To (m11L3R0InvFun x) = x :=
  m11L0R0_right

@[expose, reducible]
public def m11L3R0 : Equiv.Perm (Fin 11) := m11L0R0

@[expose, reducible]
public def m11L3R1To : Fin 11 -> Fin 11
  | 0 => (8 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (5 : Fin 11)
  | 5 => (4 : Fin 11)
  | 6 => (10 : Fin 11)
  | 7 => (9 : Fin 11)
  | 8 => (0 : Fin 11)
  | 9 => (7 : Fin 11)
  | 10 => (6 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L3R1InvFun : Fin 11 -> Fin 11 := m11L3R1To

public theorem m11L3R1_left : forall x, m11L3R1InvFun (m11L3R1To x) = x := by decide +kernel

public theorem m11L3R1_right : forall x, m11L3R1To (m11L3R1InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L3R1_left

@[expose, reducible]
public def m11L3R1 : Equiv.Perm (Fin 11) :=
  tablePerm m11L3R1To m11L3R1InvFun m11L3R1_left m11L3R1_right

@[expose, reducible]
public def m11L3R2To : Fin 11 -> Fin 11
  | 0 => (5 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (0 : Fin 11)
  | 5 => (8 : Fin 11)
  | 6 => (9 : Fin 11)
  | 7 => (6 : Fin 11)
  | 8 => (4 : Fin 11)
  | 9 => (10 : Fin 11)
  | 10 => (7 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L3R2InvFun : Fin 11 -> Fin 11
  | 0 => (4 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (8 : Fin 11)
  | 5 => (0 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (10 : Fin 11)
  | 8 => (5 : Fin 11)
  | 9 => (6 : Fin 11)
  | 10 => (9 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L3R2_left : forall x, m11L3R2InvFun (m11L3R2To x) = x := by decide +kernel

public theorem m11L3R2_right : forall x, m11L3R2To (m11L3R2InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L3R2_left

@[expose, reducible]
public def m11L3R2 : Equiv.Perm (Fin 11) :=
  tablePerm m11L3R2To m11L3R2InvFun m11L3R2_left m11L3R2_right

@[expose, reducible]
public def m11L3R3To : Fin 11 -> Fin 11 := m11L3R2InvFun

@[expose, reducible]
public def m11L3R3InvFun : Fin 11 -> Fin 11 := m11L3R2To

public theorem m11L3R3_left : forall x, m11L3R3InvFun (m11L3R3To x) = x :=
  m11L3R2_right

public theorem m11L3R3_right : forall x, m11L3R3To (m11L3R3InvFun x) = x :=
  m11L3R2_left

@[expose, reducible]
public def m11L3R3 : Equiv.Perm (Fin 11) :=
  tablePerm m11L3R3To m11L3R3InvFun m11L3R3_left m11L3R3_right

@[expose, reducible]
public def m11L3R4To : Fin 11 -> Fin 11
  | 0 => (7 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (6 : Fin 11)
  | 5 => (10 : Fin 11)
  | 6 => (5 : Fin 11)
  | 7 => (8 : Fin 11)
  | 8 => (9 : Fin 11)
  | 9 => (0 : Fin 11)
  | 10 => (4 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L3R4InvFun : Fin 11 -> Fin 11
  | 0 => (9 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (10 : Fin 11)
  | 5 => (6 : Fin 11)
  | 6 => (4 : Fin 11)
  | 7 => (0 : Fin 11)
  | 8 => (7 : Fin 11)
  | 9 => (8 : Fin 11)
  | 10 => (5 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L3R4_left : forall x, m11L3R4InvFun (m11L3R4To x) = x := by decide +kernel

public theorem m11L3R4_right : forall x, m11L3R4To (m11L3R4InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L3R4_left

@[expose, reducible]
public def m11L3R4 : Equiv.Perm (Fin 11) :=
  tablePerm m11L3R4To m11L3R4InvFun m11L3R4_left m11L3R4_right

@[expose, reducible]
public def m11L3R5To : Fin 11 -> Fin 11 := m11L3R4InvFun

@[expose, reducible]
public def m11L3R5InvFun : Fin 11 -> Fin 11 := m11L3R4To

public theorem m11L3R5_left : forall x, m11L3R5InvFun (m11L3R5To x) = x :=
  m11L3R4_right

public theorem m11L3R5_right : forall x, m11L3R5To (m11L3R5InvFun x) = x :=
  m11L3R4_left

@[expose, reducible]
public def m11L3R5 : Equiv.Perm (Fin 11) :=
  tablePerm m11L3R5To m11L3R5InvFun m11L3R5_left m11L3R5_right

@[expose, reducible]
public def m11L3R6To : Fin 11 -> Fin 11
  | 0 => (10 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (7 : Fin 11)
  | 5 => (9 : Fin 11)
  | 6 => (0 : Fin 11)
  | 7 => (5 : Fin 11)
  | 8 => (6 : Fin 11)
  | 9 => (4 : Fin 11)
  | 10 => (8 : Fin 11)
  | _ => (1 : Fin 11)

@[expose, reducible]
public def m11L3R6InvFun : Fin 11 -> Fin 11
  | 0 => (6 : Fin 11)
  | 1 => (1 : Fin 11)
  | 2 => (2 : Fin 11)
  | 3 => (3 : Fin 11)
  | 4 => (9 : Fin 11)
  | 5 => (7 : Fin 11)
  | 6 => (8 : Fin 11)
  | 7 => (4 : Fin 11)
  | 8 => (10 : Fin 11)
  | 9 => (5 : Fin 11)
  | 10 => (0 : Fin 11)
  | _ => (1 : Fin 11)

public theorem m11L3R6_left : forall x, m11L3R6InvFun (m11L3R6To x) = x := by decide +kernel

public theorem m11L3R6_right : forall x, m11L3R6To (m11L3R6InvFun x) = x :=
  rightInverse_of_leftInverse_fin m11L3R6_left

@[expose, reducible]
public def m11L3R6 : Equiv.Perm (Fin 11) :=
  tablePerm m11L3R6To m11L3R6InvFun m11L3R6_left m11L3R6_right

@[expose, reducible]
public def m11L3R7To : Fin 11 -> Fin 11 := m11L3R6InvFun

@[expose, reducible]
public def m11L3R7InvFun : Fin 11 -> Fin 11 := m11L3R6To

public theorem m11L3R7_left : forall x, m11L3R7InvFun (m11L3R7To x) = x :=
  m11L3R6_right

public theorem m11L3R7_right : forall x, m11L3R7To (m11L3R7InvFun x) = x :=
  m11L3R6_left

@[expose, reducible]
public def m11L3R7 : Equiv.Perm (Fin 11) :=
  tablePerm m11L3R7To m11L3R7InvFun m11L3R7_left m11L3R7_right

@[expose, reducible]
public def m11L3RepWord : Fin 8 -> List (Fin 6)
  | 0 => []
  | 1 => [(0 : Fin 6)]
  | 2 => [(4 : Fin 6)]
  | 3 => [(1 : Fin 6)]
  | 4 => [(5 : Fin 6)]
  | 5 => [(2 : Fin 6)]
  | 6 => [(1 : Fin 6), (5 : Fin 6)]
  | 7 => [(1 : Fin 6), (2 : Fin 6)]
  | _ => []

@[expose, reducible]
public def m11L3Rep : Fin 8 -> Equiv.Perm (Fin 11)
  | 0 => m11L3R0
  | 1 => m11L3R1
  | 2 => m11L3R2
  | 3 => m11L3R3
  | 4 => m11L3R4
  | 5 => m11L3R5
  | 6 => m11L3R6
  | 7 => m11L3R7
  | _ => m11L3R0

public theorem m11L3Rep_eq_word : (r : Fin 8) -> m11L3Rep r = evalWord m11L3Gen (m11L3RepWord r) := by decide +kernel

@[expose, reducible]
public def m11L3Point : Fin 8 -> Fin 11
  | 0 => (4 : Fin 11)
  | 1 => (5 : Fin 11)
  | 2 => (0 : Fin 11)
  | 3 => (8 : Fin 11)
  | 4 => (6 : Fin 11)
  | 5 => (10 : Fin 11)
  | 6 => (7 : Fin 11)
  | 7 => (9 : Fin 11)
  | _ => (4 : Fin 11)

@[expose, reducible]
public def m11L3Act : Fin 6 -> Fin 8 -> Fin 8
  | 0, 0 => (1 : Fin 8)
  | 0, 1 => (0 : Fin 8)
  | 0, 2 => (3 : Fin 8)
  | 0, 3 => (2 : Fin 8)
  | 0, 4 => (5 : Fin 8)
  | 0, 5 => (4 : Fin 8)
  | 0, 6 => (7 : Fin 8)
  | 0, 7 => (6 : Fin 8)
  | 1, 0 => (3 : Fin 8)
  | 1, 1 => (2 : Fin 8)
  | 1, 2 => (0 : Fin 8)
  | 1, 3 => (1 : Fin 8)
  | 1, 4 => (6 : Fin 8)
  | 1, 5 => (7 : Fin 8)
  | 1, 6 => (5 : Fin 8)
  | 1, 7 => (4 : Fin 8)
  | 2, 0 => (5 : Fin 8)
  | 2, 1 => (4 : Fin 8)
  | 2, 2 => (7 : Fin 8)
  | 2, 3 => (6 : Fin 8)
  | 2, 4 => (0 : Fin 8)
  | 2, 5 => (1 : Fin 8)
  | 2, 6 => (2 : Fin 8)
  | 2, 7 => (3 : Fin 8)
  | 3, 0 => (1 : Fin 8)
  | 3, 1 => (0 : Fin 8)
  | 3, 2 => (3 : Fin 8)
  | 3, 3 => (2 : Fin 8)
  | 3, 4 => (5 : Fin 8)
  | 3, 5 => (4 : Fin 8)
  | 3, 6 => (7 : Fin 8)
  | 3, 7 => (6 : Fin 8)
  | 4, 0 => (2 : Fin 8)
  | 4, 1 => (3 : Fin 8)
  | 4, 2 => (1 : Fin 8)
  | 4, 3 => (0 : Fin 8)
  | 4, 4 => (7 : Fin 8)
  | 4, 5 => (6 : Fin 8)
  | 4, 6 => (4 : Fin 8)
  | 4, 7 => (5 : Fin 8)
  | 5, 0 => (4 : Fin 8)
  | 5, 1 => (5 : Fin 8)
  | 5, 2 => (6 : Fin 8)
  | 5, 3 => (7 : Fin 8)
  | 5, 4 => (1 : Fin 8)
  | 5, 5 => (0 : Fin 8)
  | 5, 6 => (3 : Fin 8)
  | 5, 7 => (2 : Fin 8)
  | _, _ => (1 : Fin 8)

@[expose, reducible]
public def m11L3Factor : Fin 6 -> Fin 8 -> List (Fin 0) :=
  fun _ _ => []

public theorem m11L3RepBase : m11L3Rep (0 : Fin 8) = 1 := by decide +kernel

public theorem m11L3RepPoint : (r : Fin 8) -> m11L3Rep r (4 : Fin 11) = m11L3Point r := by decide +kernel

@[expose, reducible]
public def m11L3PointInv : Fin 11 -> Fin 8
  | 0 => (2 : Fin 8)
  | 1 => (0 : Fin 8)
  | 2 => (0 : Fin 8)
  | 3 => (0 : Fin 8)
  | 4 => (0 : Fin 8)
  | 5 => (1 : Fin 8)
  | 6 => (4 : Fin 8)
  | 7 => (6 : Fin 8)
  | 8 => (3 : Fin 8)
  | 9 => (7 : Fin 8)
  | 10 => (5 : Fin 8)
  | _ => (2 : Fin 8)

public theorem m11L3PointInv_left : (r : Fin 8) -> m11L3PointInv (m11L3Point r) = r := by decide +kernel

public theorem m11L3Point_injective : Function.Injective m11L3Point := by
  intro x y h
  have hh := congrArg m11L3PointInv h
  simpa [m11L3PointInv_left] using hh

public theorem m11L3Step : (i : Fin 6) -> (r : Fin 8) -> m11L3Gen i * m11L3Rep r = m11L3Rep (m11L3Act i r) * evalWord m11L4Gen (m11L3Factor i r) := by decide +kernel

public theorem m11L3_card :
    Nat.card (wordSubgroup m11L3Gen m11L3Inv m11L3Inv_spec) =
      8 * Nat.card (wordSubgroup m11L4Gen m11L4Inv m11L4Inv_spec) :=
  wordSubgroup_card_eq_mul_next
    m11L3Gen m11L3Inv m11L3Inv_spec
    m11L4Gen m11L4Inv m11L4Inv_spec
    m11L3Rep m11L3Act m11L3Factor (4 : Fin 11) m11L3Point (0 : Fin 8)
    (fun r => by rw [m11L3Rep_eq_word r]; exact evalWord_mem_wordSubgroup m11L3Gen m11L3Inv m11L3Inv_spec (m11L3RepWord r))
    (wordSubgroup_le_of_gen_mem (fun i => Fin.elim0 i))
    m11L3RepBase m11L3RepPoint m11L3Point_injective
    (wordSubgroup_fix_of_gen_fix m11L4Gen m11L4Inv m11L4Inv_spec (fun i => Fin.elim0 i))
    m11L3Step

public theorem m11L4_card :
    Nat.card (wordSubgroup m11L4Gen m11L4Inv m11L4Inv_spec) = 1 :=
  wordSubgroup_fin_zero_card m11L4Gen m11L4Inv m11L4Inv_spec

public theorem m11Generated_order :
    Nat.card (wordSubgroup m11L0Gen m11L0Inv m11L0Inv_spec) = 7920 := by
  rw [m11L0_card, m11L1_card, m11L2_card, m11L3_card, m11L4_card]
end M11OrderCertificate

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace M11OrderRigidity

open scoped Pointwise
/-- There are exactly 7920 possible ordered images of four distinct points
inside the eleven-point action. -/
@[expose]
public def m11InitialFour : Finset (Fin 11) := {1, 2, 3, 4}
@[expose]
public def m11InitialBlock : Finset (Fin 11) := {1, 2, 3, 4, 5}

public theorem m11InitialBlock_mem : m11InitialBlock ∈ m11Blocks := by
  rw [m11Blocks]
  refine Finset.mem_image.mpr ⟨0, Finset.mem_univ _, ?_⟩
  decide +kernel

public theorem m11FixPointFive (g : Equiv.Perm (Fin 11))
    (hblocks : g • m11Blocks = m11Blocks)
    (h1 : g 1 = 1) (h2 : g 2 = 2) (h3 : g 3 = 3) (h4 : g 4 = 4) :
    g 5 = 5 := by
  have hImageMem : g • m11InitialBlock ∈ m11Blocks := by
    rw [← hblocks]
    exact Finset.smul_mem_smul_finset (a := g) m11InitialBlock_mem
  have hSub : m11InitialFour ⊆ g • m11InitialBlock := by
    intro x hx
    simp only [m11InitialFour, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa [h1] using Finset.smul_mem_smul_finset (a := g)
        (show (1 : Fin 11) ∈ m11InitialBlock by decide +kernel)
    · simpa [h2] using Finset.smul_mem_smul_finset (a := g)
        (show (2 : Fin 11) ∈ m11InitialBlock by decide +kernel)
    · simpa [h3] using Finset.smul_mem_smul_finset (a := g)
        (show (3 : Fin 11) ∈ m11InitialBlock by decide +kernel)
    · simpa [h4] using Finset.smul_mem_smul_finset (a := g)
        (show (4 : Fin 11) ∈ m11InitialBlock by decide +kernel)
  have hInitialMem : m11InitialBlock ∈
      m11Blocks.filter (fun B => m11InitialFour ⊆ B) := by
    exact Finset.mem_filter.mpr ⟨m11InitialBlock_mem, by decide +kernel⟩
  have hImageFilter : g • m11InitialBlock ∈
      m11Blocks.filter (fun B => m11InitialFour ⊆ B) := by
    exact Finset.mem_filter.mpr ⟨hImageMem, hSub⟩
  have hCard : (m11Blocks.filter (fun B => m11InitialFour ⊆ B)).card = 1 := by
    apply m11Blocks_unique_block
    decide +kernel
  rcases Finset.card_eq_one.mp hCard with ⟨B, hB⟩
  have hInitialEq : m11InitialBlock = B := by
    have : m11InitialBlock ∈ ({B} : Finset (Finset (Fin 11))) := by
      rwa [← hB]
    simpa using this
  have hImageEqB : g • m11InitialBlock = B := by
    have : g • m11InitialBlock ∈ ({B} : Finset (Finset (Fin 11))) := by
      rwa [← hB]
    simpa using this
  have hImageEq : g • m11InitialBlock = m11InitialBlock :=
    hImageEqB.trans hInitialEq.symm
  have h5mem : g 5 ∈ m11InitialBlock := by
    rw [← hImageEq]
    exact Finset.smul_mem_smul_finset (a := g) (by decide +kernel)
  have hne1 : g 5 ≠ 1 := by
    intro h
    exact (by decide +kernel : (5 : Fin 11) ≠ 1) (g.injective (h.trans h1.symm))
  have hne2 : g 5 ≠ 2 := by
    intro h
    exact (by decide +kernel : (5 : Fin 11) ≠ 2) (g.injective (h.trans h2.symm))
  have hne3 : g 5 ≠ 3 := by
    intro h
    exact (by decide +kernel : (5 : Fin 11) ≠ 3) (g.injective (h.trans h3.symm))
  have hne4 : g 5 ≠ 4 := by
    intro h
    exact (by decide +kernel : (5 : Fin 11) ≠ 4) (g.injective (h.trans h4.symm))
  simpa [m11InitialBlock, hne1, hne2, hne3, hne4] using h5mem

@[expose]
public def m11ShiftTo : Fin 11 → Fin 11
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6
  | 6 => 7 | 7 => 8 | 8 => 9 | 9 => 10 | 10 => 0 | _ => 0

@[expose]
public def m11ShiftInv : Fin 11 → Fin 11
  | 0 => 10 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4
  | 6 => 5 | 7 => 6 | 8 => 7 | 9 => 8 | 10 => 9 | _ => 0

public theorem m11Shift_left : (x : Fin 11) → m11ShiftInv (m11ShiftTo x) = x
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl
  | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl | 10 => rfl

public theorem m11Shift_right : (x : Fin 11) → m11ShiftTo (m11ShiftInv x) = x
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl
  | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl | 10 => rfl

@[expose]
public def m11Shift : Equiv.Perm (Fin 11) where
  toFun := m11ShiftTo
  invFun := m11ShiftInv
  left_inv := m11Shift_left
  right_inv := m11Shift_right

@[expose]
public def m11SplitFive : Fin 5 ⊕ Fin 6 ≃ Fin 11 :=
  (finSumFinEquiv : Fin 5 ⊕ Fin 6 ≃ Fin 11).trans m11Shift

@[expose]
public def m11ConjugateFive (g : Equiv.Perm (Fin 11)) :
    Equiv.Perm (Fin 5 ⊕ Fin 6) :=
  m11SplitFive.symm.permCongr g

public theorem perm_eq_sumCongr_one_of_fix_inl
    {m n : Type*} [Finite m] [Finite n]
    (q : Equiv.Perm (m ⊕ n))
    (hfix : ∀ i : m, q (Sum.inl i) = Sum.inl i) :
    ∃ p : Equiv.Perm n, q = Equiv.sumCongr 1 p := by
  have hmap : Set.MapsTo q (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i, (hfix i).symm⟩
  rcases MonoidHom.mem_range.mp
      (Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmap) with
    ⟨⟨p₁, p₂⟩, hp⟩
  have hp₁ : p₁ = 1 := by
    ext i
    have hi := Equiv.congr_fun hp (Sum.inl i)
    simpa [hfix i] using hi
  refine ⟨p₂, ?_⟩
  simpa [Equiv.Perm.sumCongrHom_apply, hp₁] using hp.symm

public theorem m11SplitFive_inl (i : Fin 5) :
    m11SplitFive (Sum.inl i) = m11Shift (Fin.castAdd 6 i) := by
  change m11Shift ((finSumFinEquiv : Fin 5 ⊕ Fin 6 ≃ Fin 11) (Sum.inl i)) = m11Shift (Fin.castAdd 6 i)
  exact congrArg m11Shift (finSumFinEquiv_apply_left (n := 6) i)

@[expose]
public def m11RemainingEmbedding : Fin 6 ↪ Fin 11 where
  toFun
    | 0 => 6
    | 1 => 7
    | 2 => 8
    | 3 => 9
    | 4 => 10
    | 5 => 0
  inj' := by decide +kernel

public theorem m11SplitFive_inr (j : Fin 6) :
    m11SplitFive (Sum.inr j) = m11RemainingEmbedding j := by
  change m11Shift ((finSumFinEquiv : Fin 5 ⊕ Fin 6 ≃ Fin 11) (Sum.inr j)) =
    m11RemainingEmbedding j
  rw [finSumFinEquiv_apply_right]
  fin_cases j <;> rfl
public theorem m11RestrictToSix (g : Equiv.Perm (Fin 11))
    (h1 : g 1 = 1) (h2 : g 2 = 2) (h3 : g 3 = 3)
    (h4 : g 4 = 4) (h5 : g 5 = 5) :
    ∃ p : Equiv.Perm (Fin 6),
      m11ConjugateFive g = Equiv.sumCongr 1 p := by
  apply perm_eq_sumCongr_one_of_fix_inl
  intro i
  calc
    m11SplitFive.symm (g (m11SplitFive (Sum.inl i))) =
        m11SplitFive.symm (m11SplitFive (Sum.inl i)) := by
          congr 1
          rw [m11SplitFive_inl i]; fin_cases i <;> simp [m11Shift, m11ShiftTo, h1, h2, h3, h4, h5]
    _ = Sum.inl i := m11SplitFive.symm_apply_apply _

public theorem m11Remaining_action {g : Equiv.Perm (Fin 11)}
    {p : Equiv.Perm (Fin 6)}
    (hgp : m11ConjugateFive g = Equiv.sumCongr 1 p) (j : Fin 6) :
    g (m11RemainingEmbedding j) = m11RemainingEmbedding (p j) := by
  calc
    g (m11RemainingEmbedding j) = g (m11SplitFive (Sum.inr j)) :=
      congrArg g (m11SplitFive_inr j).symm
    _ = m11SplitFive (Sum.inr (p j)) := by
      have hj := congrArg m11SplitFive (Equiv.congr_fun hgp (Sum.inr j))
      simpa [m11ConjugateFive, Equiv.permCongr_apply] using hj
    _ = m11RemainingEmbedding (p j) := m11SplitFive_inr (p j)

public theorem m11_eq_one_of_restriction_eq_one {g : Equiv.Perm (Fin 11)}
    {p : Equiv.Perm (Fin 6)}
    (hgp : m11ConjugateFive g = Equiv.sumCongr 1 p) (hp : p = 1) :
    g = 1 := by
  subst p
  have hq : m11ConjugateFive g = 1 := by simpa using hgp
  apply Equiv.ext
  intro x
  have hx := congrArg m11SplitFive
    (Equiv.congr_fun hq (m11SplitFive.symm x))
  simpa [m11ConjugateFive, Equiv.permCongr_apply] using hx
@[expose]
public def m11Matching123 : Finset (Finset (Fin 6)) :=
  {{0, 4}, {1, 3}, {2, 5}}
@[expose]
public def m11Matching124 : Finset (Finset (Fin 6)) :=
  {{0, 1}, {2, 3}, {4, 5}}
@[expose]
public def m11Matching134 : Finset (Finset (Fin 6)) :=
  {{0, 5}, {1, 2}, {3, 4}}
@[expose]
public def m11Matching234 : Finset (Finset (Fin 6)) :=
  {{0, 3}, {1, 5}, {2, 4}}

@[expose]
public def m11LiftBlock (T : Finset (Fin 11)) (P : Finset (Fin 6)) :
    Finset (Fin 11) := T ∪ P.map m11RemainingEmbedding

@[expose]
public def m11Triple123 : Finset (Fin 11) := {1, 2, 3}
@[expose]
public def m11Triple124 : Finset (Fin 11) := {1, 2, 4}
@[expose]
public def m11Triple134 : Finset (Fin 11) := {1, 3, 4}
@[expose]
public def m11Triple234 : Finset (Fin 11) := {2, 3, 4}

public theorem m11Matching123_mem_iff (P : Finset (Fin 6)) :
    P ∈ m11Matching123 ↔ m11LiftBlock m11Triple123 P ∈ m11Blocks := by
  revert P
  decide +kernel

public theorem m11Matching124_mem_iff (P : Finset (Fin 6)) :
    P ∈ m11Matching124 ↔ m11LiftBlock m11Triple124 P ∈ m11Blocks := by
  revert P
  decide +kernel

public theorem m11Matching134_mem_iff (P : Finset (Fin 6)) :
    P ∈ m11Matching134 ↔ m11LiftBlock m11Triple134 P ∈ m11Blocks := by
  revert P
  decide +kernel

public theorem m11Matching234_mem_iff (P : Finset (Fin 6)) :
    P ∈ m11Matching234 ↔ m11LiftBlock m11Triple234 P ∈ m11Blocks := by
  revert P
  decide +kernel
public theorem m11LiftBlock_smul {g : Equiv.Perm (Fin 11)}
    {p : Equiv.Perm (Fin 6)}
    (hgp : m11ConjugateFive g = Equiv.sumCongr 1 p)
    (T : Finset (Fin 11)) (hT : ∀ x ∈ T, g x = x)
    (P : Finset (Fin 6)) :
    g • m11LiftBlock T P = m11LiftBlock T (p • P) := by
  classical
  have hTset : g • T = T := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_smul_finset.mp hx with ⟨y, hy, hxy⟩
      change g y = x at hxy
      rw [hT y hy] at hxy
      subst x
      exact hy
    · simp
  have hPset : g • P.map m11RemainingEmbedding =
      (p • P).map m11RemainingEmbedding := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_smul_finset.mp hx with ⟨y, hy, hxy⟩
      rcases Finset.mem_map.mp hy with ⟨j, hj, rfl⟩
      apply Finset.mem_map.mpr
      refine ⟨p j, Finset.smul_mem_smul_finset (a := p) hj, ?_⟩
      calc
        m11RemainingEmbedding (p j) = g (m11RemainingEmbedding j) :=
          (m11Remaining_action hgp j).symm
        _ = x := by simpa [Equiv.Perm.smul_def] using hxy
    · simp
  rw [m11LiftBlock, Finset.smul_finset_union, hTset, hPset]
  rfl

public theorem m11Matching_preserved {g : Equiv.Perm (Fin 11)}
    {p : Equiv.Perm (Fin 6)}
    (hgp : m11ConjugateFive g = Equiv.sumCongr 1 p)
    (hblocks : g • m11Blocks = m11Blocks)
    (T : Finset (Fin 11)) (hT : ∀ x ∈ T, g x = x)
    (M : Finset (Finset (Fin 6)))
    (hM : ∀ P, P ∈ M ↔ m11LiftBlock T P ∈ m11Blocks) :
    p • M = M := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro P hP
    rcases Finset.mem_smul_finset.mp hP with ⟨Q, hQ, rfl⟩
    apply (hM _).mpr
    have hBlock : m11LiftBlock T Q ∈ m11Blocks := (hM Q).mp hQ
    have hImage := Finset.smul_mem_smul_finset (a := g) hBlock
    rw [hblocks] at hImage
    rwa [m11LiftBlock_smul hgp T hT Q] at hImage
  · simp

public theorem m11ComplementRigidity (g : Equiv.Perm (Fin 6))
    (h123 : g • m11Matching123 = m11Matching123)
    (h124 : g • m11Matching124 = m11Matching124)
    (h134 : g • m11Matching134 = m11Matching134)
    (h234 : g • m11Matching234 = m11Matching234) :
    g = 1 := by
  revert g
  decide +kernel

public theorem m11FourPointRigidity (g : Equiv.Perm (Fin 11))
    (hblocks : g • m11Blocks = m11Blocks)
    (h1 : g 1 = 1) (h2 : g 2 = 2) (h3 : g 3 = 3) (h4 : g 4 = 4) :
    g = 1 := by
  have h5 := m11FixPointFive g hblocks h1 h2 h3 h4
  rcases m11RestrictToSix g h1 h2 h3 h4 h5 with ⟨p, hgp⟩
  have hfix123 : ∀ x ∈ m11Triple123, g x = x := by
    intro x hx
    simp only [m11Triple123, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hfix124 : ∀ x ∈ m11Triple124, g x = x := by
    intro x hx
    simp only [m11Triple124, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h4
  have hfix134 : ∀ x ∈ m11Triple134, g x = x := by
    intro x hx
    simp only [m11Triple134, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1
    · exact h3
    · exact h4
  have hfix234 : ∀ x ∈ m11Triple234, g x = x := by
    intro x hx
    simp only [m11Triple234, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h2
    · exact h3
    · exact h4
  have hp := m11ComplementRigidity p
    (m11Matching_preserved hgp hblocks m11Triple123 hfix123
      m11Matching123 m11Matching123_mem_iff)
    (m11Matching_preserved hgp hblocks m11Triple124 hfix124
      m11Matching124 m11Matching124_mem_iff)
    (m11Matching_preserved hgp hblocks m11Triple134 hfix134
      m11Matching134 m11Matching134_mem_iff)
    (m11Matching_preserved hgp hblocks m11Triple234 hfix234
      m11Matching234 m11Matching234_mem_iff)
  exact m11_eq_one_of_restriction_eq_one hgp hp
public theorem m11_fourPointImages_card :
    Fintype.card (Fin 4 ↪ Fin 11) = 7920 := by
  rw [Fintype.card_embedding_eq]
  norm_num [Nat.descFactorial]

@[expose]
public def m11FourPointImage (g : M11) : Fin 4 ↪ Fin 11 where
  toFun i := (g : Equiv.Perm (Fin 11)) (m11Shift (Fin.castAddEmb 7 i))
  inj' := by
    intro i j hij
    apply (Fin.castAddEmb 7).injective
    apply m11Shift.injective
    exact (g : Equiv.Perm (Fin 11)).injective hij

public theorem m11Mem_blocks (g : M11) :
    (g : Equiv.Perm (Fin 11)) • m11Blocks = m11Blocks := by
  apply Finset.coe_injective
  have hg : (g : Equiv.Perm (Fin 11)) ∈ m11WittDesign.aut := by
    simpa only [M11] using g.property
  rw [SteinerSystem.mem_aut_iff] at hg
  rw [m11WittDesign_blocks] at hg
  simpa only [Finset.coe_smul_finset] using hg

public theorem m11FourPointImage_injective : Function.Injective m11FourPointImage := by
  intro g h hgh
  let q : M11 := g⁻¹ * h
  have hAt (i : Fin 4) :
      (g : Equiv.Perm (Fin 11)) (m11Shift (Fin.castAddEmb 7 i)) =
        (h : Equiv.Perm (Fin 11)) (m11Shift (Fin.castAddEmb 7 i)) := by
    exact congrArg (fun e : Fin 4 ↪ Fin 11 => e i) hgh
  have hfix1 : (q : Equiv.Perm (Fin 11)) 1 = 1 := by
    have hi := hAt 0
    change (g : Equiv.Perm (Fin 11)) 1 = (h : Equiv.Perm (Fin 11)) 1 at hi
    change ((g : Equiv.Perm (Fin 11))⁻¹ * (h : Equiv.Perm (Fin 11))) 1 = 1
    rw [Equiv.Perm.mul_apply, ← hi]
    simp
  have hfix2 : (q : Equiv.Perm (Fin 11)) 2 = 2 := by
    have hi := hAt 1
    change (g : Equiv.Perm (Fin 11)) 2 = (h : Equiv.Perm (Fin 11)) 2 at hi
    change ((g : Equiv.Perm (Fin 11))⁻¹ * (h : Equiv.Perm (Fin 11))) 2 = 2
    rw [Equiv.Perm.mul_apply, ← hi]
    simp
  have hfix3 : (q : Equiv.Perm (Fin 11)) 3 = 3 := by
    have hi := hAt 2
    change (g : Equiv.Perm (Fin 11)) 3 = (h : Equiv.Perm (Fin 11)) 3 at hi
    change ((g : Equiv.Perm (Fin 11))⁻¹ * (h : Equiv.Perm (Fin 11))) 3 = 3
    rw [Equiv.Perm.mul_apply, ← hi]
    simp
  have hfix4 : (q : Equiv.Perm (Fin 11)) 4 = 4 := by
    have hi := hAt 3
    change (g : Equiv.Perm (Fin 11)) 4 = (h : Equiv.Perm (Fin 11)) 4 at hi
    change ((g : Equiv.Perm (Fin 11))⁻¹ * (h : Equiv.Perm (Fin 11))) 4 = 4
    rw [Equiv.Perm.mul_apply, ← hi]
    simp
  have hq : (q : Equiv.Perm (Fin 11)) = 1 :=
    m11FourPointRigidity q (m11Mem_blocks q) hfix1 hfix2 hfix3 hfix4
  apply Subtype.ext
  have hmul := congrArg (fun k : Equiv.Perm (Fin 11) =>
    (g : Equiv.Perm (Fin 11)) * k) hq
  simpa [q, mul_assoc] using hmul.symm

public theorem m11_card_le : Nat.card M11 ≤ 7920 := by
  calc
    Nat.card M11 ≤ Nat.card (Fin 4 ↪ Fin 11) :=
      Nat.card_le_card_of_injective m11FourPointImage m11FourPointImage_injective
    _ = Fintype.card (Fin 4 ↪ Fin 11) := Nat.card_eq_fintype_card
    _ = 7920 := m11_fourPointImages_card
end M11OrderRigidity

end Sporadic.Mathieu
