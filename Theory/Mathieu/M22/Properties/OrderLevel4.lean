module

public import Theory.Mathieu.M22.Properties.OrderCertificate
import Mathlib.Tactic.FinCases

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise
@[reducible]
private def m22L4R0To : Fin 22 -> Fin 22
  | 0 => (0 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (6 : Fin 22)
  | 7 => (7 : Fin 22)
  | 8 => (8 : Fin 22)
  | 9 => (9 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (13 : Fin 22)
  | 14 => (14 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (16 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (21 : Fin 22)
  | _ => (1 : Fin 22)

@[reducible]
private def m22L4R0InvFun : Fin 22 -> Fin 22
  | 0 => (0 : Fin 22)
  | 1 => (1 : Fin 22)
  | 2 => (2 : Fin 22)
  | 3 => (3 : Fin 22)
  | 4 => (4 : Fin 22)
  | 5 => (5 : Fin 22)
  | 6 => (6 : Fin 22)
  | 7 => (7 : Fin 22)
  | 8 => (8 : Fin 22)
  | 9 => (9 : Fin 22)
  | 10 => (10 : Fin 22)
  | 11 => (11 : Fin 22)
  | 12 => (12 : Fin 22)
  | 13 => (13 : Fin 22)
  | 14 => (14 : Fin 22)
  | 15 => (15 : Fin 22)
  | 16 => (16 : Fin 22)
  | 17 => (17 : Fin 22)
  | 18 => (18 : Fin 22)
  | 19 => (19 : Fin 22)
  | 20 => (20 : Fin 22)
  | 21 => (21 : Fin 22)
  | _ => (1 : Fin 22)

private theorem m22L4R0_left : forall x, m22L4R0InvFun (m22L4R0To x) = x := by
  intro x
  fin_cases x <;> rfl

private theorem m22L4R0_right : forall x, m22L4R0To (m22L4R0InvFun x) = x := by
  intro x
  fin_cases x <;> rfl

@[reducible]
private def m22L4R0 : Equiv.Perm (Fin 22) :=
  tablePerm m22L4R0To m22L4R0InvFun m22L4R0_left m22L4R0_right

@[reducible]
private def m22L4R1To : Fin 22 -> Fin 22
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

@[reducible]
private def m22L4R1InvFun : Fin 22 -> Fin 22
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

private theorem m22L4R1_left : forall x, m22L4R1InvFun (m22L4R1To x) = x := by
  intro x
  fin_cases x <;> rfl

private theorem m22L4R1_right : forall x, m22L4R1To (m22L4R1InvFun x) = x := by
  intro x
  fin_cases x <;> rfl

@[reducible]
private def m22L4R1 : Equiv.Perm (Fin 22) :=
  tablePerm m22L4R1To m22L4R1InvFun m22L4R1_left m22L4R1_right

@[reducible]
private def m22L4R2To : Fin 22 -> Fin 22
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

@[reducible]
private def m22L4R2InvFun : Fin 22 -> Fin 22
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

private theorem m22L4R2_left : forall x, m22L4R2InvFun (m22L4R2To x) = x := by
  intro x
  fin_cases x <;> rfl

private theorem m22L4R2_right : forall x, m22L4R2To (m22L4R2InvFun x) = x := by
  intro x
  fin_cases x <;> rfl

@[reducible]
private def m22L4R2 : Equiv.Perm (Fin 22) :=
  tablePerm m22L4R2To m22L4R2InvFun m22L4R2_left m22L4R2_right

@[reducible]
private def m22L4RepWord : Fin 3 -> List (Fin 2)
  | 0 => []
  | 1 => [(1 : Fin 2)]
  | 2 => [(0 : Fin 2)]
  | _ => []

@[reducible]
private def m22L4Rep : Fin 3 -> Equiv.Perm (Fin 22)
  | 0 => m22L4R0
  | 1 => m22L4R1
  | 2 => m22L4R2
  | _ => m22L4R0

private theorem m22L4Rep_eq_word : (r : Fin 3) -> m22L4Rep r = evalWord m22L4Gen (m22L4RepWord r) := by
  intro r
  revert r
  decide +kernel

@[reducible]
private def m22L4Point : Fin 3 -> Fin 22
  | 0 => (5 : Fin 22)
  | 1 => (16 : Fin 22)
  | 2 => (17 : Fin 22)
  | _ => (5 : Fin 22)

@[reducible]
private def m22L4Act : Fin 2 -> Fin 3 -> Fin 3
  | 0, 0 => (2 : Fin 3)
  | 0, 1 => (0 : Fin 3)
  | 0, 2 => (1 : Fin 3)
  | 1, 0 => (1 : Fin 3)
  | 1, 1 => (2 : Fin 3)
  | 1, 2 => (0 : Fin 3)
  | _, _ => (2 : Fin 3)

@[reducible]
private def m22L4Factor : Fin 2 -> Fin 3 -> List (Fin 0)
  | 0, 0 => []
  | 0, 1 => []
  | 0, 2 => []
  | 1, 0 => []
  | 1, 1 => []
  | 1, 2 => []
  | _, _ => []

private theorem m22L4RepBase : m22L4Rep (0 : Fin 3) = 1 := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

private theorem m22L4RepPoint : (r : Fin 3) -> m22L4Rep r (5 : Fin 22) = m22L4Point r := by
  intro r
  fin_cases r <;> rfl

@[reducible]
private def m22L4PointInv : Fin 22 -> Fin 3
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (0 : Fin 3)
  | 6 => (0 : Fin 3)
  | 7 => (0 : Fin 3)
  | 8 => (0 : Fin 3)
  | 9 => (0 : Fin 3)
  | 10 => (0 : Fin 3)
  | 11 => (0 : Fin 3)
  | 12 => (0 : Fin 3)
  | 13 => (0 : Fin 3)
  | 14 => (0 : Fin 3)
  | 15 => (0 : Fin 3)
  | 16 => (1 : Fin 3)
  | 17 => (2 : Fin 3)
  | 18 => (0 : Fin 3)
  | 19 => (0 : Fin 3)
  | 20 => (0 : Fin 3)
  | 21 => (0 : Fin 3)
  | _ => (0 : Fin 3)

private theorem m22L4PointInv_left : (r : Fin 3) -> m22L4PointInv (m22L4Point r) = r := by
  intro r
  fin_cases r <;> rfl

private theorem m22L4Point_injective : Function.Injective m22L4Point := by
  intro x y h
  have hh := congrArg m22L4PointInv h
  simpa [m22L4PointInv_left] using hh

private theorem m22L4Step : (i : Fin 2) -> (r : Fin 3) -> m22L4Gen i * m22L4Rep r = m22L4Rep (m22L4Act i r) * evalWord m22L5Gen (m22L4Factor i r) := by
  intro i r
  fin_cases i <;> fin_cases r <;> apply Equiv.ext <;> intro x <;> fin_cases x <;> rfl

public theorem m22L4_card :
    Nat.card (wordSubgroup m22L4Gen m22L4Inv m22L4Inv_spec) =
      3 * Nat.card (wordSubgroup m22L5Gen m22L5Inv m22L5Inv_spec) :=
  wordSubgroup_card_eq_mul_next
    m22L4Gen m22L4Inv m22L4Inv_spec
    m22L5Gen m22L5Inv m22L5Inv_spec
    m22L4Rep m22L4Act m22L4Factor (5 : Fin 22) m22L4Point (0 : Fin 3)
    (fun r => by rw [m22L4Rep_eq_word r]; exact evalWord_mem_wordSubgroup m22L4Gen m22L4Inv m22L4Inv_spec (m22L4RepWord r))
    (wordSubgroup_le_of_gen_mem (fun i => Fin.elim0 i))
    m22L4RepBase m22L4RepPoint m22L4Point_injective
    (wordSubgroup_fix_of_gen_fix m22L5Gen m22L5Inv m22L5Inv_spec (fun i => Fin.elim0 i))
    m22L4Step

public theorem m22L5_card :
    Nat.card (wordSubgroup m22L5Gen m22L5Inv m22L5Inv_spec) = 1 :=
  wordSubgroup_fin_zero_card m22L5Gen m22L5Inv m22L5Inv_spec

end Sporadic.Mathieu
