/-
Authors: OpenAI, Yusen Tang
-/

module

public import Submission.FeitThompson.BGsection6.Defs

open scoped MatrixGroups Pointwise TensorProduct

/-! # Theorem 6.1 from BG Section 6 -/

public theorem theorem_6_1
    {G : Type*} [Group G] [IsSolvable G] (ho : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (A : Subgroup S) [A.Normal] [IsMulCommutative A] :
    A.map S.toSubgroup.subtype ≤ Op_p'p p G := by
  letI : Finite G := card_odd_finite ho
  exact sylow_abelian_normal_le_op_pPrime_p
    (G := G) (hsolv := inferInstance) ho S A
