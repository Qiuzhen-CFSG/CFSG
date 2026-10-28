module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.Defs
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Legacy conditional interfaces for Chapter 6

These declarations are retained for compatibility. `Hypothesis61` omits
essential assumptions of source Hypothesis 6.1.1: QTKE, membership in
`L_f^*(G,T)` and `R₂(LT)`, the A₅-module exclusion, and the condition on
`n(H)`. `IsRankTwoTwoSubgroup` is not the source's `R₂` condition.
`IsNaturalL2Layer` does not identify the ambient conjugation action on `V`.
Use the separate `SourceDefs` interface for source statements.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.663.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter6

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Legacy elementary-abelian, containment and normalization predicate.
It asserts neither rank two nor membership in the source family `R₂(LT)`. -/
def IsRankTwoTwoSubgroup (V L T : Subgroup G) : Prop :=
  IsElementaryAbelian 2 V ∧ V ≤ L ⊔ T ∧ T ≤ normalizer (V : Set G)

/-- Legacy block-model predicate with an abstract group isomorphism to `V`.
The displayed isomorphism is not required to respect ambient conjugation;
this is not the natural-module conclusion of 6.1.6 or 6.1.27. -/
def IsNaturalL2Layer (L V : Subgroup G) (n : ℕ) : Prop :=
  ChapterC.IsL2EvenBlock (↥L) n ∧
    Nonempty (ChapterC.BlockModule (↥L) ≃* ↥V)

/-- Legacy local hypotheses, insufficient for source Hypothesis 6.1.1.
See the module documentation for the missing assumptions. -/
public structure Hypothesis61 where
  T : Sylow 2 G
  L : Subgroup G
  M : Subgroup G
  V : Subgroup G
  n : ℕ
  simple : IsSimpleGroup G
  nonabelian : ¬ IsMulCommutative G
  maximal_two_local : IsMaximalTwoLocal M
  T_le_M : (T : Subgroup G) ≤ M
  L_le_M : L ≤ M
  L_normal_in_M : (L.subgroupOf M).Normal
  quotient_model : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)
  n_gt_one : 1 < n
  isRankTwo : IsRankTwoTwoSubgroup V L (T : Subgroup G)
  commutator_nontrivial : ⁅V, L⁆ ≠ ⊥

namespace Hypothesis61

variable (h : Hypothesis61 (G := G))

omit [Finite G] in
public theorem V_le_LT : h.V ≤ h.L ⊔ (h.T : Subgroup G) := h.isRankTwo.2.1

omit [Finite G] in
public theorem T_normalizes_V : (h.T : Subgroup G) ≤ normalizer (h.V : Set G) :=
  h.isRankTwo.2.2

omit [Finite G] in
public theorem VL_nontrivial : ⁅h.V, h.L⁆ ≠ ⊥ := h.commutator_nontrivial

end Hypothesis61

end CFSG.Quasithin.Chapter6

end
