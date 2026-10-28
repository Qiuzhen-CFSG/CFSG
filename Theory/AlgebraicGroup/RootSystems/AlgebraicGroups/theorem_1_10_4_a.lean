module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_3_d
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.RootSystemType

/-!
This module isolates `theorem_1_10_4_a` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
It retains the unresolved numbered declaration while the source-faithful
`HasRootSystemType` contract and its model conversion API are re-exported from
the lower `RootSystemType` module.  This preserves the public API and keeps
the model bookkeeping independent of the numbered isogeny theorem.
-/

universe u v w

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable local instance pslCarrierAlgebraicGroup (m : ℕ) :
    AlgebraicGroup
      (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierVariety :=
  (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierAlgebraicGroup

local instance torusNormalInNormalizer
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K) :
    (T.toSubgroup.subgroupOf T.normalizer.toSubgroup).Normal :=
  T.toSubgroup.normal_in_normalizer

public theorem theorem_1_10_4_a
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (hK : IsSimpleAlgebraicGroup K) (hH : IsSimpleAlgebraicGroup H)
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    {ι ι' E E' F F' : Type u} [Finite ι] [Finite ι']
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']
    (P : RootPairing ι ℝ E E') [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (Q : RootPairing ι' ℝ F F') [Q.IsRootSystem]
    [Q.IsCrystallographic] [Q.IsReduced]
    (_modelK : RootSystemModel P K) (_modelH : RootSystemModel Q H) :
    P.IsIsomorphic Q ∨
      ∃ m : ℕ, ringChar k = 2 ∧
        ((HasDynkinType P ⟨.B, m⟩ ∧ HasDynkinType Q ⟨.C, m⟩) ∨
          (HasDynkinType P ⟨.C, m⟩ ∧ HasDynkinType Q ⟨.B, m⟩)) := by sorry

end Theory.AlgebraicGroup
