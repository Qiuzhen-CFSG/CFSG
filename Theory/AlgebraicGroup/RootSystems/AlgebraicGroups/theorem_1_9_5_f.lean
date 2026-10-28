module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_9_5_e

/-!
This module isolates `theorem_1_9_5_f` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
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

public theorem theorem_1_9_5_f
    {K : Variety k} [AlgebraicGroup K] (hK : IsReductiveAlgebraicGroup K)
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T)
    (D : RootGroupData K T) (hD : D.IsRealization)
    {ι M N : Type u} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (e : D.Root ≃ ι)
    (hActual : IsActualBasedRootPairing D P base e) :
    let : (T.toSubgroup.subgroupOf T.normalizer.toSubgroup).Normal :=
      T.toSubgroup.normal_in_normalizer
    Nonempty
      ((T.normalizer.toSubgroup ⧸
          T.toSubgroup.subgroupOf T.normalizer.toSubgroup) ≃* P.weylGroup) ∧
    ∃ weylEquiv :
        (T.normalizer.toSubgroup ⧸
          T.toSubgroup.subgroupOf T.normalizer.toSubgroup) ≃* P.weylGroup,
      (∀ (n : T.normalizer.toSubgroup) (α : D.Root),
        (D.rootSubgroup α).conjugate ((n : Variety.Point K)⁻¹) =
          D.rootSubgroup
            (e.symm (P.weylGroupToPerm
              (weylEquiv
                (QuotientGroup.mk'
                  (T.toSubgroup.subgroupOf T.normalizer.toSubgroup) n))⁻¹
              (e α)))) ∧
      (∀ α : D.Root, ∃ n : T.normalizer.toSubgroup,
        weylEquiv
            (QuotientGroup.mk'
              (T.toSubgroup.subgroupOf T.normalizer.toSubgroup) n) =
          RootPairing.weylGroup.ofIdx P (e α)) := by sorry

end Theory.AlgebraicGroup
