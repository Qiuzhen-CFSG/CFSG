module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_1_a

/-!
This module isolates `theorem_1_10_1_b` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
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

public theorem theorem_1_10_1_b
    {K : Variety k} [AlgebraicGroup K] (hK : IsReductiveAlgebraicGroup K)
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T)
    (D : RootGroupData K T) (hD : D.IsRealization)
    {ι M N : Type u} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (e : D.Root ≃ ι)
    (hActual : IsActualBasedRootPairing D P base e)
    (d : P.OrthogonalDecomposition)
    (hd : d.IsIrreducible) :
    (∀ s ∈ d.parts,
      RootSubgroupGenerated D (e.symm '' s) =
        (connectedRootBlockSubgroup D (e.symm '' s)).toSubgroup) ∧
    (∀ s ∈ d.parts,
      IsSimpleAlgebraicGroup
        (connectedRootBlockSubgroup D (e.symm '' s)).carrierVariety) ∧
    (∀ s ∈ d.parts, ∀ t ∈ d.parts, s ≠ t →
      ⁅(connectedRootBlockSubgroup D (e.symm '' s)).toSubgroup,
        (connectedRootBlockSubgroup D (e.symm '' t)).toSubgroup⁆ = ⊥) ∧
    (subgroupZariskiClosure K
      (commutator (Variety.Point K))).toSubgroup =
      ⨆ s : d.parts,
        (connectedRootBlockSubgroup D (e.symm '' (s : Set ι))).toSubgroup ∧
    (∀ s ∈ d.parts,
      ∃ hreflect : ∀ i ∈ s, ∀ j ∈ s, P.reflectionPerm i j ∈ s,
      ∃ Ti : { Ti : ClosedSubgroup
          (connectedRootBlockSubgroup D (e.symm '' s)).carrierVariety //
          IsMaximalTorus Ti },
      ∃ Di : { Di : RootGroupData
          (connectedRootBlockSubgroup D (e.symm '' s)).carrierVariety Ti.1 //
          Di.IsRealization },
      ∃ componentBase : (P.rootSubsystem s hreflect).Base,
      ∃ componentRoots : Di.1.Root ≃ s,
        IsActualBasedRootPairing Di.1 (P.rootSubsystem s hreflect)
          componentBase componentRoots) := by sorry

end Theory.AlgebraicGroup
