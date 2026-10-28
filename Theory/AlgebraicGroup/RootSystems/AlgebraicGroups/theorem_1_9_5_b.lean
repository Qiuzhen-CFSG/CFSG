module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_9_5_a

/-!
This module isolates `theorem_1_9_5_b` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.  The root-system realization reuses the root
cocharacters owned by its realized `RootGroupData`; this makes the Cartan
equation here the root-weight specialization of the full character--coroot
pairing from GLS3, Remarks 1.9.6.
-/

universe u v w

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable local instance pslCarrierAlgebraicGroup (m : ℕ) :
    AlgebraicGroup
      (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierVariety :=
  (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierAlgebraicGroup

public theorem theorem_1_9_5_b
    {K : Variety k} [AlgebraicGroup K] (hK : IsReductiveAlgebraicGroup K)
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T) (χ : TorusWeight T)
    (hχ : IsTorusRoot T χ) :
    ∃! X : ClosedSubgroup K, IsTorusRootSubgroup T X ∧
      RootWeightEquation T X χ := by sorry

public structure TorusRootSystemIdentification
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) where
  rootFinite : Finite D.Root
  rank : ℕ
  pairing : RootPairing D.Root ℝ (Fin rank → ℝ) (Fin rank → ℝ)
  isRootSystem : pairing.IsRootSystem
  isCrystallographic : pairing.IsCrystallographic
  isReduced : pairing.IsReduced
  add_iff : ∀ α β γ,
    D.rootWeight γ = D.rootWeight α * D.rootWeight β ↔
      pairing.root γ = pairing.root α + pairing.root β
  pairing_eq : ∀ α β,
    pairing.pairing α β = D.pairing α β

local instance torusNormalInNormalizer
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K) :
    (T.toSubgroup.subgroupOf T.normalizer.toSubgroup).Normal :=
  T.toSubgroup.normal_in_normalizer

public structure TorusRootSystemRealization
    (K : Variety k) [AlgebraicGroup K] (T : ClosedSubgroup K) where
  data : RootGroupData K T
  isRealization : data.IsRealization
  identification : TorusRootSystemIdentification data

/-- Compatibility accessor for the root cocharacters now owned by the realized
root-group datum. -/
@[expose]
public def TorusRootSystemRealization.rootCocharacter
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (R : TorusRootSystemRealization K T) :
    R.data.Root → ClosedSubgroupTorusCocharacter T :=
  R.data.rootCocharacter

omit [IsAlgClosed k] in
/-- Compatibility theorem for the Cartan equation on root weights. -/
public theorem TorusRootSystemRealization.rootCocharacter_spec
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (R : TorusRootSystemRealization K T) (α β : R.data.Root) :
    WeightCocharacterEquation T (R.data.rootWeight α) (R.rootCocharacter β)
      (R.data.pairing α β) :=
  R.isRealization.rootWeight_rootCocharacter α β

end Theory.AlgebraicGroup
