module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_4_c

/-!
This module states the two-factor decomposition of universal and adjoint
semisimple algebraic groups from GLS3, Chapter 1, Proposition 1.10.6.  The root
pairing of the first group has exactly two distinct orthogonal parts, each
identified with the root pairing of one factor; the two explicit
reflection-closure hypotheses construct those root subsystems.  The eventual
proof combines the corresponding orthogonal-sum equivalence with product
stability and uniqueness of the extreme versions.

Distinctness is a necessary part of the contract: if `s₁ = s₂`, the pair set
`{s₁, s₂}` collapses to one part and cannot support the claimed duplicated
product decomposition.
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

public theorem theorem_1_10_6
    {K K₁ K₂ : Variety k}
    [AlgebraicGroup K] [AlgebraicGroup K₁] [AlgebraicGroup K₂]
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T)
    (T₁ : ClosedSubgroup K₁) (hT₁ : IsMaximalTorus T₁)
    (T₂ : ClosedSubgroup K₂) (hT₂ : IsMaximalTorus T₂)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (D₁ : RootGroupData K₁ T₁) (hD₁ : D₁.IsRealization)
    (D₂ : RootGroupData K₂ T₂) (hD₂ : D₂.IsRealization)
    {ι ι₁ ι₂ M N M₁ N₁ M₂ N₂ : Type u}
    [Fintype ι] [Fintype ι₁] [Fintype ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₁] [Module ℝ M₁] [AddCommGroup N₁] [Module ℝ N₁]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) [P₁.IsRootSystem] [P₁.IsCrystallographic] [P₁.IsReduced]
    (P₂ : RootPairing ι₂ ℝ M₂ N₂) [P₂.IsRootSystem] [P₂.IsCrystallographic] [P₂.IsReduced]
    (b : P.Base) (b₁ : P₁.Base) (b₂ : P₂.Base)
    (e : D.Root ≃ ι) (e₁ : D₁.Root ≃ ι₁) (e₂ : D₂.Root ≃ ι₂)
    (hActual : IsActualBasedRootPairing D P b e)
    (hActual₁ : IsActualBasedRootPairing D₁ P₁ b₁ e₁)
    (hActual₂ : IsActualBasedRootPairing D₂ P₂ b₂ e₂)
    (d : P.OrthogonalDecomposition) (s₁ s₂ : Set ι)
    (hparts : d.parts = {s₁, s₂})
    (hne : s₁ ≠ s₂)
    (hreflect₁ : ∀ i ∈ s₁, ∀ j ∈ s₁, P.reflectionPerm i j ∈ s₁)
    (hreflect₂ : ∀ i ∈ s₂, ∀ j ∈ s₂, P.reflectionPerm i j ∈ s₂)
    (hroot₁ : Nonempty (P₁.Equiv (P.rootSubsystem s₁ hreflect₁)))
    (hroot₂ : Nonempty (P₂.Equiv (P.rootSubsystem s₂ hreflect₂))) :
    (IsUniversalVersion K ∧ IsUniversalVersion K₁ ∧
        IsUniversalVersion K₂ →
      Nonempty (AlgebraicGroup.Iso K (Variety.prod K₁ K₂))) ∧
    (IsAdjointVersion K ∧ IsAdjointVersion K₁ ∧
        IsAdjointVersion K₂ →
      Nonempty (AlgebraicGroup.Iso K (Variety.prod K₁ K₂))) := by sorry

end Theory.AlgebraicGroup
