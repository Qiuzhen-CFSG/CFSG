module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_6

/-!
This module isolates `theorem_1_10_7_a` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
Its coordinate-space witness is quantified in the field's universe, as required
for the standard type-A model over `k : Type u`; the classification proof
remains an independent downstream task.
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

public theorem theorem_1_10_7_a
    (m : ℕ) {Ku Ka : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup Ka]
    (hKu : IsUniversalVersion Ku) (hKa : IsAdjointVersion Ka)
    (hKuType : HasRootSystemType Ku ⟨.A, m⟩)
    (hKaType : HasRootSystemType Ka ⟨.A, m⟩) :
    ∃ V : Type u, ∃ _ : AddCommGroup V, ∃ _ : Module k V,
      ∃ _ : FiniteDimensional k V,
      Module.finrank k V = m + 1 ∧
      Nonempty (AlgebraicGroup.Iso Ku (slVarietyOf k V)) ∧
      Nonempty (@AlgebraicGroup.Iso k _ Ka
        (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierVariety
        (inferInstance : AlgebraicGroup Ka)
        (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierAlgebraicGroup) := by sorry

end Theory.AlgebraicGroup
