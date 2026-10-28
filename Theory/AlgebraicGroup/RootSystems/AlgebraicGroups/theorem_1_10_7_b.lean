module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_7_a
public import Theory.AlgebraicGroup.RootSystems.OddOrthogonalCarrier
public import Theory.AlgebraicGroup.RootSystems.OddQuadraticSpace

/-!
This module isolates `theorem_1_10_7_b` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.

The concrete odd Spin/SO witness in the conclusion uses
`OddOrthogonalModel`, whose Clifford conjugation field requires Mathlib's
`[Invertible (2 : k)]` action hypothesis.  This theorem therefore makes the
same characteristic-not-two instance explicit; the field-only scope would
include algebraic closures of `ZMod 2`, where that action theorem is
unavailable.
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

public theorem theorem_1_10_7_b
    (m : ℕ) (hm : 2 ≤ m)
    {Ku Ka : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup Ka]
    [Invertible (2 : k)]
    (hKu : IsUniversalVersion Ku) (hKa : IsAdjointVersion Ka)
    (hKuType : HasRootSystemType Ku ⟨.B, m⟩)
    (hKaType : HasRootSystemType Ka ⟨.B, m⟩) :
    ∃ V : Type u, ∃ _ : AddCommGroup V, ∃ _ : Module k V,
      ∃ _ : FiniteDimensional k V, ∃ q : QuadraticForm k V,
      Module.finrank k V = 2 * m + 1 ∧ q.Nondegenerate ∧
      ∃ model : OddOrthogonalModel q,
        letI := model.spin.carrierAlgebraicGroup
        letI := model.specialOrthogonal.carrierAlgebraicGroup
        Nonempty (AlgebraicGroup.Iso Ku model.spin.carrierVariety) ∧
        Nonempty (AlgebraicGroup.Iso Ka model.specialOrthogonal.carrierVariety) := by sorry

end Theory.AlgebraicGroup
