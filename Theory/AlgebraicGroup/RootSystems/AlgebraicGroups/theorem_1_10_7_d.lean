module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_7_c

/-!
This module isolates `theorem_1_10_7_d` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
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

public theorem theorem_1_10_7_d
    (m : ℕ) (hm : 4 ≤ m)
    {Ku Ka : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup Ka]
    (hKu : IsUniversalVersion Ku) (hKa : IsAdjointVersion Ka)
    (hKuType : HasRootSystemType Ku ⟨.D, m⟩)
    (hKaType : HasRootSystemType Ka ⟨.D, m⟩) :
    ∃ V : Type u, ∃ _ : AddCommGroup V, ∃ _ : Module k V,
      ∃ _ : FiniteDimensional k V, ∃ q : QuadraticForm k V,
      Module.finrank k V = 2 * m ∧ q.Nondegenerate ∧
      ∃ model : EvenOrthogonalModel q,
        letI := model.spin.carrierAlgebraicGroup
        letI := model.omega.carrierAlgebraicGroup
        letI := model.projectiveOmegaAlgebraicGroup
        Nonempty (AlgebraicGroup.Iso Ku model.spin.carrierVariety) ∧
        Nonempty (AlgebraicGroup.Iso Ka model.projectiveOmega) := by sorry

end Theory.AlgebraicGroup
