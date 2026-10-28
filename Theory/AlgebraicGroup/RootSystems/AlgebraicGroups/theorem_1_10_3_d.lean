module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_1_b
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ChevalleyVersions

/-!
This module isolates `theorem_1_10_3_d` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
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

public theorem theorem_1_10_3_d
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (hK : IsSemisimpleAlgebraicGroup K) (hH : IsSemisimpleAlgebraicGroup H)
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (B : ClosedSubgroup K) (hB : IsBorelSubgroup B)
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T) :
    IsBorelSubgroup (φ.comp B.inclusion).imageClosedSubgroup ∧
    IsMaximalTorus (φ.comp T.inclusion).imageClosedSubgroup ∧
    ((∃ e : AlgebraicGroup.Iso K H, e.hom = φ) ↔
      ∃ eB : AlgebraicGroup.Iso B.carrierVariety
          (φ.comp B.inclusion).imageClosedSubgroup.carrierVariety,
        ∀ x,
          (φ.comp B.inclusion).imageClosedSubgroup.inclusion.onPoints
              (eB.hom.onPoints x) =
            φ.onPoints (B.inclusion.onPoints x)) := by
  have hBimg : IsBorelSubgroup (φ.comp B.inclusion).imageClosedSubgroup :=
    isogeny_image_isBorel φ hφ hK.1 B hB
  have hTimg : IsMaximalTorus (φ.comp T.inclusion).imageClosedSubgroup :=
    isogeny_image_isMaximalTorus φ hφ T hT
  refine ⟨hBimg, hTimg, ?_⟩
  constructor
  · intro he
    apply (borel_restriction_iso_of_global_isomorphism φ hφ hK.1 hH.1 hK hH B T hB hT)
    rcases he with ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro x
    rw [he]
  · sorry

end Theory.AlgebraicGroup
