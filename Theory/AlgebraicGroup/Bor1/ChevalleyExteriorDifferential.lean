module

public import Theory.AlgebraicGroup.Bor1.AdaptedBasis
public import Theory.AlgebraicGroup.Bor1.ExteriorWedgeDifferential
public import Theory.AlgebraicGroup.Bor1.InfinitesimalChevalleyStabilizer
public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialIndependence
public import Theory.AlgebraicGroup.Bor1.RightTranslationDifferential

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A basis of Chevalley's finite right-translation space whose initial block
is the distinguished vanishing subspace. -/
@[expose]
public noncomputable def ClosedSubgroup.chevalleyAdaptedBasis
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Module.Basis (Fin (Module.finrank k H.rightTranslateVanishingSpan)) k
      H.rightTranslateVanishingSpan :=
  Classical.choose (exists_basis_extends_finBasis
    H.rightTranslateVanishingSubspaceInSpan)

omit [IsAlgClosed k] in
/-- The distinguished vanishing subspace has rank at most the ambient finite
right-translation space. -/
public theorem ClosedSubgroup.chevalleyAdaptedRankLE
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    H.rightTranslateVanishingTopWedgeData.degree ≤
      Module.finrank k H.rightTranslateVanishingSpan :=
  Classical.choose (Classical.choose_spec (exists_basis_extends_finBasis
    H.rightTranslateVanishingSubspaceInSpan))

/-- The order embedding selecting the initial adapted-basis block. -/
@[expose]
public noncomputable def ClosedSubgroup.chevalleyAdaptedIndex
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Fin H.rightTranslateVanishingTopWedgeData.degree ↪o
      Fin (Module.finrank k H.rightTranslateVanishingSpan) :=
  Fin.castLEOrderEmb (ClosedSubgroup.chevalleyAdaptedRankLE H)

set_option linter.unusedSectionVars false in
/-- The initial entries of the adapted basis are the distinguished subspace's
canonical finite basis. -/
public theorem ClosedSubgroup.chevalleyAdaptedBasis_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (j : Fin H.rightTranslateVanishingTopWedgeData.degree) :
    ClosedSubgroup.chevalleyAdaptedBasis H
        (ClosedSubgroup.chevalleyAdaptedIndex H j) =
      (Module.finBasis k H.rightTranslateVanishingSubspaceInSpan j :
        H.rightTranslateVanishingSpan) := by
  change ClosedSubgroup.chevalleyAdaptedBasis H
      (Fin.castLE (ClosedSubgroup.chevalleyAdaptedRankLE H) j) = _
  exact Classical.choose_spec (Classical.choose_spec
    (exists_basis_extends_finBasis H.rightTranslateVanishingSubspaceInSpan)) j

/-- The coordinate differential of the exterior-power Chevalley
representation on its distinguished top wedge. -/
@[expose]
public noncomputable def ClosedSubgroup.chevalleyExteriorWedgeDifferential
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    IdentityPointDerivation G →ₗ[k]
      (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan) :=
  rationalRepresentationExteriorWedgeDifferential
    (⟨H.rightTranslateVanishingSpanGeneralLinear⟩ :
      RationalRepresentation G H.rightTranslateVanishingSpan)
    (ClosedSubgroup.chevalleyAdaptedBasis H)
    (H.rightTranslateVanishingRepresentationMorphismOfBasis
      (ClosedSubgroup.chevalleyAdaptedBasis H))
    (ClosedSubgroup.chevalleyAdaptedIndex H)

/-- The initial adapted-basis block spans exactly the distinguished vanishing
subspace. -/
public theorem ClosedSubgroup.chevalleyAdaptedInitialSpan_eq
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Submodule.span k (Set.range fun j =>
      ClosedSubgroup.chevalleyAdaptedBasis H
        (ClosedSubgroup.chevalleyAdaptedIndex H j)) =
      H.rightTranslateVanishingSubspaceInSpan := by
  rw [show (Set.range fun j => ClosedSubgroup.chevalleyAdaptedBasis H
      (ClosedSubgroup.chevalleyAdaptedIndex H j)) =
      Set.range fun j =>
        (Module.finBasis k H.rightTranslateVanishingSubspaceInSpan j :
          H.rightTranslateVanishingSpan) by
    ext x
    simp only [Set.mem_range]
    constructor <;> rintro ⟨j, rfl⟩
    · refine ⟨j, ?_⟩
      simpa [ClosedSubgroup.chevalleyAdaptedIndex] using
        (ClosedSubgroup.chevalleyAdaptedBasis_apply H j).symm
    · refine ⟨j, ?_⟩
      simpa [ClosedSubgroup.chevalleyAdaptedIndex] using
        ClosedSubgroup.chevalleyAdaptedBasis_apply H j]
  rw [show (Set.range fun j =>
      (Module.finBasis k H.rightTranslateVanishingSubspaceInSpan j :
        H.rightTranslateVanishingSpan)) =
      H.rightTranslateVanishingSubspaceInSpan.subtype ''
        Set.range (Module.finBasis k H.rightTranslateVanishingSubspaceInSpan) by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨Module.finBasis k H.rightTranslateVanishingSubspaceInSpan j,
        ⟨j, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩]
  rw [← Submodule.map_span,
    (Module.finBasis k H.rightTranslateVanishingSubspaceInSpan).span_eq,
    Submodule.map_top, Submodule.range_subtype]

/-- The top wedge of the initial adapted-basis block is Chevalley's Pluecker
vector. -/
public theorem ClosedSubgroup.chevalleyAdaptedTopWedge_eq_plucker
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    exteriorPower.ιMulti k
        (Module.finrank k H.rightTranslateVanishingSubspaceInSpan)
        (fun j => ClosedSubgroup.chevalleyAdaptedBasis H
          (ClosedSubgroup.chevalleyAdaptedIndex H j)) =
      H.rightTranslateVanishingPluckerVector := by
  rw [ClosedSubgroup.rightTranslateVanishingPluckerVector]
  change _ = exteriorPower.map
    (Module.finrank k H.rightTranslateVanishingSubspaceInSpan)
      H.rightTranslateVanishingSubspaceInSpan.subtype
      (exteriorPower.ιMulti k
        (Module.finrank k H.rightTranslateVanishingSubspaceInSpan)
        (Module.finBasis k H.rightTranslateVanishingSubspaceInSpan))
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext j
  simpa [ClosedSubgroup.chevalleyAdaptedIndex] using
    ClosedSubgroup.chevalleyAdaptedBasis_apply H j

/-- Infinitesimal stability of Chevalley's Pluecker line detects tangent
vectors coming from the closed subgroup. -/
public theorem ClosedSubgroup.identityTangent_mem_range_of_chevalleyExteriorWedgeDifferential_line
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (D : IdentityPointDerivation G)
    (hline : ClosedSubgroup.chevalleyExteriorWedgeDifferential H D ∈
      k ∙ H.rightTranslateVanishingPluckerVector) :
    D ∈ LinearMap.range (identityTangentMorphismLinearMap H.inclusion) := by
  apply identityTangent_mem_range_of_infinitesimalChevalley_stable H D
    (ClosedSubgroup.rightTranslateVanishingSpanDifferential H D)
  · exact ClosedSubgroup.rightTranslateVanishingSpanDifferential_eval_one H D
  · intro q hq
    have hline' :
        rationalRepresentationExteriorWedgeDifferential
            (⟨H.rightTranslateVanishingSpanGeneralLinear⟩ :
              RationalRepresentation G H.rightTranslateVanishingSpan)
            (ClosedSubgroup.chevalleyAdaptedBasis H)
            (H.rightTranslateVanishingRepresentationMorphismOfBasis
              (ClosedSubgroup.chevalleyAdaptedBasis H))
            (ClosedSubgroup.chevalleyAdaptedIndex H) D ∈
          k ∙ exteriorPower.ιMulti k
            (Module.finrank k H.rightTranslateVanishingSubspaceInSpan)
            (fun j => ClosedSubgroup.chevalleyAdaptedBasis H
              (ClosedSubgroup.chevalleyAdaptedIndex H j)) := by
      rw [ClosedSubgroup.chevalleyAdaptedTopWedge_eq_plucker H]
      exact hline
    have hpreserved :=
      rationalRepresentationDifferential_preserves_initialSpan_of_exteriorWedge_line
        (⟨H.rightTranslateVanishingSpanGeneralLinear⟩ :
          RationalRepresentation G H.rightTranslateVanishingSpan)
        (ClosedSubgroup.chevalleyAdaptedBasis H)
        (H.rightTranslateVanishingRepresentationMorphismOfBasis
          (ClosedSubgroup.chevalleyAdaptedBasis H))
        (ClosedSubgroup.rightTranslateVanishingRepresentationMorphismOfBasis_pointEquiv
          H (ClosedSubgroup.chevalleyAdaptedBasis H))
        D (ClosedSubgroup.chevalleyAdaptedIndex H) hline' q
    rw [ClosedSubgroup.chevalleyAdaptedInitialSpan_eq H] at hpreserved
    have hdiff :
        rationalRepresentationDifferential
            (⟨H.rightTranslateVanishingSpanGeneralLinear⟩ :
              RationalRepresentation G H.rightTranslateVanishingSpan)
            (ClosedSubgroup.chevalleyAdaptedBasis H)
            (H.rightTranslateVanishingRepresentationMorphismOfBasis
              (ClosedSubgroup.chevalleyAdaptedBasis H)) =
          ClosedSubgroup.rightTranslateVanishingSpanDifferential H := by
      rw [ClosedSubgroup.rightTranslateVanishingSpanDifferential]
      exact rationalRepresentationDifferential_eq_of_point_action
        (⟨H.rightTranslateVanishingSpanGeneralLinear⟩ :
          RationalRepresentation G H.rightTranslateVanishingSpan)
        (ClosedSubgroup.chevalleyAdaptedBasis H)
        H.rightTranslateVanishingSpanBasis
        (H.rightTranslateVanishingRepresentationMorphismOfBasis
          (ClosedSubgroup.chevalleyAdaptedBasis H))
        (H.rightTranslateVanishingRepresentationMorphismOfBasis
          H.rightTranslateVanishingSpanBasis)
        (ClosedSubgroup.rightTranslateVanishingRepresentationMorphismOfBasis_pointEquiv
          H (ClosedSubgroup.chevalleyAdaptedBasis H))
        (ClosedSubgroup.rightTranslateVanishingRepresentationMorphismOfBasis_pointEquiv
          H H.rightTranslateVanishingSpanBasis)
    rw [hdiff] at hpreserved
    exact hpreserved hq

end Theory.AlgebraicGroup.Bor1
