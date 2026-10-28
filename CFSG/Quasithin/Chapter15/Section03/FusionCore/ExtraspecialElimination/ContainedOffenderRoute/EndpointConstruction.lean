module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.OffenderLifts
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ActionGeneration
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement.GeometryTransport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Selection
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Symmetry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.StrongConstruction

/-!
# Compatible placement and strong offending

Move the elementary endpoint and its contained best lift with the same
element of H. The edge-core hypothesis is the geometric input; membership
of the contained lift in the transported star two-core is proved here.

After the component reduction, choose a symmetric endpoint using the finite
maximum in Geometry.Symmetry. At that exact endpoint, the rank comparison
gives ordinary offending and elementary nontriviality. The reduced-group
commutator theorem gives L = [L,U_gamma], and the strict span gives strong
offending. Only then choose a strong best subgroup, still inside the actual
endpoint. No whole-endpoint best assumption or endpoint change is used.

The actual F.9 endpoint data, reduced component, and strict span remain
inputs to these conditional helpers. Source: Aschbacher–Smith, combined
manuscript (1 March 2004), pp.1143–1145, proof of 15.3.49(h), (n).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute

open Subgroup Representation.BinaryOffender ComponentReduction
open FactorGeneration FactorGeneration.ConjugatePlacement
open Geometry.Symmetry
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

/-- Placement acts on both the selected lift and the original endpoint.
The input does not assert best status of the endpoint. -/
theorem exists_placed_containedBest
    (Y Y0 T H V ZS Z : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z) (g : G)
    [IsElementaryAbelian 2 (endpointModule V H g)]
    (gamma2 : Vertex Y T H) (ht : gamma2.type = false)
    (hadj : CosetGeometry.Incident (family Y T H) (base Y T H true) gamma2)
    (hB : H ⊓ (Y ⊔ T) = Y0 ⊔ T)
    (hcore : endpointModule V H g ≤
      (edgeGroup Y T H (base Y T H true) gamma2).pCoreIn 2)
    (hoff : IsOffender action.representation (starImage H (endpointModule V H g)))
    (hquad : IsQuadratic action.representation (starImage H (endpointModule V H g))) :
    ∃ d : ContainedBest H (localSpan ZS H) Z (endpointModule V H g) action,
      ∃ h : H, (h : G)⁻¹ • gamma2 = base Y T H false ∧
        starImage H (d.conjugate h⁻¹).carrier ≤ (starImage H Y0 ⊔ starImage H T).pCoreIn 2 ∧
        (d.conjugate h⁻¹).carrier ≤ endpointModule V H ((h : G)⁻¹ * g) ∧
        localSpan (d.conjugate h⁻¹).carrier H = localSpan d.carrier H := by
  obtain ⟨d⟩ := exists_containedBest H (localSpan ZS H) Z (endpointModule V H g)
    action hoff hquad
  obtain ⟨h, hv, _, hs⟩ := exists_placed_of_edgeCore Y Y0 T H
    (endpointModule V H g) gamma2 ht hadj hB hcore
  refine ⟨d, h, hv, (d.conjugate h⁻¹).starImage_le hs, ?_, d.conjugate_span h⁻¹⟩
  rw [endpointModule_right]
  exact (d.conjugate h⁻¹).le_endpoint

/-- The ordinary strong offender and a contained strong best subgroup at a
single compatible symmetric endpoint. The original endpoint images need
only be elementary; their offending and nontriviality are proved. -/
theorem exists_strong_endpoint
    {ι : Type*} [Finite ι]
    (H L T V ZS Z : Subgroup G) (ends : ι → Endpoint G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    [IsElementaryAbelian 2 (localSpan V H)]
    [∀ i, IsElementaryAbelian 2 (ends i).U]
    [∀ i, IsElementaryAbelian 2 (ends i).V]
    (action : SectionAction H (localSpan ZS H) Z)
    (opposite : ∀ i, SectionAction (ends i).K (ends i).U (ends i).Z)
    (hZS : ZS ≤ V) (hHZ : H ≤ centralizer (Z : Set G))
    (hUV : ∀ i, (ends i).U ≤ (ends i).V)
    (hVgH : ∀ i, (ends i).V ≤ H)
    (hVHK : ∀ i, localSpan V H ≤ (ends i).K)
    (hcross : ∀ i, sectionCentralizer (localSpan V H) (ends i).U (ends i).Z ≤
      centralizer ((ends i).V : Set G))
    (hcomm : ∀ i, ⁅localSpan ZS H, (ends i).V⁆ ≤ (ends i).V)
    (hselected : ∃ i,
      0 < Nat.log 2 ((sectionCentralizer (ends i).U (localSpan ZS H) Z).relIndex (ends i).U) ∧
      Nat.log 2 ((sectionCentralizer (localSpan ZS H) (ends i).U (ends i).Z).relIndex
        (localSpan ZS H)) ≤
      Nat.log 2 ((sectionCentralizer (ends i).U (localSpan ZS H) Z).relIndex (ends i).U))
    (hreversal : ∀ i,
      0 < Nat.log 2 ((sectionCentralizer (ends i).U (localSpan ZS H) Z).relIndex (ends i).U) →
      ∃ j, Reversal ⟨H, localSpan ZS H, localSpan V H, Z⟩ (ends i) (ends j))
    (hgen : H = L ⊔ T) (hn : H ≤ normalizer (L : Set G)) (hT : IsPGroup 2 T)
    (hL : (L.subgroupOf H).IsCComponent)
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hTV : T ≤ normalizer (V : Set G)) (hVH : localSpan V H ≤ H)
    (hproper : localSpan ZS H ⊔ V < localSpan V H) :
    ∃ i, IsStrongOffender action.representation (starImage H (ends i).V) ∧
      ∃ d : ContainedBest H (localSpan ZS H) Z (ends i).V action,
        IsStrongOffender action.representation (starImage H d.carrier) := by
  obtain ⟨i, hi, hsym⟩ := exists_symmetric_cover H V ZS Z ends action opposite
    hZS hHZ hUV hVgH hVHK hcross hselected hreversal
  have hnorm : localSpan ZS H ≤ normalizer ((ends i).Z : Set G) :=
    ((conjugateSpanBy_mono hZS le_rfl).trans (hVHK i)).trans (opposite i).normalizes_layer
  obtain ⟨hfixed, hrank, hU, hV, _, hquad⟩ :=
    Geometry.selected_rank_and_quadratic_offenders V ZS Z H (ends i).U (ends i).V
      (ends i).Z action hZS (hUV i) (hVgH i) hHZ hnorm (hcross i) (hcomm i) hi
  have hLU := commutator_eq_of_reduced_two_subgroup H L T (ends i).U hgen hn hT
    ((hUV i).trans (hVgH i)) hL hq hU.1
  have hs := strong_from_symmetric_cover H L T V ZS Z (ends i).U (ends i).V action
    (Geometry.sectionImage (localSpan ZS H) Z
      (sectionCentralizer (localSpan ZS H) (ends i).U (ends i).Z))
    hU.1 hV.1 (hUV i) (hVgH i) hfixed hrank hsym hgen hZS hTV hVH hLU hproper
  exact ⟨i, hs, exists_strong_containedBest H (localSpan ZS H) Z (ends i).V action hs hquad⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
