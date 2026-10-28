module

public import CFSG.Quasithin.ChapterF.Section09.CriticalEndpoints
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.GeometricAssembly
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Conjugation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement.IntrinsicGeometry

/-!
# The extraspecial consumer's family from original F.9 geometry

The finite family consists of actual normalized critical endpoints. The
source edge embedding preserves its literal two-core. The two section actions,
omega-center bound and normalizer test give a proper small-span action kernel
at every endpoint. Simultaneous reversal exchanges the two small ranks, so one
orientation has the required rank inequality. This discharges the geometric
premises of the existing contained-offender construction.

Source: Aschbacher–Smith, F.9.13, F.9.16(4), F.9.17 and 15.3.49(c–h),
combined manuscript (1 March 2004), printed pp.322–324, 1143.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
open Subgroup Representation.BinaryOffender ComponentReduction
open FactorGeneration FactorGeneration.ConjugatePlacement Geometry.Symmetry
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem source_edge_witness (Y T H A : Subgroup G)
    {F : Bool → Subgroup (geometryGroup Y T H)} (hF : F = sourceFamily Y T H)
    (w : CosetGeometry.Vertex F) (hwt : w.type = false)
    (hw : (CosetGeometry.RankTwo.graph F).Adj (CosetGeometry.base F true) w)
    (hc : A ≤ ((MulAction.stabilizer (geometryGroup Y T H) (CosetGeometry.base F true) ⊓
      MulAction.stabilizer (geometryGroup Y T H) w).map (geometryGroup Y T H).subtype).pCoreIn 2) :
    ∃ v : Vertex Y T H, v.type = false ∧
      CosetGeometry.Incident (family Y T H) (base Y T H true) v ∧
      A ≤ (edgeGroup Y T H (base Y T H true) v).pCoreIn 2 := by
  subst F
  refine ⟨sourceEmbedding Y T H w, hwt, ?_, ?_⟩
  · simpa only [sourceEmbedding_base] using
      sourceEmbedding_incident Y T H (sourceBase Y T H true) w hw.2
  · have he :
        ((MulAction.stabilizer (geometryGroup Y T H) (sourceBase Y T H true) ⊓
          MulAction.stabilizer (geometryGroup Y T H) w).map
            (geometryGroup Y T H).subtype) =
        edgeGroup Y T H (sourceEmbedding Y T H (sourceBase Y T H true))
          (sourceEmbedding Y T H w) := by
      simpa only [sourceEdgeGroup] using
        source_edge_image Y T H (sourceBase Y T H true) w
    simpa only [he, sourceEmbedding_base] using hc

omit [Finite G] in
private theorem starRank_conjugate (H A : Subgroup G) (hAH : A ≤ H) (g : G) :
    rank (starImage (H.map (MulAut.conj g).toMonoidHom)
      (A.map (MulAut.conj g).toMonoidHom)) = rank (starImage H A) := by
  rw [rank, rank, Geometry.starImage_card _ _ (map_mono hAH), Geometry.starImage_card H A hAH]
  change Nat.log 2 (((H.map (MulAut.conj g).toMonoidHom).pCoreIn 2).relIndex
    (A.map (MulAut.conj g).toMonoidHom)) = _
  rw [← map_pCoreIn_of_injective 2 H _ (MulAut.conj g).injective,
    relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  rfl

variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] [IsElementaryAbelian 2 D.VH]

local instance original_UH_elementary : IsElementaryAbelian 2 (localSpan D.Vplus D.H) :=
  ‹IsElementaryAbelian 2 D.UH›
local instance original_VH_elementary : IsElementaryAbelian 2 (localSpan D.V D.H) :=
  ‹IsElementaryAbelian 2 D.VH›

omit [IsElementaryAbelian 2 D.UH] [IsElementaryAbelian 2 D.VH] in
private theorem original_endpoint_eq (i : h.CriticalEndpoint) :
    spanEndpoint D.H D.V D.Vplus D.V₁ i.representative =
      Endpoint.mk (i.conjugate D.H) (i.conjugate D.UH)
        (i.conjugate D.VH) (i.conjugate D.V₁) := by
  rw [spanEndpoint_eq_conjugate]
  rfl

/-- The genuine earlier local inputs produce the entire finite endpoint family
consumed by the contained-offender contradiction, including rank selection. -/
noncomputable def geometricFamily_of_original
    (action : SectionAction D.H D.UH D.V₁)
    (hcenter : D.UH ≤
      (center (omegaOneAmbient (localTwoCore D.H))).map
        (omegaOneAmbient (localTwoCore D.H)).subtype)
    (htest : Geometry.ConjugateNormalizerTest D.V D.Vplus)
    (hcore : D.V ≤ D.QH)
    (hc : ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V, D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    GeometricFamily h.CriticalEndpoint D.L (D.T : Subgroup G) D.H D.V D.Vplus D.V₁ := by
  classical
  have hb := (h.b_bounds_of_intersecting_conjugates_commute hcore hc).1
  let ends (i : h.CriticalEndpoint) := spanEndpoint D.H D.V D.Vplus D.V₁ i.representative
  have he (i) : ends i = Endpoint.mk (i.conjugate D.H) (i.conjugate D.UH)
      (i.conjugate D.VH) (i.conjugate D.V₁) := original_endpoint_eq h i
  letI (i : h.CriticalEndpoint) : IsElementaryAbelian 2 (ends i).U :=
    spanEndpoint_elementary_small D.H D.V D.Vplus D.V₁ i.representative
  letI (i : h.CriticalEndpoint) : IsElementaryAbelian 2 (ends i).V :=
    spanEndpoint_elementary_large D.H D.V D.Vplus D.V₁ i.representative
  let opposite (i : h.CriticalEndpoint) : SectionAction (ends i).K (ends i).U (ends i).Z := by
    simpa only [he] using action.conjugate h.UH_le_H i.representative
  have hcenter' (i) : (ends i).U ≤
      (center (omegaOneAmbient (localTwoCore (ends i).K))).map
        (omegaOneAmbient (localTwoCore (ends i).K)).subtype := by
    have hh := Geometry.centered_conjugate hcenter i.representative
    change (ends i).U ≤ (center (omegaOneAmbient
      (localTwoCore (D.H.map (MulAut.conj i.representative).toMonoidHom)))).map
        (omegaOneAmbient (localTwoCore
          (D.H.map (MulAut.conj i.representative).toMonoidHom))).subtype
    simpa only [he] using hh
  have hUV (i) : (ends i).U ≤ (ends i).V := by
    rw [he]
    exact map_mono (conjugateSpanBy_mono h.plus_le le_rfl)
  have hVH (i) : (ends i).V ≤ D.H := by simpa only [he] using i.large_le hb
  have hrev (i) : D.VH ≤ (ends i).K := by simpa only [he] using i.reverse_le hb
  have hcomm (i) : ⁅D.VH, (ends i).V⁆ ≤ D.VH ⊓ (ends i).V := by
    simpa only [he] using i.commutator hb
  have hnoncentral (i) : ¬ ⁅(ends i).U, D.V⁆ ≤ (ends i).Z := by
    simpa only [he] using i.noncentral
  have hcross (i) :
      sectionCentralizer (ends i).V D.UH D.V₁ ≤ centralizer (D.VH : Set G) ∧
      sectionCentralizer D.VH (ends i).U (ends i).Z ≤ centralizer ((ends i).V : Set G) := by
    let : IsElementaryAbelian 2
        (localSpan (D.Vplus.map (MulAut.conj i.representative).toMonoidHom) (ends i).K) :=
      spanEndpoint_elementary_small D.H D.V D.Vplus D.V₁ i.representative
    let : IsElementaryAbelian 2
        (localSpan (D.V.map (MulAut.conj i.representative).toMonoidHom) (ends i).K) :=
      spanEndpoint_elementary_large D.H D.V D.Vplus D.V₁ i.representative
    exact Geometry.crossCentralizations D.V D.Vplus D.V₁ D.H (ends i).K i.representative
      action (opposite i) (hVH i) (hrev i) hcenter (hcenter' i) (hcomm i) htest
  have hproper (i) : sectionCentralizer (ends i).U D.UH D.V₁ < (ends i).U :=
    (Geometry.centralizer_equality_and_proper_kernel D.V D.Vplus D.H (ends i).U
      (ends i).V D.V₁ (ends i).Z (hUV i)
      (((hUV i).trans (hVH i)).trans action.normalizes_layer)
      (hcross i).2 (hcross i).1 (hnoncentral i)).2
  have hpos (i) : 0 < Nat.log 2
      ((sectionCentralizer (ends i).U D.UH D.V₁).relIndex (ends i).U) := by
    have hn : (sectionCentralizer (ends i).U D.UH D.V₁).relIndex (ends i).U ≠ 1 :=
      fun hh => (hproper i).not_ge (relIndex_eq_one.mp hh)
    have hz : (sectionCentralizer (ends i).U D.UH D.V₁).relIndex (ends i).U ≠ 0 :=
      index_ne_zero_of_finite
    exact Nat.log_pos (by decide) (by omega)
  have hescape (i : h.CriticalEndpoint) : ¬ i.conjugate D.UH ≤ D.QH := by
    intro hu
    apply (hproper i).not_ge
    rw [Geometry.sectionCentralizer_eq_core_intersection D.H D.UH D.V₁
      (ends i).U action ((hUV i).trans (hVH i)), he]
    exact le_inf le_rfl hu
  have reversal (i) : ∃ j, Reversal ⟨D.H, D.UH, D.VH, D.V₁⟩ (ends i) (ends j) := by
    obtain ⟨j, hj⟩ := i.reverse_labels hb (hescape i)
    refine ⟨j, j.representative, ?_, ?_⟩
    · rw [he]
      rfl
    · rw [he]
      change Endpoint.mk _ _ _ _ = Endpoint.mk _ _ _ _
      rw [hj D.H D.H.le_normalizer,
        hj D.UH (le_normalizer_conjugateSpanBy D.Vplus D.H),
        hj D.VH (le_normalizer_conjugateSpanBy D.V D.H),
        hj D.V₁ (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))]
  have hforward (i) : Nat.log 2
      ((sectionCentralizer (ends i).U D.UH D.V₁).relIndex (ends i).U) =
      rank (starImage D.H (ends i).U) :=
    (Geometry.starImage_rank D.H (ends i).U _ ((hUV i).trans (hVH i))
      (Geometry.sectionCentralizer_eq_core_intersection D.H D.UH D.V₁ _ action
        ((hUV i).trans (hVH i)))).symm
  have hback (i) : Nat.log 2
      ((sectionCentralizer D.UH (ends i).U (ends i).Z).relIndex D.UH) =
      rank (starImage (ends i).K D.UH) :=
    (Geometry.starImage_rank (ends i).K D.UH _
      ((conjugateSpanBy_mono h.plus_le le_rfl).trans (hrev i))
      (Geometry.sectionCentralizer_eq_core_intersection (ends i).K (ends i).U (ends i).Z
        D.UH (opposite i) ((conjugateSpanBy_mono h.plus_le le_rfl).trans (hrev i)))).symm
  have selected : ∃ i,
      0 < Nat.log 2 ((sectionCentralizer (ends i).U D.UH D.V₁).relIndex (ends i).U) ∧
      Nat.log 2 ((sectionCentralizer D.UH (ends i).U (ends i).Z).relIndex D.UH) ≤
        Nat.log 2 ((sectionCentralizer (ends i).U D.UH D.V₁).relIndex (ends i).U) := by
    obtain ⟨i⟩ := h.criticalEndpoint_nonempty hcore hc
    by_cases hle : rank (starImage (ends i).K D.UH) ≤ rank (starImage D.H (ends i).U)
    · exact ⟨i, hpos i, by rwa [hforward, hback]⟩
    · obtain ⟨j, g, hbase, hend⟩ := reversal i
      have hH := congrArg Endpoint.K hbase
      have hU := congrArg Endpoint.U hbase
      have hK := congrArg Endpoint.K hend
      have hUg := congrArg Endpoint.U hend
      dsimp only [Endpoint.conjugate] at hH hU hK hUg
      have hjforward : rank (starImage D.H (ends j).U) =
          rank (starImage (ends i).K D.UH) := by
        have hh := starRank_conjugate (ends i).K D.UH
          ((conjugateSpanBy_mono h.plus_le le_rfl).trans (hrev i)) g
        rwa [hK, hU] at hh
      have hjback : rank (starImage (ends j).K D.UH) =
          rank (starImage D.H (ends i).U) := by
        have hh := starRank_conjugate D.H (ends i).U ((hUV i).trans (hVH i)) g
        rwa [hH, hUg] at hh
      refine ⟨j, hpos j, ?_⟩
      rw [hforward, hback, hjforward, hjback]
      omega
  have hedge (i : h.CriticalEndpoint) : ∃ v : Vertex D.L (D.T : Subgroup G) D.H,
      v.type = false ∧ CosetGeometry.Incident (family D.L (D.T : Subgroup G) D.H)
        (base D.L (D.T : Subgroup G) D.H true) v ∧
      (ends i).V ≤ (edgeGroup D.L (D.T : Subgroup G) D.H
        (base D.L (D.T : Subgroup G) D.H true) v).pCoreIn 2 := by
    obtain ⟨w, hwt, hw, hew⟩ := i.edge_core hb
    have hf : ChapterF.Section09.Setup.Hypothesis.family (D := D) =
        sourceFamily D.L (D.T : Subgroup G) D.H := by
      funext b
      cases b <;> rfl
    rw [he]
    exact source_edge_witness D.L (D.T : Subgroup G) D.H (i.conjugate D.VH)
      hf w hwt hw hew
  exact {
    representative := fun i => i.representative
    opposite := opposite
    centered := hcenter
    opposite_centered := hcenter'
    normalizer_test := htest
    reverse_le := hrev
    commutator := hcomm
    neighbor := fun i => (hedge i).choose
    neighbor_type := fun i => (hedge i).choose_spec.1
    incident := fun i => (hedge i).choose_spec.2.1
    edge_core := fun i => (hedge i).choose_spec.2.2
    noncentral := hnoncentral
    selected := selected
    reversal := fun i _ => reversal i }

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
