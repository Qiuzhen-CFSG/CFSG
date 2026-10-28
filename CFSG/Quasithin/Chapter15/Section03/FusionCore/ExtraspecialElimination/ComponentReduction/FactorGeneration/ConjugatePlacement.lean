module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement.LocalFamily
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement.IntrinsicGeometry

/-!
# The selected conjugate in the component-generation argument

The source factorization identifies Y₀ with the L₁ of 15.3.48 and proves
H ∩ YT = Y₀T. The actual coset action then moves gamma2 to gamma0, carrying
the selected endpoint module into O₂(Y₀T) and its star image into
O₂(Y₀* T*). Its quadratic best-offender status and H-conjugate span are
preserved on the specified action on U_H/Z.

The theorem below still requires the original critical endpoint containment
of F.9.13(2). Its derivation from the genuine F.9 hypotheses belongs to the
unfinished F.9 geometry development. Thus this is a conditional assembly,
not a completed proof of the source placement step or of 15.3.49(i).
The final theorem applies at every eligible K, proves local-family and theta
inheritance, and reconstructs the action on U_K/Z from its kernel theorem at K.
Its endpoint and quadratic best-offender assertions are explicitly local to K.
IntrinsicGeometry retains the source cosets inside G₀ = ⟨YT,K⟩.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.13(2),
printed p.322, and 15.3.49 immediately after (h), printed p.1143.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement
variable {G : Type*} [Group G]

/-- Identify Y₀ with L₁ and construct the source conjugate, conditional on the still-required F.9.13 edge-core bound. -/
theorem exists_selected_endpoint_of_F913 [Finite G]
    (M Y Y0 H V ZS Z : Subgroup G) (T : Sylow 2 G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hYM : Y ≤ M) (hM : M ≤ normalizer (V : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hZV : Z ≤ V)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hHZ : H ≤ centralizer (Z : Set G))
    (hY0 : Y0 = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G)))
    (hYH : Y0 ⊔ (T : Subgroup G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ centralizer (Z : Set G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (g : G) (gamma2 : Vertex Y (T : Subgroup G) H)
    (ht : gamma2.type = false)
    (hadj : CosetGeometry.Incident (family Y (T : Subgroup G) H)
      (base Y (T : Subgroup G) H true) gamma2)
    (hcore : endpointModule V H g ≤
      (edgeGroup Y (T : Subgroup G) H (base Y (T : Subgroup G) H true) gamma2).pCoreIn 2)
    (hbest : IsBestOffender action.representation (starImage H (endpointModule V H g)))
    (hquad : IsQuadratic action.representation (starImage H (endpointModule V H g))) :
    ∃ h : H, (h : G)⁻¹ • gamma2 = base Y (T : Subgroup G) H false ∧
      ((h : G)⁻¹ * g) • base Y (T : Subgroup G) H true =
        (h : G)⁻¹ • (g • base Y (T : Subgroup G) H true) ∧
      endpointModule V H ((h : G)⁻¹ * g) = selectedConjugate H (endpointModule V H g) h⁻¹ ∧
      endpointModule V H ((h : G)⁻¹ * g) ≤ (Y0 ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      starImage H (endpointModule V H ((h : G)⁻¹ * g)) ≤
        (starImage H Y0 ⊔ starImage H (T : Subgroup G)).pCoreIn 2 ∧
      IsBestOffender action.representation (starImage H (endpointModule V H ((h : G)⁻¹ * g))) ∧
      IsQuadratic action.representation (starImage H (endpointModule V H ((h : G)⁻¹ * g))) ∧
      localSpan (endpointModule V H ((h : G)⁻¹ * g)) H = localSpan (endpointModule V H g) H := by
  have hL : CosetSetup.localL1 Y Z = Y0 :=
    (localL1_eq_Y0 M Y V Z T hYM hM hTM hZV hfactor).trans hY0.symm
  have hB := base_edge_eq_localL1 Y H Z T (le_sup_right.trans hYH) hHZ hTY
    (hL ▸ le_sup_left.trans hYH)
  rw [hL] at hB
  exact exists_selected_endpoint_of_edgeCore Y Y0 (T : Subgroup G) H V ZS Z action
    g gamma2 ht hadj hB hcore hbest hquad


/-- Construct the conjugate in the actual source geometry G₀, retaining the original F.9.13 obligation. -/
theorem exists_source_selected_endpoint_of_F913 [Finite G]
    (M Y Y0 H V ZS Z : Subgroup G) (T : Sylow 2 G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hYM : Y ≤ M) (hM : M ≤ normalizer (V : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hZV : Z ≤ V)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hHZ : H ≤ centralizer (Z : Set G))
    (hY0 : Y0 = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G)))
    (hYH : Y0 ⊔ (T : Subgroup G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ centralizer (Z : Set G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (g : geometryGroup Y (T : Subgroup G) H) (gamma2 : SourceVertex Y (T : Subgroup G) H)
    (ht : gamma2.type = false)
    (hadj : CosetGeometry.Incident (sourceFamily Y (T : Subgroup G) H)
      (sourceBase Y (T : Subgroup G) H true) gamma2)
    (hcore : endpointModule V H (g : G) ≤
      ((sourceEdgeGroup Y (T : Subgroup G) H (sourceBase Y (T : Subgroup G) H true) gamma2).pCoreIn 2).map
        (geometryGroup Y (T : Subgroup G) H).subtype)
    (hbest : IsBestOffender action.representation (starImage H (endpointModule V H (g : G))))
    (hquad : IsQuadratic action.representation (starImage H (endpointModule V H (g : G)))) :
    ∃ h : H, (sourceActor Y (T : Subgroup G) H h)⁻¹ • gamma2 = sourceBase Y (T : Subgroup G) H false ∧
      ((sourceActor Y (T : Subgroup G) H h)⁻¹ * g) • sourceBase Y (T : Subgroup G) H true =
        (sourceActor Y (T : Subgroup G) H h)⁻¹ • (g • sourceBase Y (T : Subgroup G) H true) ∧
      endpointModule V H ((h : G)⁻¹ * (g : G)) = selectedConjugate H (endpointModule V H (g : G)) h⁻¹ ∧
      endpointModule V H ((h : G)⁻¹ * (g : G)) ≤ (Y0 ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      starImage H (endpointModule V H ((h : G)⁻¹ * (g : G))) ≤
        (starImage H Y0 ⊔ starImage H (T : Subgroup G)).pCoreIn 2 ∧
      IsBestOffender action.representation (starImage H (endpointModule V H ((h : G)⁻¹ * (g : G)))) ∧
      IsQuadratic action.representation (starImage H (endpointModule V H ((h : G)⁻¹ * (g : G)))) ∧
      localSpan (endpointModule V H ((h : G)⁻¹ * (g : G))) H = localSpan (endpointModule V H (g : G)) H := by
  have hadj' := sourceEmbedding_incident Y (T : Subgroup G) H _ _ hadj
  rw [sourceEmbedding_base] at hadj'
  rw [source_edge_core_image, sourceEmbedding_base] at hcore
  obtain ⟨h, hmove, _, hm, hc, hs, hb, hq, hspan⟩ :=
    exists_selected_endpoint_of_F913 M Y Y0 H V ZS Z T action hYM hM hTM hZV hTY hHZ hY0 hYH
      hfactor g (sourceEmbedding Y (T : Subgroup G) H gamma2) ht hadj' hcore hbest hquad
  refine ⟨h, ?_, mul_smul _ _ _, hm, hc, hs, hb, hq, hspan⟩
  apply sourceEmbedding_injective Y (T : Subgroup G) H
  rw [sourceEmbedding_smul, sourceEmbedding_base]
  exact hmove

/-- Apply placement at each eligible K using its own reconstructed action and selected endpoint. No best-offender status is restricted from H. -/
theorem exists_source_selected_at_intermediate_of_F913 [Finite G]
    (M Y Y0 H K V ZS Z : Subgroup G) (T : Sylow 2 G)
    [IsElementaryAbelian 2 (localSpan V H)]
    (hYM : Y ≤ M) (hM : M ≤ normalizer (V : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hVT : V ≤ (T : Subgroup G))
    (hZ : Z ≤ ZS) (hZS : ZS ≤ V)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hHZ : H ≤ centralizer (Z : Set G))
    (hY0 : Y0 = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G)))
    (hQ : localTwoCore H ≠ ⊥) (hKH : K ≤ H)
    (hYK : Y0 ⊔ (T : Subgroup G) ≤ K) (hKM : ¬ K ≤ M)
    (hθ : theta (M ⊓ H) = Y0)
    (hfactor : ∀ x ∈ M ⊓ centralizer (Z : Set G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hkernel : letI := CosetSetup.layer_normal K Z (hKH.trans hHZ)
      CosetSetup.quotientCentralizer K (localSpan ZS K) Z = pCore 2 K)
    (g : geometryGroup Y (T : Subgroup G) K) (gamma2 : SourceVertex Y (T : Subgroup G) K)
    (ht : gamma2.type = false)
    (hadj : CosetGeometry.Incident (sourceFamily Y (T : Subgroup G) K)
      (sourceBase Y (T : Subgroup G) K true) gamma2)
    (hcore : endpointModule V K (g : G) ≤
      ((sourceEdgeGroup Y (T : Subgroup G) K (sourceBase Y (T : Subgroup G) K true) gamma2).pCoreIn 2).map
        (geometryGroup Y (T : Subgroup G) K).subtype)
    (hbest : letI := localSpan_elementary_of_le V ZS H K hZS hKH
      IsBestOffender (sectionActionAtIntermediate V ZS Z H K hZ hZS
        (hVT.trans (le_sup_right.trans hYK)) hKH hHZ hkernel).representation
        (starImage K (endpointModule V K (g : G))))
    (hquad : letI := localSpan_elementary_of_le V ZS H K hZS hKH
      IsQuadratic (sectionActionAtIntermediate V ZS Z H K hZ hZS
        (hVT.trans (le_sup_right.trans hYK)) hKH hHZ hkernel).representation
        (starImage K (endpointModule V K (g : G)))) :
    letI := localSpan_elementary_of_le V ZS H K hZS hKH
    let action := sectionActionAtIntermediate V ZS Z H K hZ hZS
      (hVT.trans (le_sup_right.trans hYK)) hKH hHZ hkernel
    K ∈ outsideFamily Y0 (T : Subgroup G) M ∧
      theta (M ⊓ K) = Y0 ∧ Y ⊓ centralizer (V : Set G) ≤ K ∧
      ∃ h : K, (sourceActor Y (T : Subgroup G) K h)⁻¹ • gamma2 = sourceBase Y (T : Subgroup G) K false ∧
        ((sourceActor Y (T : Subgroup G) K h)⁻¹ * g) • sourceBase Y (T : Subgroup G) K true =
          (sourceActor Y (T : Subgroup G) K h)⁻¹ • (g • sourceBase Y (T : Subgroup G) K true) ∧
        endpointModule V K ((h : G)⁻¹ * (g : G)) = selectedConjugate K (endpointModule V K (g : G)) h⁻¹ ∧
        endpointModule V K ((h : G)⁻¹ * (g : G)) ≤ (Y0 ⊔ (T : Subgroup G)).pCoreIn 2 ∧
        starImage K (endpointModule V K ((h : G)⁻¹ * (g : G))) ≤
          (starImage K Y0 ⊔ starImage K (T : Subgroup G)).pCoreIn 2 ∧
        IsBestOffender action.representation (starImage K (endpointModule V K ((h : G)⁻¹ * (g : G)))) ∧
        IsQuadratic action.representation (starImage K (endpointModule V K ((h : G)⁻¹ * (g : G)))) ∧
        localSpan (endpointModule V K ((h : G)⁻¹ * (g : G))) K = localSpan (endpointModule V K (g : G)) K := by
  let := localSpan_elementary_of_le V ZS H K hZS hKH
  let action := sectionActionAtIntermediate V ZS Z H K hZ hZS
    (hVT.trans (le_sup_right.trans hYK)) hKH hHZ hkernel
  have hd := intermediate_local_data M Y Y0 H K V ZS Z T hQ hKH hYK hKM hθ
    hTY (hTM.trans hM) hY0 hHZ hZS
  refine ⟨hd.1, hd.2.1, hd.2.2.1, ?_⟩
  exact exists_source_selected_endpoint_of_F913 M Y Y0 K V ZS Z T action hYM hM hTM
    (hZ.trans hZS) hTY (hKH.trans hHZ) hY0 hYK hfactor g gamma2 ht hadj hcore hbest hquad

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement
