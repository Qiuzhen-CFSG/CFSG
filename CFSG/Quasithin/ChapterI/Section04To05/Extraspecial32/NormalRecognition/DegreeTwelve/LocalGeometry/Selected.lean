module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Selected.Saturation
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Selected.Involution
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Selected.Alignment
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Saturated.LocalAction


/-!
# Assembly of the selected intersection and fused inverter

The source witness gives two conjugate extraspecial cores with elementary
intersection of order eight. Saturation would imply global normality of
the canonical fusion eight, by the full strong-closure and TI argument.
Thus nonnormality forces distinct eights. The conjugated fusion eight then
supplies an involution in the second core, centralizing z and outside Q.

The elementary-eight involution-action calculation closes the global-normality
argument. An outside involution can be conjugated inside H to invert the
original chosen Sylow three-subgroup. Applying that same left conjugation to
the selected core preserves every field of SelectedFusionData. The final
assembly discharges both local premises of the preserved conditional theorem.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 31–47, Lemmas 2.2–2.8 and 4.1.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve
open Subgroup Selected
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Assemble the literal selected configuration from the two independent local calculations. -/
public theorem nonempty_selectedFusionData_of_local_steps
    (h : Hypotheses z) (d : FusionEightData z) (hnon : ¬ (fusionCore z).Normal)
    (local_action : ∀ (g : G) (_b : NonnormalRecognition.IntersectionData z g) (j : G),
      j ∈ normalizer (NonnormalRecognition.coreIntersection z g : Set G) →
      orderOf j = 2 → j ∉ NonnormalRecognition.coreIntersection z g →
      Nat.card (NonnormalRecognition.centralizerIntersection z g j) = 4 ∧
        IsPGroup 2 ((normalizer (NonnormalRecognition.coreIntersection z g : Set G)).subgroupOf
          (Centralizer j)))
    (alignment : ∀ u : G, orderOf u = 2 → u ∈ Centralizer z → u ∉ coreInG z →
      IsConj z u → ∃ a : Centralizer z, ∀ x : h.X,
        ((a : G) * u * (a : G)⁻¹) * ((x : Centralizer z) : G) *
          ((a : G) * u * (a : G)⁻¹)⁻¹ = ((x : Centralizer z) : G)⁻¹) :
    Nonempty (SelectedFusionData h) := by
  obtain ⟨g, hgQ, hg⟩ := h.fused
  have hEF := intersection_ne_fusion_of_local_action h d hnon local_action g hgQ hg
  obtain ⟨a, ⟨u⟩⟩ := arrange_inverter_of_outside_alignment h d alignment g hgQ hg hEF
  obtain ⟨haQ, ha⟩ := conjugated_fusion_witness h a.property g hgQ hg
  exact ⟨{
    g := (a : G) * g
    fused_mem := haQ
    fused_ne := ha
    intersection_elementary := NonnormalRecognition.coreIntersection_elementary h _ ha
    intersection_card := NonnormalRecognition.coreIntersection_card h _ haQ ha
    intersection_ne_fusion := intersection_ne_fusion_of_conj h a.property g hEF
    u := u.u
    u_order := u.u_order
    u_centralizes := u.u_centralizes
    u_conjugate_core := u.u_conjugate_core
    u_not_core := u.u_not_core
    u_fused := u.u_fused
    u_inverts_X := u.u_inverts_X }⟩

/-- The selected intersection and marked fused inverter from the source inputs.
The quaternion-normal branch supplies the fusion-eight data; once those data
are given, both remaining local calculations hold without further premises. -/
public theorem nonempty_selectedFusionData
    (h : Hypotheses z) (_hn : QuaternionSubgroupsNormal z)
    (d : FusionEightData z) (hnon : ¬ (fusionCore z).Normal) :
    Nonempty (SelectedFusionData h) := by
  apply nonempty_selectedFusionData_of_local_steps h d hnon
  · intro g b j hj hj2 hjE
    exact NonnormalRecognition.centralizerIntersection_local_action b hj hj2 hjE
  · intro u hu huH huQ _
    exact outside_involution_alignment h u hu huH huQ

/-- The source four-group intersection in 4.1(1), applied to the exact selected core. -/
public theorem SelectedFusionData.intersection_fusion_card (h : Hypotheses z)
    (d : FusionEightData z) (a : SelectedFusionData h) :
    Nat.card (coreIntersection z a.g ⊓ fusionCore z : Subgroup G) = 4 :=
  Selected.intersection_fusion_card h d a.g a.fused_mem a.fused_ne a.intersection_ne_fusion

end CFSG.Quasithin.Extraspecial32.DegreeTwelve
