module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Edges.Bitplanes
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Edges.Factors

/-!
# Assembly of the Fi23 forward-edge certificate

The published representatives have 63342 forward edges. Literal tree prefixes
and the certified A²/B³ relations reduce their membership to the two residual
families defined in `Edges.Reduction`. This module consumes both families
with the original eight-generator witness group and exact inclusion map.
The residual memberships remain explicit until their certificates are proved;
this is not yet `edge_mem_witnessGroup_of_source_maps`.

Source: ATLAS F23G1-p31671B0 and GLS3 Table 5.3u. The final consumer is
`centralizer_le_witnessGroup_of_edges_and_separation` in `Exhaustion.lean`.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion
open Fi24Prime.Fi23Lift.Certificate Edges

/-- Assemble all 63342 edges from the two strictly smaller residual families.
The two numerical membership premises are still proof obligations. -/
theorem edge_mem_witnessGroup_of_residual_certificates
    (hA : ∀ x, generatorA x = sourceA x) (hB : ∀ x, generatorB x = sourceB x)
    (hresA : ∀ x, ResidualA x → inclusion (edge false x) ∈ witnessGroup)
    (hresB : ∀ x, ResidualB x → inclusion (edge true x) ∈ witnessGroup) :
    ∀ (b : Bool) (x : Fin 31671), inclusion (edge b x) ∈ witnessGroup := by
  intro b x
  cases b
  · exact edge_false_mem_of_residual hA hB hresA x
  · exact edge_true_mem_of_residual hA hB hresB x

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion
