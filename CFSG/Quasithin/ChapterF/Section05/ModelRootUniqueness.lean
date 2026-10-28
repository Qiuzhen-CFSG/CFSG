module
public import CFSG.Quasithin.ChapterF.Section05.ModelEdge
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.RootUniqueness

/-!
# Identifying the corrected local map's edge reversal

The graph square and centralization of the actual complementary S₄ identify
an order-four root up to inversion. Pointwise agreement with the vertex map
transports those two marks to the corrected local map. Both choices induce
the same conjugation on the full edge group because their square centralizes
that group. This removes the choice of generator in the F.5.7 amalgam map;
the source conjugation action itself remains a separate input.
Source: Aschbacher--Smith F.5.5 and F.5.7, printed pp.301--303.
-/

public section

namespace CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
open OmegaSixThree OrthogonalityGraph TriangleLocal
local notation "Model" => omegaPlusSixThree

/-- A marked local map sends the fixed reversal to either generator of the
source cyclic-four group, retaining the actual complement embedding. -/
theorem model_reversal_image_eq_root_or_inv {K : Type*} [Group K]
    (eH : modelSystem.H ≃* K) (r : K)
    (hsq : eH graphElement = r^2)
    (hc : ∀ g : modelSystem.H, g ∈ complementFactor → r * eH g = eH g * r) :
    eH modelEdgeReversal = r ∨ eH modelEdgeReversal = r⁻¹ := by
  let e : H ≃* K := eH
  change e edgeReversal = r ∨ e edgeReversal = r⁻¹
  have hsq' : (e.symm r)^2 = graphElement := by
    apply e.injective
    rw [map_pow,e.apply_symm_apply]
    exact hsq.symm
  have hc' (g : H) (hg : g ∈ complementFactor) :
      e.symm r * g = g * e.symm r := by
    apply e.injective
    rw [map_mul,map_mul,e.apply_symm_apply]
    exact hc g hg
  rcases graph_root_eq_reversal_or_inv (e.symm r) hsq' hc' with ht | ht
  · exact Or.inl (by simpa only [e.apply_symm_apply] using (congrArg e ht).symm)
  · right
    have hh : r = (e edgeReversal)⁻¹ := by
      simpa only [e.apply_symm_apply,map_inv] using congrArg e ht
    simpa only [inv_inv] using (congrArg Inv.inv hh).symm

variable {G : Type*} [Group G] (M J : Subgroup G)
  (eV : modelSystem.vertexGroup ≃* M) (eH : modelSystem.H ≃* J)
  (hagree : ∀ (g : Model) (hgH : g ∈ modelSystem.H) (hgV : g ∈ modelSystem.vertexGroup),
    (eV ⟨g,hgV⟩ : G) = (eH ⟨g,hgH⟩ : G))
  (r : J) (hsq : (r : G)^2 = (eV modelGraphElement : G))
  (hc : ∀ g : vertexLocal, g.val ∈ complementFactor →
    (r : G) * (eV ⟨g.val.val,g.property⟩ : G) =
      (eV ⟨g.val.val,g.property⟩ : G) * (r : G))

include hagree hsq hc
/-- Pointwise agreement with the original vertex map supplies the graph and
complement marks needed to identify the corrected local map's reversal. -/
theorem agreeing_local_reversal_image_eq_root_or_inv :
    eH modelEdgeReversal = r ∨ eH modelEdgeReversal = r⁻¹ := by
  apply model_reversal_image_eq_root_or_inv eH r
  · apply Subtype.ext
    change (eH graphElement : G) = (r : G)^2
    rw [hsq]
    exact (hagree vertexGraphInvolution graph_mem modelGraphElement.property).symm
  · intro g hg
    apply Subtype.ext
    let v : vertexLocal := ⟨g,complementFactor_le_vertexLocal hg⟩
    have hh := hc v hg
    rw [hagree g.val g.property v.property] at hh
    exact hh

omit hagree hsq hc in
private theorem inverse_conjugation_of_square_commutes (r x : G)
    (hc : r^2*x=x*r^2) : r⁻¹*x*r = r*x*r⁻¹ := by
  calc
    r⁻¹*x*r = r⁻¹*(x*r^2)*r⁻¹ := by group
    _ = r⁻¹*(r^2*x)*r⁻¹ := by rw [hc]
    _ = r*x*r⁻¹ := by group

/-- The inverse choice produces the same conjugation on every full edge-fixer
element, because the root square is the marked graph involution. -/
theorem agreeing_local_reversal_conjugation (b : modelSystem.edgeGroup) :
    (eH modelEdgeReversal : G) * (eV ⟨b,b.property.1⟩ : G) *
        (eH modelEdgeReversal : G)⁻¹ =
      (r : G) * (eV ⟨b,b.property.1⟩ : G) * (r : G)⁻¹ := by
  rcases agreeing_local_reversal_image_eq_root_or_inv M J eV eH hagree r hsq hc with ht | ht
  · rw [ht]
  · rw [ht]
    simp only [Subgroup.coe_inv,inv_inv]
    apply inverse_conjugation_of_square_commutes
    rw [hsq]
    have hh := (modelEdge_iff_commutes ⟨b,b.property.1⟩).mp b.property
    have hh' := congrArg (fun a : modelSystem.vertexGroup => (eV a : G)) hh
    simpa only [map_mul,Subgroup.coe_mul] using hh'.symm

end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
