module
public import CFSG.Quasithin.ChapterF.Section05.ModelRootUniqueness
public import CFSG.Quasithin.ChapterF.Section05.ModelVertexCoreTransport
public import Theory.GroupTheory.GraphUniquenessSystem.ResidualConjugation
-- Intentional internal split: unfold the literal model complement subgroup
-- to transport its membership through the original marked vertex map.
import all CFSG.Quasithin.ChapterF.Section05.ModelVertexCoreTransport

/-!
# Source edge conjugation from the actual graph-centralizer residual

The graph-marked vertex map sends the model edge into the original graph
centralizer. Functoriality sends its two-residual into the embedded source
two-residual. A source cyclic-four root centralizes that image. Its graph
square and centralization of the independent complement identify the local
reversal image up to inversion, preserving residual centralization.

The generic residual-and-local generation lemma then gives the complete edge
conjugation identity required by SourceAmalgamRecognition. The two model
residual facts remain explicit inputs from their independent producer.
Source: Aschbacher--Smith F.5.5 and F.5.7, printed pp.301--303.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
open Subgroup Theory.GroupTheory Theory.GroupTheory.GraphUniquenessSystem
open GreenBook.LieModels.UnitaryFour ExceptionalLocal
open OmegaSixThree.OrthogonalityGraph
open OmegaSixThree.TriangleLocal (vertexLocal complementFactor)
local notation "hn" => Nat.le_refl 1
local notation "O" => OmegaSixThree.omegaPlusSixThree
variable {G G0 : Type*} [Group G] [Group G0]
  (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (eV : modelSystem.vertexGroup ≃* i.range)
  (hgraph : (eV modelGraphElement : G)=Source.graphElement c i)

private def modelEdgeToSourceCentralizer : modelSystem.edgeGroup →* C c i :=
  ((i.range.subtype.comp eV.toMonoidHom).comp
    (Subgroup.inclusion (show modelSystem.edgeGroup≤modelSystem.vertexGroup from inf_le_left))).codRestrict
    (C c i) (fun b => mem_centralizer_singleton_iff.mpr
      ((modelEdge_iff_image_commutes i.range eV (Source.graphElement c i) hgraph
        ⟨b,b.property.1⟩).mp b.property))

include hgraph

/-- The actual marked vertex map sends the model edge residual into the
embedded two-residual of the original source graph centralizer. -/
theorem source_model_edge_residual_image (b : modelSystem.edgeGroup)
    (hb : b∈pResidual 2 modelSystem.edgeGroup) :
    (eV ⟨b,b.property.1⟩ : G) ∈ (pResidual 2 (C c i)).map (C c i).subtype := by
  let f := modelEdgeToSourceCentralizer c i eV hgraph
  exact ⟨f b,map_pResidual_le 2 f (mem_map_of_mem f hb),rfl⟩

/-- Full edge conjugation follows from the actual source graph/complement
marks, the source root's residual centralization, and the model residual
supplement and centralization facts. -/
theorem source_local_conjugation_of_residual
    (eH : modelSystem.H ≃* H c i)
    (hcomp : modelComplementInVertex.map (i.range.subtype.comp eV.toMonoidHom)=
      sourceLocalComplement c i)
    (hagree : ∀ (g : O) (hgH : g∈modelSystem.H) (hgv : g∈modelSystem.vertexGroup),
      (eV ⟨g,hgv⟩:G)=(eH ⟨g,hgH⟩:G))
    (r : G) (hr : r∈H c i) (hsq : r^2=Source.graphElement c i)
    (hc : ∀ a∈sourceLocalComplement c i,r*a=a*r)
    (hres : ∀ a∈(pResidual 2 (C c i)).map (C c i).subtype,r*a=a*r)
    (gen : pResidual 2 modelSystem.edgeGroup ⊔
      modelSystem.H.subgroupOf modelSystem.edgeGroup=⊤)
    (hmodel : ∀ b:modelSystem.edgeGroup,b∈pResidual 2 modelSystem.edgeGroup →
      (modelEdgeReversal:O)*b*(modelEdgeReversal:O)⁻¹=b) :
    ∀ b:modelSystem.edgeGroup,
      (eV ⟨(modelEdgeReversal:O)*b*(modelEdgeReversal:O)⁻¹,
        (modelSystem.conj_mem_edgeGroup modelEdgeReversal_first
          modelEdgeReversal_second b.property).1⟩:G)=
      (eH modelEdgeReversal:G)*(eV ⟨b,b.property.1⟩:G)*(eH modelEdgeReversal:G)⁻¹ := by
  have hcomp' : ∀ g:vertexLocal,g.val∈complementFactor →
      r*(eV ⟨g.val.val,g.property⟩:G)=(eV ⟨g.val.val,g.property⟩:G)*r := by
    intro g hg
    apply hc
    rw [←hcomp]
    refine ⟨⟨g.val.val,g.property⟩,?_,rfl⟩
    change g.val.val∈complementFactor.map OmegaSixThree.TriangleLocal.H.subtype
    exact ⟨g.val,hg,rfl⟩
  have ht := agreeing_local_reversal_image_eq_root_or_inv i.range (H c i) eV eH
    hagree ⟨r,hr⟩ (hsq.trans hgraph.symm) hcomp'
  let v : modelSystem.vertexGroup →* G := i.range.subtype.comp eV.toMonoidHom
  let l : modelSystem.H →* G := (H c i).subtype.comp eH.toMonoidHom
  apply modelSystem.conjugation_of_residual_and_local v l hagree modelEdgeReversal
    modelEdgeReversal_first modelEdgeReversal_second gen hmodel
  intro b hb
  have hh : r*(eV ⟨b,b.property.1⟩:G)=(eV ⟨b,b.property.1⟩:G)*r :=
    hres _ (source_model_edge_residual_image c i eV hgraph b hb)
  change (eH modelEdgeReversal:G)*(eV ⟨b,b.property.1⟩:G)=
    (eV ⟨b,b.property.1⟩:G)*(eH modelEdgeReversal:G)
  rcases ht with ht | ht
  · simpa only [ht] using hh
  · simpa only [ht,Subgroup.coe_inv] using (show Commute r (eV ⟨b,b.property.1⟩:G) from hh).inv_left.eq

end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
