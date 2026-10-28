module
public import Theory.GroupTheory.SubgroupEmbeddingAlignment
public import CFSG.Quasithin.ChapterF.Section05.ModelVertexCoreTransport
public import CFSG.Quasithin.ChapterF.Section05.ModelEdge
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.SourceSmallRecognition
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ExtendedAffinePlaneAutomorphism

/-!
# Aligning the actual F.5 vertex through its plane endpoint

The F.5.5 comparison initially preserves the endpoint ranges. Every
automorphism of the extended plane E16:S5 is inner, so an ambient inner
adjustment makes its plane restriction agree pointwise with the original
faithful completion. The graph element, A2 and the independent corrected S4
all lie in that plane. The existing literal model maps therefore supply
their three exact markings without a full amalgam-automorphism theorem.

The final consumer retains only the original fixed-endpoint involutions
whose order-four product gives F.4.26. Their construction belongs to F.5.5.
Source: Aschbacher--Smith F.5.5(4) and F.5.7(1), printed pp.302--303.
-/

public noncomputable section
open Subgroup

namespace CFSG.Quasithin.ChapterF.Section05
open Theory.GroupTheory GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0]
  (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

theorem source_plane_aligned_of_range
    (e : G0 ≃* Extension.ProjectiveExtension 1 hn)
    (he : c.right.range.map e.toMonoidHom = Extension.plane 1 hn) :
    ∃ f : G0 ≃* Extension.ProjectiveExtension 1 hn,
      ∀ x : Extension.plane 1 hn, f (c.right x) = x :=
  Subgroup.exists_aligned_equiv_of_inner_automorphisms _ c.right c.right_injective e he UnitaryTwo.ExtendedAffinePlane.exists_conj

open OmegaSixThree.OrthogonalityGraph (modelSystem)
open CompletionRecognition ExceptionalLocal

@[expose] def sourceVertexComparison (hi : Function.Injective i)
    (e : G0 ≃* Extension.ProjectiveExtension 1 hn) :
    modelSystem.vertexGroup ≃* i.range :=
  markedModelUnitaryExtensionEquivVertex.symm.trans
    (e.symm.trans (MonoidHom.ofInjective hi))

private theorem inverse_plane_agreement
    (e : G0 ≃* Extension.ProjectiveExtension 1 hn)
    (he : ∀ a : Extension.plane 1 hn, e (c.right a) = a) :
    ∀ a : Extension.plane 1 hn, (i.comp e.symm.toMonoidHom) a.val = i (c.right a) := by
  intro a
  change i (e.symm a.val) = i (c.right a)
  exact congrArg i ((congrArg e.symm (he a)).symm.trans (e.symm_apply_apply _))

theorem sourceVertexComparison_graph (hi : Function.Injective i)
    (e : G0 ≃* Extension.ProjectiveExtension 1 hn)
    (he : ∀ a : Extension.plane 1 hn, e (c.right a) = a) :
    (sourceVertexComparison i hi e modelGraphElement : G) = Source.graphElement c i := by
  have hm : markedModelUnitaryExtensionEquivVertex (Extension.sigma 1 hn) =
      modelGraphElement := Subtype.ext markedModelUnitaryExtensionEquivVertex_sigma
  change i (e.symm (markedModelUnitaryExtensionEquivVertex.symm modelGraphElement)) = _
  rw [←hm,markedModelUnitaryExtensionEquivVertex.symm_apply_apply]
  exact (inverse_plane_agreement c i e he (modelGraph true)).trans
    (endpointMap_graph c i true)

theorem sourceVertexComparison_core (hi : Function.Injective i)
    (e : G0 ≃* Extension.ProjectiveExtension 1 hn)
    (he : ∀ a : Extension.plane 1 hn, e (c.right a) = a) :
    modelPlaneCoreInVertex.map
      (i.range.subtype.comp (sourceVertexComparison i hi e).toMonoidHom) = A c i true := by
  exact (source_plane_core_model_image c i hi (i.comp e.symm.toMonoidHom)
    (inverse_plane_agreement c i e he) (hi.comp e.symm.injective)).symm

theorem sourceVertexComparison_complement (hi : Function.Injective i)
    (e : G0 ≃* Extension.ProjectiveExtension 1 hn)
    (he : ∀ a : Extension.plane 1 hn, e (c.right a) = a) :
    modelComplementInVertex.map
      (i.range.subtype.comp (sourceVertexComparison i hi e).toMonoidHom) = sourceLocalComplement c i := by
  exact (source_complement_model_image c i (i.comp e.symm.toMonoidHom)
    (inverse_plane_agreement c i e he)).symm

theorem exists_source_vertex_comparison_of_plane_range
    (hi : Function.Injective i)
    (e : G0 ≃* Extension.ProjectiveExtension 1 hn)
    (he : c.right.range.map e.toMonoidHom = Extension.plane 1 hn) :
    ∃ eV : modelSystem.vertexGroup ≃* i.range,
      (eV modelGraphElement : G) = Source.graphElement c i ∧
      modelPlaneCoreInVertex.map (i.range.subtype.comp eV.toMonoidHom) = A c i true ∧
      modelComplementInVertex.map (i.range.subtype.comp eV.toMonoidHom) = sourceLocalComplement c i := by
  obtain ⟨f,hf⟩ := source_plane_aligned_of_range c e he
  exact ⟨sourceVertexComparison i hi f, sourceVertexComparison_graph c i hi f hf,
    sourceVertexComparison_core c i hi f hf, sourceVertexComparison_complement c i hi f hf⟩

variable [Finite G]

theorem exists_source_vertex_comparison_of_fixed_endpoints
    (hi : Function.Injective i)
    (s t : G) (hs : s∈Dendpoint c i false) (ht : t∈Dendpoint c i true)
    (hsout : s∉Dendpoint c i false⊓Dendpoint c i true)
    (htout : t∉Dendpoint c i false⊓Dendpoint c i true)
    (hs2 : orderOf s=2) (ht2 : orderOf t=2) (hst : orderOf (s*t)=4) :
    ∃ eV : modelSystem.vertexGroup ≃* i.range,
      (eV modelGraphElement : G) = Source.graphElement c i ∧
      modelPlaneCoreInVertex.map (i.range.subtype.comp eV.toMonoidHom) = A c i true ∧
      modelComplementInVertex.map (i.range.subtype.comp eV.toMonoidHom) = sourceLocalComplement c i := by
  obtain ⟨e,_,he⟩ := source_parabolic_preserving_equiv_of_fixed_endpoints c i hi
    s t hs ht hsout htout hs2 ht2 hst
  exact exists_source_vertex_comparison_of_plane_range c i hi e he

end CFSG.Quasithin.ChapterF.Section05
