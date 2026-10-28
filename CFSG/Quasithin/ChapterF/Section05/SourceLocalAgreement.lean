module
public import CFSG.Quasithin.ChapterF.Section05.SourceLocalComparisonOriented
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.ModelVertexProperness
public import CFSG.Quasithin.ChapterF.Section05.ModelVertexCoreTransport
public import CFSG.Quasithin.ChapterF.Section05.LocalCompatibilityCyclic
-- Intentional internal split: the restriction proof unfolds only the two
-- vertex-subgroup definitions provided by ModelVertexCoreTransport.
import all CFSG.Quasithin.ChapterF.Section05.ModelVertexCoreTransport
/-!
# Actual source vertex restriction and local-map agreement

A vertex comparison carrying the literal model core to A₂ sends the model
intersection into H=N_G(A₂), by normality of that core. The model intersection
and source intersection both have order192; the injective restriction is
therefore an isomorphism, retaining the original vertex map pointwise.

The graph mark supplies source H properness and orients the preliminary local
comparison. The original cyclic-four root, centralizing the marked independent
S₄, then removes the central sign twist through LocalCompatibilityCyclic.
The resulting local map agrees with the original vertex map on every element
of their model intersection. Only the genuine marked vertex and cyclic-root
inputs remain explicit for the F.5 source assembly.

Source: Aschbacher--Smith F.5.5 and F.5.7, printed pp.301–303.
-/
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour ExceptionalLocal
open OmegaSixThree.OrthogonalityGraph (modelSystem)
open OmegaSixThree.TriangleLocal (vertexLocal localCore)
local notation "hn" => Nat.le_refl 1
local notation "O" => OmegaSixThree.omegaPlusSixThree
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (eV : modelSystem.vertexGroup ≃* i.range)
  (hgraph : (eV modelGraphElement : G)=Source.graphElement c i)
  (hcore : modelPlaneCoreInVertex.map (i.range.subtype.comp eV.toMonoidHom)=A c i true)

include hcore in
private theorem vertex_image_mem_H (g : vertexLocal) :
    (eV ⟨g.val.val,g.property⟩ : G)∈H c i := by
  let j : modelSystem.vertexGroup →* G := i.range.subtype.comp eV.toMonoidHom
  change j ⟨g.val.val,g.property⟩∈normalizer (A c i true:Set G)
  apply mem_normalizer_fintype
  intro a ha
  rw [←hcore] at ha ⊢
  obtain ⟨b,hb,rfl⟩ := ha
  change b.val∈localCore.map OmegaSixThree.TriangleLocal.H.subtype at hb
  obtain ⟨u,hu,hub⟩ := hb
  let v : modelSystem.vertexGroup := ⟨g.val.val,g.property⟩
  refine ⟨v*b*v⁻¹,?_,?_⟩
  · change (v*b*v⁻¹).val∈localCore.map OmegaSixThree.TriangleLocal.H.subtype
    refine ⟨g.val*u*g.val⁻¹,(inferInstance : localCore.Normal).conj_mem u hu g.val,?_⟩
    change g.val.val*u.val*g.val.val⁻¹=g.val.val*b.val*g.val.val⁻¹
    change u.val=b.val at hub
    rw [hub]
  · simp only [map_mul,map_inv]
    rfl

private def sourceVertexLocalHom : vertexLocal →* i.range.subgroupOf (H c i) where
  toFun g := ⟨⟨(eV ⟨g.val.val,g.property⟩:G),vertex_image_mem_H c i eV hcore g⟩,
    (eV ⟨g.val.val,g.property⟩).property⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change (eV 1:G)=1
    exact congrArg (fun x:i.range => (x:G)) eV.map_one
  map_mul' g k := by
    apply Subtype.ext
    apply Subtype.ext
    change (eV (⟨g.val.val,g.property⟩*⟨k.val.val,k.property⟩):G)=
      (eV ⟨g.val.val,g.property⟩:G)*(eV ⟨k.val.val,k.property⟩:G)
    exact congrArg (fun x:i.range => (x:G)) (eV.map_mul ⟨g.val.val,g.property⟩ ⟨k.val.val,k.property⟩)

private theorem sourceVertexLocalHom_injective : Function.Injective (sourceVertexLocalHom c i eV hcore) := by
  intro a b hab
  have hv : eV ⟨a.val.val,a.property⟩=eV ⟨b.val.val,b.property⟩ :=
    Subtype.ext (congrArg (fun x:i.range.subgroupOf (H c i)=>(x.val:G)) hab)
  have hv' := congrArg Subtype.val (eV.injective hv)
  exact Subtype.ext (Subtype.ext hv')

include h hgraph in
private theorem source_vertex_intersection_card (R : Sylow 2 (C c i))
    (hR : Tf c i≤(R:Subgroup (C c i))) : Nat.card (i.range.subgroupOf (H c i))=192 := by
  have hi := source_H_vertex_index c i z h (source_H_not_le_vertex c i z h eV hgraph R hR)
  have hc := (i.range.subgroupOf (H c i)).card_mul_index
  rw [hi,source_H_card c i z h] at hc
  omega

/-- Restrict the actual graph/core-marked vertex comparison to the literal
local intersection. Equal order192 proves that the restriction is onto. -/
noncomputable def sourceVertexLocalRestriction (R : Sylow 2 (C c i))
    (hR : Tf c i≤(R:Subgroup (C c i))) : vertexLocal ≃* i.range.subgroupOf (H c i) :=
  MulEquiv.ofBijective (sourceVertexLocalHom c i eV hcore)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨sourceVertexLocalHom_injective c i eV hcore,
        (OmegaSixThree.TriangleLocal.vertexLocal_card).trans
          (source_vertex_intersection_card c i z h eV hgraph R hR).symm⟩)

/-- The restriction retains the actual vertex map, including both ambient
subgroup inclusions. -/
theorem sourceVertexLocalRestriction_val (R : Sylow 2 (C c i))
    (hR : Tf c i≤(R:Subgroup (C c i))) (g : vertexLocal) :
    (((sourceVertexLocalRestriction c i z h eV hgraph hcore R hR g).val):G)=
      (eV ⟨g.val.val,g.property⟩:G) := by
  unfold sourceVertexLocalRestriction
  rfl

include h hgraph hcore in
/-- Correct the source local comparison using the actual cyclic root. The
conclusion is the pointwise agreement consumed by SourceAmalgamRecognition. -/
theorem source_local_agreement_of_commuting_root (R : Sylow 2 (C c i))
    (hR : Tf c i≤(R:Subgroup (C c i)))
    (hcomp : modelComplementInVertex.map (i.range.subtype.comp eV.toMonoidHom)=
      sourceLocalComplement c i)
    (r : G) (hr : r∈H c i) (hsq : r^2=Source.graphElement c i)
    (hc : ∀ a∈sourceLocalComplement c i,r*a=a*r) :
    ∃ eH : modelSystem.H ≃* H c i,
      (∀ (g : O) (hgH : g∈modelSystem.H) (hgv : g∈modelSystem.vertexGroup),
        (eV ⟨g,hgv⟩:G)=(eH ⟨g,hgH⟩:G)) ∧
      (∀ g:modelSystem.H,(eH g:G)∈i.range ↔ g∈vertexLocal) := by
  have hp := source_H_not_le_vertex c i z h eV hgraph R hR
  obtain ⟨e,_,he⟩ := exists_sourceMarkedLocalComparison c i z h hp
  let rho := sourceMarkedLocalComparison c i e
  have hrho (g:modelSystem.H) : (rho g:G)∈i.range ↔ g∈vertexLocal := (he g).symm
  let s := sourceVertexLocalRestriction c i z h eV hgraph hcore R hR
  apply model_local_agreement_of_commuting_root i.range (H c i) eV rho hrho s
    (sourceVertexLocalRestriction_val c i z h eV hgraph hcore R hR) r hr
  · exact hsq.trans hgraph.symm
  · intro g hg
    rw [sourceVertexLocalRestriction_val]
    apply hc
    rw [←hcomp]
    refine ⟨⟨g.val.val,g.property⟩,?_,rfl⟩
    change g.val.val∈OmegaSixThree.TriangleLocal.complementFactor.map OmegaSixThree.TriangleLocal.H.subtype
    exact ⟨g.val,hg,rfl⟩
end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
