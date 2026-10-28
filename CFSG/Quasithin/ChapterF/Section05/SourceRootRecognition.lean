module
public import CFSG.Quasithin.ChapterF.Section05.SourceVertexAlignment
public import CFSG.Quasithin.ChapterF.Section05.SourceLocalAgreement
public import CFSG.Quasithin.ChapterF.Section05.SourceResidualConjugation
public import CFSG.Quasithin.ChapterF.Section05.SourceAmalgamRecognition
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.EdgeResidual
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.EdgeGeneration

/-!
# F.5 ambient recognition from the actual centralizer witnesses

The source fixed-endpoint involutions give a vertex comparison through F.4.26.
Innerness of the plane automorphisms aligns the graph, core and complementary
S₄. The actual cyclic-four root corrects the local comparison. On the model
edge two-residual, both reversal actions are trivial; on the local intersection,
pointwise agreement gives conjugation. The local intersection has odd index15,
so those subgroups generate the full edge and prove its conjugation identity.
The existing model-amalgam endpoint then identifies the ambient group with PSL₄(3).

All model residual, local agreement and conjugation premises are discharged
here. Only the original F.5.5 source witnesses remain: the centralizer join,
cyclic root and fixed-endpoint involutions. Their source construction is separate.
Source: Aschbacher--Smith F.5.5 and F.5.7--8, printed pp.301--304.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05
open Subgroup Theory.GroupTheory GreenBook.LieModels.UnitaryFour
open ExceptionalLocal CompletionRecognition
open OmegaSixThree.OrthogonalityGraph (modelSystem)
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
  (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
  (hcentral : C c i = Rimage c i R ⊔ D c i)
  (r : G) (hr : r∈H c i) (hsq : r^2=Source.graphElement c i)
  (hc : ∀ a∈sourceLocalComplement c i,r*a=a*r)
  (hres : ∀ a∈(pResidual 2 (C c i)).map (C c i).subtype,r*a=a*r)

include h hR hcentral hr hsq hc hres

theorem source_ambient_of_marked_vertex_and_root
    (eV : modelSystem.vertexGroup ≃* i.range)
    (hgraph : (eV modelGraphElement : G)=Source.graphElement c i)
    (hcore : modelPlaneCoreInVertex.map (i.range.subtype.comp eV.toMonoidHom)=A c i true)
    (hcomp : modelComplementInVertex.map (i.range.subtype.comp eV.toMonoidHom)=sourceLocalComplement c i) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) := by
  obtain ⟨eH,hagree,_⟩ := source_local_agreement_of_commuting_root c i z h eV
    hgraph hcore R hR hcomp r hr hsq hc
  exact source_ambient_of_marked_local_conjugation c i z h R hR hcentral eV eH hagree
    (source_local_conjugation_of_residual c i eV hgraph eH hcomp hagree r hr hsq hc hres
      OmegaSixThree.TriangleLocal.edge_twoResidual_sup_local
      OmegaSixThree.TriangleLocal.edgeReversal_conj_twoResidual)

theorem source_ambient_of_fixed_endpoints_and_root
    (s t : G) (hs : s∈Dendpoint c i false) (ht : t∈Dendpoint c i true)
    (hsout : s∉Dendpoint c i false⊓Dendpoint c i true)
    (htout : t∉Dendpoint c i false⊓Dendpoint c i true)
    (hs2 : orderOf s=2) (ht2 : orderOf t=2) (hst : orderOf (s*t)=4) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) := by
  obtain ⟨eV,hgraph,hcore,hcomp⟩ :=
    exists_source_vertex_comparison_of_fixed_endpoints c i h.embedding_injective
      s t hs ht hsout htout hs2 ht2 hst
  exact source_ambient_of_marked_vertex_and_root c i z h R hR hcentral r hr hsq hc hres
    eV hgraph hcore hcomp

end CFSG.Quasithin.ChapterF.Section05
