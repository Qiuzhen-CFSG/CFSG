module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerProduct
public import CFSG.Quasithin.ChapterF.Section05.ModelLocal
/-!
# A concrete local comparison for the original F.5 source

The model triangle stabilizer and the original source normalizer are both
identified with S₄×S₄. Composing the proved maps gives the literal local
isomorphism required by the source-system construction. Its two-core map is
exactly A₂. The final vertex-membership lemma records precisely the remaining
source coordinate marking needed by the similarity assembly.

Source: Aschbacher--Smith F.5.7(2), printed p.303. Agreement with the separate
vertex comparison is not inferred from the abstract group isomorphisms.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour ExceptionalLocal
open OmegaSixThree.OrthogonalityGraph (modelSystem)
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)

def sourceLocalComparison : modelSystem.H ≃* H c i :=
  modelLocalEquiv.trans (sourceHEquiv c i z h).symm

theorem sourceLocalComparison_core :
    (pCore 2 modelSystem.H).map (sourceLocalComparison c i z h).toMonoidHom =
      (A c i true).subgroupOf (H c i) := by
  rw [pCore_map_iso,source_H_twoCore c i z h]

theorem sourceLocalComparison_mem_A (g : modelSystem.H) :
    g∈pCore 2 modelSystem.H ↔ (sourceLocalComparison c i z h g : G)∈A c i true := by
  rw [←show (sourceLocalComparison c i z h g)∈(A c i true).subgroupOf (H c i) ↔
      (sourceLocalComparison c i z h g:G)∈A c i true from Iff.rfl]
  rw [←sourceLocalComparison_core c i z h]
  exact (mem_map_iff_mem (sourceLocalComparison c i z h).injective).symm

/-- The exact remaining source vertex mark converts this concrete local
comparison into the local-vertex field required by the source similarity. -/
theorem sourceLocalComparison_vertex
    (hv : ∀ a:H c i, (a:G)∈i.range ↔
      (sourceHEquiv c i z h a).1∈OmegaSixThree.TriangleLocal.square)
    (g : modelSystem.H) :
    (g:OmegaSixThree.omegaPlusSixThree)∈modelSystem.vertexGroup ↔
      (sourceLocalComparison c i z h g:G)∈i.range := by
  rw [modelLocal_vertex_iff,hv]
  change (modelLocalEquiv g).1∈_ ↔
    (sourceHEquiv c i z h ((sourceHEquiv c i z h).symm (modelLocalEquiv g))).1∈_
  rw [MulEquiv.apply_symm_apply]
end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
