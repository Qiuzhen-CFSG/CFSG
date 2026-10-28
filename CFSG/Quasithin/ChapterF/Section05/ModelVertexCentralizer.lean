module
public import CFSG.Quasithin.ChapterF.Section05.ModelVertexFlag
public import Theory.SpecificGroups.OmegaSixThree.EdgeCardinality
public import Theory.GroupTheory.CentralizerSmallKernelTransport
/-!
# The graph centralizer in a marked F.5 vertex

The literal native graph involution has centralizer of order1440, transported
through the checked vertex comparison. An actual source equivalence retaining
that graph mark gives the same order inside the original embedding range,
and consequently excludes a subgroup of order64 in this centralizer.
The source equivalence and its element marking remain explicit inputs.

Source: Aschbacher--Smith F.5.5--F.5.7, printed pp.301--303.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterF.Section05
open GreenBook.LieModels.UnitaryFour
open Theory.GroupTheory Theory.GroupTheory.CentralizerSmallKernelTransport
public noncomputable section
local notation "hn" => Nat.le_refl 1
local notation "X" => Extension.ProjectiveExtension 1 hn

theorem native_graph_centralizer_card :
    Nat.card (centralizer ({Extension.sigma 1 hn} : Set X))=1440 := by
  have he : markedModelUnitaryExtensionEquivVertex (Extension.sigma 1 hn) =
      OmegaSixThree.vertexGraphElement :=
    Subtype.ext (by simpa only [OmegaSixThree.vertexGraphElement_val] using
      markedModelUnitaryExtensionEquivVertex_sigma)
  rw [Nat.card_congr (centralizerEquiv markedModelUnitaryExtensionEquivVertex
    (Extension.sigma 1 hn)).toEquiv,he]
  exact OmegaSixThree.card_vertex_graph_centralizer

theorem marked_graph_centralizer_card {K : Type*} [Group K]
    (e : K ≃* X) (z : K) (hz : e z = Extension.sigma 1 hn) :
    Nat.card (centralizer ({z} : Set K))=1440 := by
  rw [Nat.card_congr (centralizerEquiv e z).toEquiv,hz]
  exact native_graph_centralizer_card

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

def sourceVertexGraphEquiv (hi : Function.Injective i) :
    centralizer ({c.middle UnitaryTwo.GraphCentralizer.graphInvolution} : Set G0) ≃*
      (centralizer ({Source.graphElement c i} : Set G)).subgroupOf i.range where
  toFun a := ⟨⟨i a.val,⟨a.val,rfl⟩⟩,
    mem_centralizer_singleton_iff.mpr (by
      change i a.val * i (c.middle UnitaryTwo.GraphCentralizer.graphInvolution) =
        i (c.middle UnitaryTwo.GraphCentralizer.graphInvolution) * i a.val
      simpa only [map_mul] using congrArg i (mem_centralizer_singleton_iff.mp a.property))⟩
  invFun b := ⟨(MonoidHom.ofInjective hi).symm b.val,by
    apply mem_centralizer_singleton_iff.mpr
    apply hi
    simp only [map_mul]
    have he : i ((MonoidHom.ofInjective hi).symm b.val) = b.val.val :=
      congrArg Subtype.val ((MonoidHom.ofInjective hi).apply_symm_apply b.val)
    rw [he]
    exact mem_centralizer_singleton_iff.mp b.property⟩
  left_inv a := Subtype.ext ((MonoidHom.ofInjective hi).symm_apply_apply a.val)
  right_inv b := by
    apply Subtype.ext
    exact (MonoidHom.ofInjective hi).apply_symm_apply b.val
  map_mul' a b := by
    apply Subtype.ext
    exact Subtype.ext (map_mul i a.val b.val)

theorem source_vertex_graph_centralizer_card (hi : Function.Injective i)
    (e : G0 ≃* X) (he : e (c.middle UnitaryTwo.GraphCentralizer.graphInvolution) = Extension.sigma 1 hn) :
    Nat.card ((centralizer ({Source.graphElement c i} : Set G)).subgroupOf i.range)=1440 :=
  (Nat.card_congr (sourceVertexGraphEquiv c i hi).symm.toEquiv).trans
    (marked_graph_centralizer_card e _ he)

theorem source_vertex_graph_centralizer_not_dvd64 (hi : Function.Injective i)
    (e : G0 ≃* X) (he : e (c.middle UnitaryTwo.GraphCentralizer.graphInvolution) = Extension.sigma 1 hn) :
    ¬64 ∣ Nat.card ((centralizer ({Source.graphElement c i} : Set G)).subgroupOf i.range) := by
  rw [source_vertex_graph_centralizer_card c i hi e he]
  decide
end
end CFSG.Quasithin.ChapterF.Section05
