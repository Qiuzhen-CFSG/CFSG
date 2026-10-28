module
public import Theory.Representation.G2NaturalRootCentralizers

/-!
# Recovering the covering center from the full G₂ actor

The root-centralizer span misses the scalar radical in its commutator.
The whole Weyl cover has a different commutator: subtracting a long-root
displacement from a short-root displacement recovers every scalar vector.
Consequently its commutator with the full q³ actor is the full natural
three-space preimage. The natural hyperplane has field codimension one.

Transfer applies these calculations to the actual chosen cover; Normalization
uses the hyperplane bound and reciprocal roots to justify acting with all of V.
No vanishing of the covering center is asserted. Source: Aschbacher--Smith
B.4.6(3,7) and the central-cover repair in 11.2.2(5), printed pp.88,768.
The root coordinates are the existing attributed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment
open Atlas.G2 Atlas.G2.Natural Atlas.SplitOctonion Atlas.G2.Explicit
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

theorem scalar_le_full_commutator :
    (scalarLine F).restrictScalars (ZMod 2) ≤
      subspaceCommutator (RootCentralizers.coverAction F) ⊤ (EvenTwoRank.elementary F) := by
  intro x hx
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  let y : TraceZero F := ⟨![0,0,0,0,0,0,0,a],by simp [trace]⟩
  let z : TraceZero F := ⟨![0,0,0,0,0,0,a,0],by simp [trace]⟩
  have hm (b : Model F) (hb : b ∈ EvenTwoRank.elementary F) (v : TraceZero F) :
      RootCentralizers.coverAction F b v-v ∈
        subspaceCommutator (RootCentralizers.coverAction F) ⊤ (EvenTwoRank.elementary F) :=
    Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩
  have hC := hm (rootC 1) (NaturalOffenders.rootC_mem_elementary 1) y
  have hA := hm (rootA 1) (NaturalOffenders.rootA_mem_elementary 1) z
  have he : (RootCentralizers.coverAction F (rootC 1) y-y) -
      (RootCentralizers.coverAction F (rootA 1) z-z) = a • identity F := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [RootCentralizers.coverAction,restrictScalars,traceZeroAction_val,
      rootC,rootCEquiv,rootCLinear,rootCApply,rootA,rootAEquiv,rootALinear,rootAApply,
      y,z,identity,unit,CharTwo.neg_eq]
  exact he ▸ Submodule.sub_mem _ hC hA

theorem full_commutator_eq_threePreimage :
    subspaceCommutator (RootCentralizers.coverAction F) ⊤ (EvenTwoRank.elementary F) =
      RootCentralizers.threePreimage F := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,x,-,rfl⟩
    obtain ⟨p,rfl⟩ := hb
    change _ ∈ RootCentralizers.threePreimage F
    change _ ∧ _ ∧ _
    simp [EvenTwoRank.elementaryEmbedding,EvenTwoRank.elementaryParameters,
      unipotentProduct,RootCentralizers.coverAction,restrictScalars,traceZeroAction_val,
      Restricted.NaturalCoordinates.projection,rootA,rootB,rootC,rootAEquiv,rootBEquiv,rootCEquiv,rootALinear,rootBLinear,
      rootCLinear,rootAApply,rootBApply,rootCApply]
  · rw [RootCentralizers.threePreimage_eq_sup]
    apply sup_le
    · rw [←RootCentralizers.commutator_eq_threeLift]
      apply Submodule.span_mono
      rintro _ ⟨b,hb,x,hx,rfl⟩
      exact ⟨b,hb,x,Submodule.mem_top,rfl⟩
    · exact scalar_le_full_commutator F

/-- The natural hyperplane spanned by the two coordinate root fixed spaces. -/
def naturalHyperplane : Submodule F (Natural.Space F) :=
  LinearMap.ker ((LinearMap.proj (5 : Fin 6)).comp
    (Restricted.NaturalCoordinates.coordinates F))

omit [Algebra (ZMod 2) F] in
theorem naturalHyperplane_codim : Module.finrank F (Natural.Space F ⧸ naturalHyperplane F) = 1 := by
  let f := (LinearMap.proj (5 : Fin 6)).comp (Restricted.NaturalCoordinates.coordinates F)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨v,hv⟩ := (Restricted.NaturalCoordinates.equiv F).surjective (Pi.single 5 a)
    refine ⟨v,?_⟩
    change Restricted.NaturalCoordinates.coordinates F v 5 = a
    rw [show Restricted.NaturalCoordinates.coordinates F v = Pi.single 5 a from hv]
    simp
  change Module.finrank F (Natural.Space F ⧸ f.ker) = 1
  rw [(LinearMap.quotKerEquivOfSurjective f hf).finrank_eq]
  exact Module.finrank_self F

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment
