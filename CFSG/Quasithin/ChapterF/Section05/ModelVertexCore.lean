module
public import CFSG.Quasithin.ChapterF.Section05.ModelVertexFlag
public import Theory.SpecificGroups.OmegaSixThree.UnitaryFlagCore
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsTransport
import all CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsTransport
/-!
# The original plane graph centralizer and A2 in the model vertex

The native centralizer has order96. Its two marked involutions and the
independent twisted S4 complement already map onto V4×S4 inside the literal
triangle group, so equality follows by injectivity and this order. Transport
of the actual two-core then identifies A2 with O2(H)=V4×V4.

Source: Aschbacher--Smith F.5.3 and F.5.7, printed pp.300--303.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterF.Section05
open GreenBook.LieModels.UnitaryFour
open ExceptionalLocal
public noncomputable section
local notation "hn" => Nat.le_refl 1
local notation "X" => Extension.ProjectiveExtension 1 hn
local notation "C2" => Multiplicative (ZMod 2)
local notation "S4" => Equiv.Perm (Fin 4)
@[expose] def nativePlaneGraphCentralizer : Subgroup X :=
  Extension.plane 1 hn ⊓ centralizer ({Extension.sigma 1 hn} : Set X)

def nativePlaneGraphEquiv : nativePlaneGraphCentralizer ≃*
    centralizer ({modelGraph true} : Set (modelEndpoint true)) where
  toFun g := ⟨⟨g.val,g.property.1⟩,mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp g.property.2))⟩
  invFun g := ⟨g.val.val,g.val.property,mem_centralizer_singleton_iff.mpr
    (congrArg (fun a : modelEndpoint true => a.val) (mem_centralizer_singleton_iff.mp g.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def nativePlaneGraphProductEquiv : nativePlaneGraphCentralizer ≃* (C2 × S4) × C2 :=
  (((nativePlaneGraphEquiv.trans modelPlaneGraphEquiv).trans matrixPlaneGraphEquiv).trans
    (MulEquiv.prodCongr EndpointPlane.graphFixedPlaneEquivProduct (MulEquiv.refl C2)))

theorem nativePlaneGraphCentralizer_card : Nat.card nativePlaneGraphCentralizer = 96 := by
  rw [Nat.card_congr nativePlaneGraphProductEquiv.toEquiv]
  norm_num [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]


open OmegaSixThree OmegaSixThree.TriangleLocal OmegaSixThree.VertexComparison.FlagWords

theorem markedModelVertexMap_injective : Function.Injective markedModelVertexMap :=
  Subtype.val_injective.comp markedModelUnitaryExtensionEquivVertex.injective

theorem markedModelVertexMap_sigma : markedModelVertexMap (Extension.sigma 1 hn)=vertexGraphInvolution :=
  markedModelUnitaryExtensionEquivVertex_sigma

private theorem native_commutes_sigma (a : X)
    (h : markedModelVertexMap a*vertexGraphInvolution=vertexGraphInvolution*markedModelVertexMap a) :
    a∈centralizer ({Extension.sigma 1 hn} : Set X) := by
  apply mem_centralizer_singleton_iff.mpr
  apply markedModelVertexMap_injective
  simpa only [map_mul,markedModelVertexMap_sigma] using h

private theorem pair_commutes_graph : pairOmega*vertexGraphInvolution=vertexGraphInvolution*pairOmega := by
  have hh : pairElement*graphElement=graphElement*pairElement := by
    apply productEquiv.injective
    rw [map_mul,map_mul,show productEquiv pairElement=(delta,1) from pairElement_image,graphElement_image]
    decide +kernel
  exact congrArg Subtype.val hh

private theorem complement_commutes_graph (a : H) (ha : a∈complementFactor) :
    a.val*vertexGraphInvolution=vertexGraphInvolution*a.val := by
  have hh : a*graphElement=graphElement*a := by
    apply productEquiv.injective
    rw [map_mul,map_mul,graphElement_image]
    have ha1 : (productEquiv a).1=1 := ha.1
    apply Prod.ext <;> simp [ha1]
  exact congrArg Subtype.val hh

theorem nativePlaneGraphCentralizer_short : modelFlagElement 1∈nativePlaneGraphCentralizer := by
  refine ⟨?_,native_commutes_sigma _ ?_⟩
  · rw [modelFlagElement_short]
    exact (Source.planeInclusion _).property
  · change (markedModelUnitaryExtensionEquivVertex (modelFlagElement 1)).val*vertexGraphInvolution=
      vertexGraphInvolution*(markedModelUnitaryExtensionEquivVertex (modelFlagElement 1)).val
    rw [modelFlagElement_short,markedModelUnitaryExtensionEquivVertex_short]
    exact pair_commutes_graph

theorem nativePlaneGraphCentralizer_sigma : Extension.sigma 1 hn∈nativePlaneGraphCentralizer :=
  ⟨(Extension.mem_plane 1 hn _).mpr (planeParabolic 1 hn).one_mem,
    mem_centralizer_singleton_iff.mpr rfl⟩

theorem nativeLocalComplement_le_graphCentralizer : nativeLocalComplement≤nativePlaneGraphCentralizer := by
  intro a ha
  refine ⟨nativeLocalComplement_le_plane ha,native_commutes_sigma a ?_⟩
  have hm : markedModelVertexMap a∈complementFactor.map H.subtype := by
    rw [←nativeLocalComplement_image]
    exact mem_map_of_mem _ ha
  obtain ⟨b,hb,he⟩ := hm
  rw [←he]
  exact complement_commutes_graph b hb

theorem nativePlaneGraphCentralizer_image : nativePlaneGraphCentralizer.map markedModelVertexMap =
    fixedPlaneLocal.map H.subtype := by
  have hl : fixedPlaneLocal.map H.subtype≤nativePlaneGraphCentralizer.map markedModelVertexMap := by
    apply map_le_iff_le_comap.mpr
    apply fixedPlaneLocal_le_of_marks
    · change pairOmega∈nativePlaneGraphCentralizer.map markedModelVertexMap
      refine ⟨modelFlagElement 1,nativePlaneGraphCentralizer_short,?_⟩
      change (markedModelUnitaryExtensionEquivVertex (modelFlagElement 1)).val=_
      rw [modelFlagElement_short,markedModelUnitaryExtensionEquivVertex_short]
    · exact ⟨Extension.sigma 1 hn,nativePlaneGraphCentralizer_sigma,markedModelVertexMap_sigma⟩
    · apply map_le_iff_le_comap.mp
      rw [←nativeLocalComplement_image]
      exact map_mono nativeLocalComplement_le_graphCentralizer
  let : Finite nativePlaneGraphCentralizer :=
    Finite.of_injective nativePlaneGraphProductEquiv nativePlaneGraphProductEquiv.injective
  let : Finite (nativePlaneGraphCentralizer.map markedModelVertexMap) :=
    Finite.of_injective
      (nativePlaneGraphCentralizer.equivMapOfInjective markedModelVertexMap markedModelVertexMap_injective).symm
      (nativePlaneGraphCentralizer.equivMapOfInjective markedModelVertexMap markedModelVertexMap_injective).symm.injective
  apply (eq_of_le_of_card_ge hl ?_).symm
  rw [card_map_of_injective (K:=nativePlaneGraphCentralizer) markedModelVertexMap_injective,
    card_map_of_injective (K:=fixedPlaneLocal) H.subtype_injective,
    nativePlaneGraphCentralizer_card,fixedPlaneLocal_card]

@[expose] def nativePlaneCore : Subgroup X := nativePlaneGraphCentralizer.pCoreIn 2

theorem nativePlaneCore_image : nativePlaneCore.map markedModelVertexMap = localCore.map H.subtype := by
  rw [nativePlaneCore,map_pCoreIn_of_injective _ _ _ markedModelVertexMap_injective,
    nativePlaneGraphCentralizer_image,
    ←map_pCoreIn_of_injective 2 fixedPlaneLocal H.subtype H.subtype_injective,
    fixedPlaneLocal_core]

end
end CFSG.Quasithin.ChapterF.Section05
