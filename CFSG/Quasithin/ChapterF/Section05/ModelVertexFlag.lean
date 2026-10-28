module
public import CFSG.Quasithin.ChapterF.Section05.ModelVertex
public import Theory.SpecificGroups.OmegaSixThree.UnitaryFlagComplement
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsPlane
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionPlaneCommutator
import all CFSG.Quasithin.ChapterF.Section05.ModelVertex
import all Theory.SpecificGroups.OmegaSixThree.UnitaryVertex
import all CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsPlane
open SixTernaryCoordinates
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
open OmegaSixThree OmegaSixThree.VertexComparison
open FlagWords
/-!
# The literal F.5 flag and independent local complement

An explicitly checked inner adjustment aligns the source short root with the
first local square while preserving its long root and graph involution. The
ordinary fixed-plane S₄ generators acquire a nontrivial first-factor component;
twisting their odd generators by the short-root/graph product removes it.
The resulting subgroup lies in the original native plane extension and maps
onto the independent second S₄ factor, with both root images retained.

The internal imports expose only the existing vertex map and binary endpoint
matrices to establish these literal equations. No abstract complement choice
or unmarked local automorphism assertion is used.

Source: Aschbacher–Smith F.5.3 and F.5.7, printed pp.300–303.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1

/-- Coefficient transport of the six checked literal split matrices. -/
def modelFlagMatrix (j : Fin 6) : MatrixGroup 1 hn :=
  modelMatrixEquivSplit.symm (splitElement j)

theorem modelFlagMatrix_entry (j : Fin 6) (a b : Fin 4) :
    modelFieldEquiv ((modelFlagMatrix j).val.val a b) = splitMatrix j a b := by
  rw [← modelMatrixEquivSplit_entry]
  change (modelMatrixEquivSplit (modelMatrixEquivSplit.symm _)).val.val a b = _
  rw [modelMatrixEquivSplit.apply_symm_apply,splitElement_matrix]

def modelFlagElement (j : Fin 6) : Extension.ProjectiveExtension 1 hn :=
  Extension.extensionProjection 1 hn (SemidirectProduct.inl (modelFlagMatrix j))

theorem modelUnitaryExtensionEquivVertex_matrix (a : MatrixGroup 1 hn) :
    (modelUnitaryExtensionEquivVertex
      (Extension.extensionProjection 1 hn (SemidirectProduct.inl a))).val =
        splitBaseToOmega (modelMatrixEquivSplit a) := by
  have h := (Extension.extensionEquiv 1 hn).symm_apply_apply (SemidirectProduct.inl a)
  change (Extension.extensionEquiv 1 hn).symm
    (Extension.extensionProjection 1 hn (SemidirectProduct.inl a)) = _ at h
  simp only [modelUnitaryExtensionEquivVertex,MulEquiv.trans_apply,h]
  change splitExtensionToOmega (modelMatrixExtensionEquivSplit (SemidirectProduct.inl a)) = _
  rw [splitExtensionToOmega_apply]
  change splitBaseToOmega (modelMatrixEquivSplit a) * outerToOmega 1 = _
  rw [map_one,mul_one]

def modelFlagAdjustment : OmegaSixThree.OrthogonalityGraph.modelSystem.vertexGroup :=
  ⟨adjustment,by
    change adjustment • OrthogonalityGraph.point (OmegaSixThree.e 5) OmegaSixThree.quadratic_e5 =
      OrthogonalityGraph.point (OmegaSixThree.e 5) OmegaSixThree.quadratic_e5
    rw [OrthogonalityGraph.omega_smul_point,OrthogonalityGraph.point_eq_iff]
    exact Or.inl (splitBaseToOmega_fixes_vector _)⟩

def markedModelUnitaryExtensionEquivVertex : Extension.ProjectiveExtension 1 hn ≃*
    OmegaSixThree.OrthogonalityGraph.modelSystem.vertexGroup :=
  modelUnitaryExtensionEquivVertex.trans (MulAut.conj modelFlagAdjustment)

theorem markedModelUnitaryExtensionEquivVertex_sigma :
    (markedModelUnitaryExtensionEquivVertex (Extension.sigma 1 hn)).val =
      vertexGraphInvolution := by
  change adjustment * (modelUnitaryExtensionEquivVertex (Extension.sigma 1 hn)).val *
    adjustment⁻¹ = _
  rw [modelUnitaryExtensionEquivVertex_sigma,adjustment_graph]

theorem markedModelUnitaryExtensionEquivVertex_flag (j : Fin 6) :
    (markedModelUnitaryExtensionEquivVertex (modelFlagElement j)).val =
      adjustedBase (splitElement j) := by
  change adjustment * (modelUnitaryExtensionEquivVertex
    (Extension.extensionProjection 1 hn (SemidirectProduct.inl (modelFlagMatrix j)))).val *
    adjustment⁻¹ = _
  rw [modelUnitaryExtensionEquivVertex_matrix]
  change adjustment * splitBaseToOmega (modelMatrixEquivSplit
    (modelMatrixEquivSplit.symm _)) * adjustment⁻¹ = _
  rw [modelMatrixEquivSplit.apply_symm_apply]
  rfl


open UnitaryFourShortRoot UnitaryFourPlaneRadical
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn

theorem modelFlagMatrix_long : modelFlagMatrix 0 = (longLocal F σ hσ).val := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro a b
  apply modelFieldEquiv.injective
  rw [modelFlagMatrix_entry]
  change splitMatrix 0 a b = modelFieldEquiv (unipotentMatrix F (longParameter F σ).val a b)
  fin_cases a <;> fin_cases b <;>
    simp [splitMatrix,unipotentMatrix,longParameter]

theorem modelFlagMatrix_short : modelFlagMatrix 1 = (shortLocal F σ hσ).val := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro a b
  apply modelFieldEquiv.injective
  rw [modelFlagMatrix_entry]
  change splitMatrix 1 a b = modelFieldEquiv (unipotentMatrix F (shortParameter F σ).val a b)
  fin_cases a <;> fin_cases b <;>
    simp [splitMatrix,unipotentMatrix,shortParameter]

open ExceptionalLocal

theorem modelFlagMatrix_complement (k : Fin 3) :
    modelFlagMatrix ⟨k.val+3,by omega⟩ =
      (EndpointPlane.graphFixedPlaneEquivProduct.symm
        (1,Equiv.swap k.castSucc k.succ)).val.val := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro a b
  apply modelFieldEquiv.injective
  rw [modelFlagMatrix_entry]
  change splitMatrix ⟨k.val+3,by omega⟩ a b = modelFieldEquiv
    (EndpointPlane.binaryCast (EndpointPlane.binaryMatrix (1,Equiv.swap k.castSucc k.succ) a b))
  let B : Fin 3 → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    ![!![1,1,1,0;0,1,0,1;0,0,1,1;0,0,0,1],
      !![0,1,0,0;1,0,0,0;0,0,0,1;0,0,1,0],
      !![1,1,0,0;0,1,0,0;0,0,1,1;0,0,0,1]]
  have hb : ∀ k : Fin 3, EndpointPlane.binaryMatrix (1,Equiv.swap k.castSucc k.succ) = B k := by
    decide +kernel
  rw [hb]
  fin_cases k <;> fin_cases a <;> fin_cases b <;> simp [B,splitMatrix]


theorem modelFlagElement_long : modelFlagElement 0 =
    (Source.pointInclusion UnitaryTwo.ShortRootFixedFour.longPoint).val := by
  rw [modelFlagElement,modelFlagMatrix_long]
  rfl

theorem modelFlagElement_short : modelFlagElement 1 =
    (Source.planeInclusion (planeParameterMap
      (Multiplicative.ofAdd (shortParameter F σ)))).val := by
  rw [modelFlagElement,modelFlagMatrix_short]
  rfl

/-- The original marked point root has the printed four-coordinate sign image. -/
theorem markedModelUnitaryExtensionEquivVertex_long :
    (markedModelUnitaryExtensionEquivVertex
      (Source.pointInclusion UnitaryTwo.ShortRootFixedFour.longPoint).val).val.val =
        signChange {0,1,2,3} := by
  rw [←modelFlagElement_long,markedModelUnitaryExtensionEquivVertex_flag]
  exact adjustedBase_long

/-- The original short root has the central square involution as its image. -/
theorem markedModelUnitaryExtensionEquivVertex_short :
    (markedModelUnitaryExtensionEquivVertex
      (Source.planeInclusion (planeParameterMap
        (Multiplicative.ofAdd (shortParameter F σ)))).val).val =
          TriangleLocal.pairOmega := by
  rw [←modelFlagElement_short,markedModelUnitaryExtensionEquivVertex_flag]
  exact adjustedBase_short

def nativePlaneComplementGenerator (k : Fin 3) : Extension.ProjectiveExtension 1 hn :=
  Extension.extensionProjection 1 hn (SemidirectProduct.inl
    (EndpointPlane.graphFixedPlaneEquivProduct.symm
      (1,Equiv.swap k.castSucc k.succ)).val.val)

def nativeLocalComplementGenerator (k : Fin 3) : Extension.ProjectiveExtension 1 hn :=
  nativePlaneComplementGenerator k *
    (Source.planeInclusion (planeParameterMap
      (Multiplicative.ofAdd (shortParameter F σ)))).val * Extension.sigma 1 hn

theorem markedModelUnitaryExtensionEquivVertex_complement (k : Fin 3) :
    (markedModelUnitaryExtensionEquivVertex (nativeLocalComplementGenerator k)).val =
      complementGenerator k := by
  rw [nativeLocalComplementGenerator,map_mul,map_mul]
  change (markedModelUnitaryExtensionEquivVertex (nativePlaneComplementGenerator k)).val *
    (markedModelUnitaryExtensionEquivVertex _).val *
      (markedModelUnitaryExtensionEquivVertex _).val = _
  rw [markedModelUnitaryExtensionEquivVertex_short,markedModelUnitaryExtensionEquivVertex_sigma]
  have hg : nativePlaneComplementGenerator k = modelFlagElement ⟨k.val+3,by omega⟩ := by
    rw [nativePlaneComplementGenerator,modelFlagElement,modelFlagMatrix_complement]
  rw [hg,markedModelUnitaryExtensionEquivVertex_flag]
  rfl


/-- The independent S₄ inside the literal native plane extension. Its odd
ordinary generators are twisted by the marked short-root/graph product. -/
def nativeLocalComplement : Subgroup (Extension.ProjectiveExtension 1 hn) :=
  Subgroup.closure (Set.range nativeLocalComplementGenerator)

/-- The marked vertex map, including its original ambient Omega inclusion. -/
def markedModelVertexMap : Extension.ProjectiveExtension 1 hn →* omegaPlusSixThree :=
  OrthogonalityGraph.modelSystem.vertexGroup.subtype.comp
    markedModelUnitaryExtensionEquivVertex.toMonoidHom

/-- The actual native complement maps onto the independent second model factor. -/
theorem nativeLocalComplement_image : nativeLocalComplement.map markedModelVertexMap =
    TriangleLocal.complementFactor.map TriangleLocal.H.subtype := by
  rw [nativeLocalComplement,MonoidHom.map_closure]
  rw [←complementGenerator_generate]
  congr 1
  ext g
  constructor
  · rintro ⟨a,⟨k,rfl⟩,rfl⟩
    exact ⟨k,(markedModelUnitaryExtensionEquivVertex_complement k).symm⟩
  · rintro ⟨k,rfl⟩
    exact ⟨nativeLocalComplementGenerator k,⟨k,rfl⟩,
      markedModelUnitaryExtensionEquivVertex_complement k⟩

/-- The exact native subgroup has order24; this follows from the actual
comparison map and its image, retaining the chosen complement. -/
theorem nativeLocalComplement_card : Nat.card nativeLocalComplement = 24 := by
  have hj : Function.Injective markedModelVertexMap :=
    Subtype.val_injective.comp markedModelUnitaryExtensionEquivVertex.injective
  rw [←Subgroup.card_map_of_injective (K := nativeLocalComplement) hj,
    nativeLocalComplement_image,Subgroup.card_map_of_injective (K := TriangleLocal.complementFactor) TriangleLocal.H.subtype_injective]
  rw [Nat.card_congr TriangleLocal.complementEquiv.toEquiv]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]


theorem nativeLocalComplement_le_plane : nativeLocalComplement ≤ Extension.plane 1 hn := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k,rfl⟩
  apply (Extension.plane 1 hn).mul_mem
  · apply (Extension.plane 1 hn).mul_mem
    · exact ⟨SemidirectProduct.inl (EndpointPlane.graphFixedPlaneEquivProduct.symm
        (1,Equiv.swap k.castSucc k.succ)).val.val,
        (EndpointPlane.graphFixedPlaneEquivProduct.symm
          (1,Equiv.swap k.castSucc k.succ)).val.property,rfl⟩
    · exact (Source.planeInclusion (planeParameterMap
        (Multiplicative.ofAdd (shortParameter F σ)))).property
  · exact (Extension.mem_plane 1 hn _).mpr (planeParabolic 1 hn).one_mem

end CFSG.Quasithin.ChapterF.Section05
