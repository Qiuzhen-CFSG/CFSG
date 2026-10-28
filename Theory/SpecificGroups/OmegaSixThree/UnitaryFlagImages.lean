module
public import Theory.SpecificGroups.OmegaSixThree.UnitaryFlagWords
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.Marks
import all Theory.SpecificGroups.OmegaSixThree.VertexComparison
import all Theory.SpecificGroups.OmegaSixThree.UnitaryVertex
open Matrix Atlas.Algebra SixTernaryCoordinates
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
/-!
# Literal roots and complement generators in the orthogonal vertex

The checked unitary words have explicit six-dimensional images. Conjugating
by the third word fixes the graph involution and long root and aligns the
short root with the central involution of the first local square. Twisting
the three ordinary plane-complement generators by the short-root/graph product
then yields pure second-factor transpositions. The internal imports only expose
the existing comparison maps in order to prove their action equations.

Source: Aschbacher–Smith F.5.3 and F.5.7, printed pp.300–303.
-/
@[expose] public noncomputable section
namespace OmegaSixThree.VertexComparison.FlagWords

theorem splitBase_word (i : Fin 6) :
    splitBaseToOmega (splitElement i) = spToOmega (evaluate symplecticGenerator i) := by
  simp only [splitElement,splitBaseToOmega,MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    SplitMarking.splitEquivStandard.apply_symm_apply]
  rw [map_evaluate]
  rw [map_evaluate spToOmega]
  congr 1
  funext j
  exact standardToOmega_generator j

def imageMatrix : Fin 6 → Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  ![!![2,0,0,0,0,0; 0,2,0,0,0,0; 0,0,2,0,0,0; 0,0,0,2,0,0; 0,0,0,0,1,0; 0,0,0,0,0,1],
    !![0,1,0,0,0,0; 1,0,0,0,0,0; 0,0,0,2,0,0; 0,0,2,0,0,0; 0,0,0,0,1,0; 0,0,0,0,0,1],
    !![1,2,1,1,0,0; 2,1,1,1,0,0; 1,1,1,2,0,0; 1,1,2,1,0,0; 0,0,0,0,2,0; 0,0,0,0,0,1],
    !![2,0,0,0,0,0; 0,2,0,0,0,0; 0,0,1,0,0,0; 0,0,0,1,0,0; 0,0,0,0,1,0; 0,0,0,0,0,1],
    !![2,0,1,2,1,0; 0,2,1,2,1,0; 1,1,0,1,2,0; 2,2,1,0,1,0; 1,1,2,1,0,0; 0,0,0,0,0,1],
    !![0,1,0,0,0,0; 1,0,0,0,0,0; 0,0,0,1,0,0; 0,0,1,0,0,0; 0,0,0,0,1,0; 0,0,0,0,0,1]]

theorem splitBase_word_apply (i : Fin 6) (v : Space) :
    (splitBaseToOmega (splitElement i)).val v = imageMatrix i *ᵥ v := by
  have he : (splitBaseToOmega (splitElement i)).val.toLinearMap =
      Matrix.toLin' (imageMatrix i) := by
    apply (Pi.basisFun (ZMod 3) (Fin 6)).ext
    intro j
    simp only [LinearEquiv.coe_coe, Pi.basisFun_apply,Matrix.toLin'_apply]
    rw [splitBase_word]
    change (slToOmega (spToSL (evaluate symplecticGenerator i))).val _ = _
    rw [slToOmega_apply,spWord_matrix]
    revert i j
    decide +kernel
  exact LinearMap.congr_fun he v

def adjustment : omegaPlusSixThree := splitBaseToOmega (splitElement 2)

theorem adjustment_squared : adjustment * adjustment = 1 := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 3) (Fin 6)).ext
  intro j
  simp only [LinearEquiv.coe_coe,Pi.basisFun_apply,Subgroup.coe_mul,
    LinearEquiv.mul_apply,Subgroup.coe_one,LinearEquiv.coe_one,id_eq]
  change (splitBaseToOmega (splitElement 2)).val
    ((splitBaseToOmega (splitElement 2)).val _) = _
  rw [splitBase_word_apply,splitBase_word_apply]
  revert j
  decide +kernel

theorem adjustment_inv : adjustment⁻¹ = adjustment := by
  exact inv_eq_of_mul_eq_one_left adjustment_squared

theorem adjustment_graph : adjustment * vertexGraphInvolution * adjustment⁻¹ =
    vertexGraphInvolution := by
  rw [adjustment_inv]
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 3) (Fin 6)).ext
  intro j
  simp only [LinearEquiv.coe_coe,Pi.basisFun_apply,Subgroup.coe_mul,
    LinearEquiv.mul_apply]
  change (splitBaseToOmega (splitElement 2)).val
    (graphInvolution ((splitBaseToOmega (splitElement 2)).val _)) = _
  rw [splitBase_word_apply,splitBase_word_apply]
  revert j
  decide +kernel

def adjustedBase : SplitSU →* omegaPlusSixThree :=
  (MulAut.conj adjustment).toMonoidHom.comp splitBaseToOmega

theorem adjustedBase_word_apply (i : Fin 6) (v : Space) :
    (adjustedBase (splitElement i)).val v =
      imageMatrix 2 *ᵥ (imageMatrix i *ᵥ (imageMatrix 2 *ᵥ v)) := by
  change (adjustment * splitBaseToOmega (splitElement i) * adjustment⁻¹).val v = _
  rw [adjustment_inv]
  change adjustment.val ((splitBaseToOmega (splitElement i)).val (adjustment.val v)) = _
  rw [show adjustment = splitBaseToOmega (splitElement 2) from rfl]
  rw [splitBase_word_apply,splitBase_word_apply,splitBase_word_apply]

theorem adjustedBase_long : (adjustedBase (splitElement 0)).val = signChange {0,1,2,3} := by
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 3) (Fin 6)).ext
  intro j
  simp only [LinearEquiv.coe_coe,Pi.basisFun_apply]
  rw [adjustedBase_word_apply]
  revert j
  decide +kernel

theorem adjustedBase_short : adjustedBase (splitElement 1) = TriangleLocal.pairOmega := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 3) (Fin 6)).ext
  intro j
  simp only [LinearEquiv.coe_coe,Pi.basisFun_apply]
  rw [adjustedBase_word_apply]
  revert j
  decide +kernel

/-- The corrected image of an odd ordinary plane-complement generator, twisted
by the marked short root and graph involution. -/
def complementGenerator (k : Fin 3) : omegaPlusSixThree :=
  adjustedBase (splitElement ⟨k.val+3,by omega⟩) * TriangleLocal.pairOmega * vertexGraphInvolution

theorem complementGenerator_apply (k : Fin 3) (v : Space) :
    (complementGenerator k).val v =
      imageMatrix 2 *ᵥ (imageMatrix ⟨k.val+3,by omega⟩ *ᵥ
        (imageMatrix 2 *ᵥ ((signChange {0,1}) (graphInvolution v)))) := by
  change (adjustedBase (splitElement ⟨k.val+3,by omega⟩)).val
    (TriangleLocal.pairOmega.val (vertexGraphInvolution.val v)) = _
  exact adjustedBase_word_apply _ _

theorem complementGenerator_mem (k : Fin 3) : complementGenerator k ∈ TriangleLocal.H := by
  apply (OrthogonalityGraph.mem_triangleStabilizer_iff _).mpr
  apply Set.EqOn.image_eq_self
  intro p hp
  obtain ⟨j,rfl⟩ := (TriangleLocal.mem_standardTriangle_iff p).mp hp
  apply (OrthogonalityGraph.point_eq_iff _ _ _ _).mpr
  change TriangleLocal.signed ((complementGenerator k).val (TriangleLocal.negativeBasis j)) _
  rw [complementGenerator_apply]
  clear hp
  revert k j
  unfold TriangleLocal.signed
  decide +kernel

def complementElement (k : Fin 3) : TriangleLocal.H :=
  ⟨complementGenerator k,complementGenerator_mem k⟩

def complementPermutation (k : Fin 3) : Equiv.Perm (Fin 4) :=
  ![Equiv.swap 0 1, Equiv.swap 0 3, Equiv.swap 2 3] k

theorem complementElement_image (k : Fin 3) :
    TriangleLocal.productEquiv (complementElement k) =
      (1,complementPermutation k) := by
  apply Prod.ext <;> apply Equiv.ext <;> intro j
  · apply TriangleLocal.imageIndex_eq
    change TriangleLocal.signed ((complementGenerator k).val (TriangleLocal.tetra false j)) _
    rw [complementGenerator_apply]
    revert k j
    unfold TriangleLocal.signed
    decide +kernel
  · apply TriangleLocal.imageIndex_eq
    change TriangleLocal.signed ((complementGenerator k).val (TriangleLocal.tetra true j)) _
    rw [complementGenerator_apply]
    revert k j
    unfold TriangleLocal.signed
    decide +kernel

end OmegaSixThree.VertexComparison.FlagWords
