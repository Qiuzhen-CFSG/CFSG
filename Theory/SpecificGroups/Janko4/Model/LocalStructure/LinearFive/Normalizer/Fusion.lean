module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.ExteriorAction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Construction
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Assembly
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.Seeds

/-!
# The two native F orbits are the distinct ambient involution classes

The marked decomposable representative is kernel mask 73 (2A), and the
nondecomposable representative is mask 51 (2B). Explicit local fusion paths
and the existing native class separation identify them. The two normalizer
words supply orbit transport before invoking decomposable preservation, so
there is no circular use of the full normalizer recognition.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.NativeNormalizer
open Cardinality KernelCount
open Representation Representation.SL5ExteriorSquare Representation.SL5TenDimensional
open Representation.SL5ExteriorSquare.TwoGeneratorRecognition
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localX localY localKernelSeed

def decomposableRep : F := ⟨fValue 2, fValue_mem 2⟩
def nondecomposableRep : F := ⟨fValue 1, fValue_mem 1⟩

theorem decomposableRep_marking : (exteriorMarking decomposableRep).toAdd = decomposable := by
  have h : exteriorParam (Multiplicative.ofAdd decomposable) = decomposableRep := by
    apply Subtype.ext
    exact exteriorParam_basis 0
  rw [← h]
  exact congrArg Multiplicative.toAdd (exteriorParam.symm_apply_apply _)

theorem nondecomposableRep_marking : (exteriorMarking nondecomposableRep).toAdd = nondecomposable := by
  have h : exteriorParam (Multiplicative.ofAdd nondecomposable) = nondecomposableRep := by
    apply Subtype.ext
    change (exteriorParam (Multiplicative.ofAdd (basis 0) * Multiplicative.ofAdd (basis 7)) : Model) = fValue 1
    rw [map_mul, Subgroup.coe_mul, exteriorParam_basis, exteriorParam_basis, ← fValue_xor]
    rfl
  rw [← h]
  exact congrArg Multiplicative.toAdd (exteriorParam.symm_apply_apply _)

theorem decomposableRep_first : IsConj (decomposableRep : Model) Janko4.a := by
  have hp : IsConj (kernelValue 3 : Model) (kernelValue 73 : Model) :=
    isConj_iff.mpr ⟨(kernelPairFusionWord : Model)⁻¹, by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using
        congrArg (fun x : M => (x : Model)) kernelPairFusionWord_conjugates⟩
  have hr : (decomposableRep : Model) = (kernelValue 73 : Model) := by
    change fValue 2 = _
    rw [show (2 : ℕ) = 2^(1 : Fin 10).val from rfl, fValue_basis]
    rfl
  rw [hr]
  apply hp.symm.trans
  obtain ⟨g,hg⟩ := pair_fuses_first matrixA_mul_self matrixB_pow_four
  refine isConj_iff.mpr ⟨g, ?_⟩
  rw [show kernelValue 3 = kernelPair matrixA_mul_self matrixB_pow_four from maskValue_three _ _]
  exact hg.symm

theorem nondecomposableRep_second :
    IsConj (nondecomposableRep : Model) (localKernelSeed matrixA_mul_self matrixB_pow_four : Model) := by
  have ht : IsConj (kernelValue 1 : Model) (kernelValue 51 : Model) :=
    isConj_iff.mpr ⟨(kernelFusionWord : Model)⁻¹, by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using
        congrArg (fun x : M => (x : Model)) kernelFusionWord_conjugates⟩
  have hr : (nondecomposableRep : Model) = (kernelValue 51 : Model) := by
    change fValue 1 = _
    rw [show (1 : ℕ) = 2^(0 : Fin 10).val from rfl, fValue_basis]
    rfl
  rw [hr]
  simpa only [show kernelValue 1 = localKernelSeed matrixA_mul_self matrixB_pow_four from maskValue_one _ _] using ht.symm

theorem representatives_not_isConj : ¬ IsConj (decomposableRep : Model) (nondecomposableRep : Model) := by
  intro h
  apply Cardinality.LocalInvolutionCensus.not_isConj_z_t
  simpa only [Cardinality.LocalInvolutionCensus.z_eq_a, Cardinality.LocalInvolutionCensus.t] using
    (decomposableRep_first.symm.trans (h.trans nondecomposableRep_second))

private theorem orbit_isConj (x y : F)
    (hxy : InExteriorOrbit (exteriorMarking x).toAdd (exteriorMarking y).toAdd) :
    IsConj (x : Model) (y : Model) := by
  obtain ⟨n,hn⟩ := normalizer_transporter_of_exteriorOrbit F exteriorMarking
    (normalizerElement 0) (normalizerElement 1)
    (action_eq_of_coordinates F exteriorMarking _ _ (exterior_conjugation 0))
    (action_eq_of_coordinates F exteriorMarking _ _ (exterior_conjugation 1)) x y hxy
  refine isConj_iff.mpr ⟨n, ?_⟩
  exact (Subgroup.normalizerMonoidHom_apply_apply_coe F n x).symm.trans
    (congrArg Subtype.val hn)

/-- Every normalizer element preserves the actual decomposable class in F. -/
theorem preserves_decomposable (n : Subgroup.normalizer (F : Set Model)) (x : F)
    (hx : InExteriorOrbit decomposable (exteriorMarking x).toAdd) :
    InExteriorOrbit decomposable (exteriorMarking (F.normalizerMonoidHom n x)).toAdd := by
  let y := F.normalizerMonoidHom n x
  have hx0 : (exteriorMarking x).toAdd ≠ 0 := by
    intro h
    exact decomposable_ne_zero (hx.eq_zero_iff.mpr h)
  have hx1 : x ≠ 1 := by
    intro h
    apply hx0
    rw [h, map_one]
    rfl
  have hy0 : (exteriorMarking y).toAdd ≠ 0 := by
    intro h
    have hy1 : y = 1 := exteriorMarking.injective
      ((congrArg Multiplicative.ofAdd h).trans exteriorMarking.map_one.symm)
    exact hx1 ((F.normalizerMonoidHom n).injective (hy1.trans (F.normalizerMonoidHom n).map_one.symm))
  rcases exterior_orbits_exhaustive (exteriorMarking y).toAdd hy0 with hD | hU
  · exact hD
  · exfalso
    have hdx := orbit_isConj decomposableRep x (by rw [decomposableRep_marking]; exact hx)
    have huy := orbit_isConj nondecomposableRep y (by rw [nondecomposableRep_marking]; exact hU)
    have hxy : IsConj (x : Model) (y : Model) :=
      isConj_iff.mpr ⟨n, (Subgroup.normalizerMonoidHom_apply_apply_coe F n x).symm⟩
    exact representatives_not_isConj (hdx.trans (hxy.trans huy.symm))

end Janko4.LocalStructure.LinearFive.NativeNormalizer
