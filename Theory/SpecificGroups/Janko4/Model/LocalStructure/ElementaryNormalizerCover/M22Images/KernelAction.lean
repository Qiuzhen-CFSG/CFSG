module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.OctadNormalizer
public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Coordinates

/-!
# Kernel characters in the native Mathieu local

The actual star action gives conjugation on all eleven binary kernel
coordinates. Fixing the endpoints of a pair places an element in the
residual of that pair's full centralizer. These facts are used by the sextet
lift to calculate its orthogonal kernel, with the original inclusions.

Source: Kleidman--Wilson (1988), Proposition 2.2.2, pp.490--491.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.KernelAction
open Cardinality QuotientCount.Image KernelCount
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits Simplicity.Max1Fusion.QuotientInvolutions
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

theorem projection_star (g : M) : projection g = starGroupEquivM24 (starHom g) := by
  change localQuotientEquivM24 matrixA_mul_self matrixB_pow_four (QuotientGroup.mk' _ g) = _
  rw [localQuotientEquivM24_apply]
  rfl

theorem star_points (x : M) (p : M23) (hx : projection x = pointEmbedding p)
    (j : Fin 24) : (starHom x).val j = StarOrderCertificate.relabel.symm
      (M23Geometry.CommonFour.extendPoint p.val (StarOrderCertificate.relabel j)) := by
  calc
    (starHom x).val j = StarOrderCertificate.relabel.symm
        ((projection x).val (StarOrderCertificate.relabel j)) := by
      rw [projection_star,starGroupEquivM24_apply]
      simp
    _ = _ := by rw [hx,M23Geometry.CommonFour.pointEmbedding_apply_all]

theorem kernel_conjugation (x : M) (m : ℕ) :
    x * kernelValue m * x⁻¹ = kernelValue
      (maskImage (fun j => pairLabel ((starHom x).val (basisPair j).1)
        ((starHom x).val (basisPair j).2)) m) := by
  have hb (j : Fin 11) : x * basis matrixA_mul_self matrixB_pow_four j * x⁻¹ =
      kernelValue (pairLabel ((starHom x).val (basisPair j).1)
        ((starHom x).val (basisPair j).2)) := by
    rw [← maskValue_basis matrixA_mul_self matrixB_pow_four j,← pairLabel_basisPair j]
    exact congrArg Subtype.val (starHom_pair x (basisPair j).1 (basisPair j).2)
  change (MulAut.conj x).toMonoidHom (binaryProduct (basis matrixA_mul_self matrixB_pow_four)
    (fun j => m.testBit j.val)) = _
  rw [map_binaryProduct]
  rw [show kernelValue (maskImage (fun j => pairLabel ((starHom x).val (basisPair j).1)
      ((starHom x).val (basisPair j).2)) m) = _ from
    maskValue_maskImage matrixA_mul_self matrixB_pow_four _ m]
  congr 1
  funext j
  exact hb j

private theorem pair_to_seed (i j : Fin 24) (hij : i ≠ j) :
    ∃ g : M, g * kernelValue (pairLabel i j) * g⁻¹ = kernelValue 1 := by
  have hn : kernelValue (pairLabel i j) ≠ 1 := by
    intro he
    have hl := kernelValue_injective (pairLabel_lt i j) (by decide) (he.trans kernelValue_zero.symm)
    exact hij ((pairLabel_eq_zero_iff i j).mp hl)
  obtain ⟨g,hg | hg⟩ := kernel_nonidentity_orbits matrixA_mul_self matrixB_pow_four
    (kernelValue (pairLabel i j)) (maskValue _ _ _).property hn
  · exact ⟨g,hg.symm.trans (maskValue_one _ _).symm⟩
  · have he : kernelValue (pairLabel ((starHom g).val i) ((starHom g).val j)) = kernelValue 3 :=
      (congrArg Subtype.val (starHom_pair g i j)).symm.trans
        (hg.symm.trans (maskValue_three _ _).symm)
    have hl := kernelValue_injective (pairLabel_lt _ _) (by decide) he
    have hh : ∀ i j : Fin 24, pairLabel i j ≠ 3 := by decide +kernel
    exact (hh _ _ hl).elim

theorem pair_order (i j : Fin 24) (hij : i ≠ j) :
    orderOf (kernelValue (pairLabel i j) : Model) = 2 := by
  obtain ⟨g,hg⟩ := pair_to_seed i j hij
  have he : (MulAut.conj (g : Model)) (kernelValue (pairLabel i j) : Model) =
      (seed : Model) := congrArg (fun x : M => (x : Model)) (hg.trans (maskValue_one _ _))
  rw [← (MulAut.conj (g : Model)).orderOf_eq,he]
  exact seed_order

/-- Pointwise fixation of a kernel pair is the intrinsic inner-half condition. -/
theorem inner_of_star_fixed (x : M) (i j : Fin 24) (hij : i ≠ j)
    (hi : (starHom x).val i = i) (hj : (starHom x).val j = j) :
    InnerRelated (kernelValue (pairLabel i j) : Model) (x : Model) := by
  obtain ⟨g,hg⟩ := pair_to_seed i j hij
  let y : M := g*x*g⁻¹
  have hlabel : pairLabel ((starHom g).val i) ((starHom g).val j) = 1 :=
    kernelValue_injective (pairLabel_lt _ _) (by decide)
      ((congrArg Subtype.val (starHom_pair g i j)).symm.trans hg)
  have hp : ∀ a b : Fin 24, pairLabel a b = 1 →
      (a=0 ∧ b=1) ∨ (a=1 ∧ b=0) := by decide +kernel
  have hact (k : Fin 24) : (starHom y).val ((starHom g).val k) =
      (starHom g).val ((starHom x).val k) := by simp [y,map_mul,map_inv]
  have hfixed : (starHom y).val 0 = 0 ∧ (starHom y).val 1 = 1 := by
    rcases hp _ _ hlabel with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact ⟨by simpa only [ha,hi] using hact i, by simpa only [hb,hj] using hact j⟩
    · exact ⟨by simpa only [hb,hj] using hact j, by simpa only [ha,hi] using hact i⟩
  have hy : y ∈ localCentralizer := by
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg Subtype.val (starHom_pair y 0 1)
    rw [hfixed.1,hfixed.2] at he
    change y * kernelValue 1 * y⁻¹ = kernelValue 1 at he
    rw [show kernelValue 1 = seed from maskValue_one _ _] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hinner := (innerRelated_second_iff_star ⟨y,hy⟩).mpr hfixed
  have hg' : (MulAut.conj (g : Model)) (kernelValue (pairLabel i j) : Model) =
      (seed : Model) := congrArg (fun x : M => (x : Model)) (hg.trans (maskValue_one _ _))
  apply (innerRelated_equiv (MulAut.conj (g : Model)) _ _).mp
  rw [hg']
  exact hinner

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.KernelAction
