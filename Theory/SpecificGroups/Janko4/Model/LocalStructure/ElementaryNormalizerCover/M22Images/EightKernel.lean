module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.OctadNormalizer
public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Coordinates

/-!
# The exceptional E8 image and its orthogonal kernel

Three generators of the literal E8 quotient image fix sixteen binary kernel
masks. Each fixed mask is one of eight pair labels or its sum with the
distinguished fixed pair. Every other pair is swapped by a displayed quotient
element. Lifting that element from X and using the actual second-centralizer
character excludes the pair when X has zero intrinsic form. Thus X intersects
the native E precisely in the distinguished pair line.

The action comparison uses the actual Mathieu projection and conjugation on
the original eleven-dimensional kernel. The finite check covers 2048 masks;
no unproved centralizer or orthogonality table is assumed. `EightLift` carries
the result through the original M22 residual marking.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Proposition
2.2.2(iv), pp.490--491. The native permutation and binary labels retain the
ATLAS attribution of the imported M23 and J4 certificates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.EightKernel
open Cardinality QuotientCount.Image KernelCount
open Simplicity.Max1Fusion.KernelOrbits Simplicity.Max1Fusion.QuotientInvolutions
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open M23Geometry FusionCertificate
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

@[expose] def imageGroup : Subgroup M24 := (small 0).map pointEmbedding
@[expose] def imageElement (i : Fin 8) : M24 := pointEmbedding (sylowElement (smallIndex 0 i))

theorem imageElement_mem (i : Fin 8) : imageElement i ∈ imageGroup :=
  mem_map_of_mem pointEmbedding (show sylowElement (smallIndex 0 i) ∈ small 0 from ⟨i,rfl⟩)

private def starTable : Fin 8 → Fin 24 → Fin 24 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 16, 11, 3, 21, 5, 6, 7, 14, 17, 12, 2, 10, 13, 8, 19, 1, 9, 18, 15, 22, 4, 20, 23], ![0, 16, 12, 18, 21, 5, 23, 7, 8, 15, 11, 10, 2, 13, 14, 9, 1, 19, 3, 17, 20, 4, 22, 6], ![0, 1, 10, 18, 4, 5, 23, 7, 14, 19, 2, 12, 11, 13, 8, 17, 16, 15, 3, 9, 22, 21, 20, 6], ![7, 1, 17, 18, 21, 5, 6, 0, 14, 11, 15, 9, 19, 13, 8, 10, 16, 2, 3, 12, 20, 4, 22, 23], ![7, 16, 9, 18, 4, 5, 6, 0, 8, 2, 19, 17, 15, 13, 14, 12, 1, 11, 3, 10, 22, 21, 20, 23], ![7, 16, 19, 3, 4, 5, 23, 0, 14, 10, 9, 15, 17, 13, 8, 11, 1, 12, 18, 2, 20, 21, 22, 6], ![7, 1, 15, 3, 21, 5, 23, 0, 8, 12, 17, 19, 9, 13, 14, 2, 16, 10, 18, 11, 22, 4, 20, 6]]
private theorem starTable_spec : ∀ (i : Fin 8) (x : Fin 24),
    StarOrderCertificate.relabel.symm
      (M23Geometry.CommonFour.extendPoint (pointTable (smallIndex 0 i))
        (StarOrderCertificate.relabel x)) = starTable i x := by decide +kernel

private def generatorIndex : Fin 3 → Fin 8 := ![1,2,4]
private def rows : Fin 3 → Fin 11 → ℕ := ![![1058, 295, 1553, 8, 1824, 534, 851, 165, 256, 54, 816], ![1058, 1912, 1553, 1874, 841, 32, 598, 1484, 256, 54, 1881], ![78, 464, 1553, 71, 699, 857, 1927, 1086, 256, 1045, 1764]]
private theorem rows_spec : ∀ (i : Fin 3) (j : Fin 11),
    pairLabel (starTable (generatorIndex i) (basisPair j).1)
      (starTable (generatorIndex i) (basisPair j).2) = rows i j := by decide +kernel

private def pairPoints : Fin 8 → Fin 24 × Fin 24 :=
  ![(0,7),(1,16),(3,18),(4,21),(5,13),(6,23),(8,14),(20,22)]
private def pairMask : Fin 8 → ℕ := ![79,1059,1388,1557,633,1882,822,256]
private theorem pairMask_spec (i : Fin 8) :
    pairLabel (pairPoints i).1 (pairPoints i).2 = pairMask i := by
  have h : ∀ i : Fin 8, pairLabel (pairPoints i).1 (pairPoints i).2 = pairMask i := by decide +kernel
  exact h i
private def swapIndex : Fin 8 → Fin 8 := ![4,1,2,1,0,2,1,1]
private theorem swap_spec : ∀ i : Fin 8, i ≠ 4 →
    (pairPoints i).1 ≠ (pairPoints i).2 ∧
    starTable (swapIndex i) (pairPoints i).1 = (pairPoints i).2 ∧
    starTable (swapIndex i) (pairPoints i).2 = (pairPoints i).1 := by decide +kernel

private theorem fixed_masks : ∀ m : Fin 2048,
    maskImage (rows 0) m.val = m.val →
    maskImage (rows 1) m.val = m.val →
    maskImage (rows 2) m.val = m.val →
    ∃ i : Fin 8, m.val = pairMask i ∨ m.val = Nat.xor (pairMask i) 633 := by decide +kernel

private theorem projection_star (g : M) : projection g = starGroupEquivM24 (starHom g) := by
  change localQuotientEquivM24 matrixA_mul_self matrixB_pow_four (QuotientGroup.mk' _ g) = _
  rw [localQuotientEquivM24_apply]
  rfl

private theorem star_points (x : M) (i : Fin 8) (hx : projection x = imageElement i)
    (j : Fin 24) : (starHom x).val j = starTable i j := by
  calc
    (starHom x).val j = StarOrderCertificate.relabel.symm
        ((projection x).val (StarOrderCertificate.relabel j)) := by
      rw [projection_star,starGroupEquivM24_apply]
      simp
    _ = StarOrderCertificate.relabel.symm
        (CommonFour.extendPoint (pointTable (smallIndex 0 i))
          (StarOrderCertificate.relabel j)) := by
      rw [hx]
      change StarOrderCertificate.relabel.symm
        ((pointEmbedding (sylowElement (smallIndex 0 i))).val (StarOrderCertificate.relabel j)) = _
      rw [CommonFour.pointEmbedding_apply_all]
      rfl
    _ = starTable i j := starTable_spec i j

private theorem kernel_conjugation (x : M) (m : ℕ) :
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

private theorem image_lift (X : Subgroup Model)
    (himage : (X.subgroupOf M).map projection = imageGroup) (i : Fin 8) :
    ∃ x : M, (x : Model) ∈ X ∧ projection x = imageElement i := by
  have h := imageElement_mem i
  rw [← himage] at h
  exact h

private theorem kernel_fixed (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (himage : (X.subgroupOf M).map projection = imageGroup)
    (m : Fin 2048) (hmX : (kernelValue m.val : Model) ∈ X) (i : Fin 3) :
    maskImage (rows i) m.val = m.val := by
  obtain ⟨x,hx,hpi⟩ := image_lift X himage (generatorIndex i)
  have hc : Commute (kernelValue m.val) x := by
    apply Subtype.ext
    exact (X.le_centralizer hx) _ hmX
  have hrow : (fun j => pairLabel ((starHom x).val (basisPair j).1)
    ((starHom x).val (basisPair j).2)) = rows i := by
    funext j
    rw [star_points x _ hpi,star_points x _ hpi,rows_spec]
  have he : kernelValue (maskImage (rows i) m.val) = kernelValue m.val := by
    rw [← hrow,← kernel_conjugation,← hc.eq,mul_assoc,mul_inv_cancel,mul_one]
  apply kernelValue_injective ?_ m.isLt he
  rw [← hrow]
  exact SylowCore.Transport.starMask_lt (starHom x) m.val

private theorem no_swapped_pair (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (himage : (X.subgroupOf M).map projection = imageGroup)
    (hzero : intrinsicElementaryForm X = 0) (i : Fin 8) (hi : i ≠ 4) :
    (kernelValue (pairMask i) : Model) ∉ X := by
  intro hpair
  obtain ⟨x,hx,hpi⟩ := image_lift X himage (swapIndex i)
  obtain ⟨hne,ha,hb⟩ := swap_spec i hi
  have hpair1 : (kernelValue (pairMask i) : Model) ≠ 1 := by
    intro h
    have hk : pairMask i = 0 := kernelValue_injective
      (pairMask_spec i ▸ pairLabel_lt _ _) (by decide)
      ((show kernelValue (pairMask i) = 1 from Subtype.ext h).trans kernelValue_zero.symm)
    rw [← pairMask_spec] at hk
    exact hne ((pairLabel_eq_zero_iff _ _).mp hk)
  have hinner := zero_form_le_involution_residual X hzero _ hpair hpair1 hx
  rw [← pairMask_spec] at hinner
  exact LinearFive.Geometry.not_inner_of_star_swap x _ _ hne
    ((star_points x _ hpi _).trans ha) ((star_points x _ hpi _).trans hb) hinner

/-- In the exceptional E8 image, zero intrinsic form leaves only the
distinguished pair line in the kernel. This uses actual pair swapping by
lifts from X, not an assumed orthogonality table. -/
theorem kernel_mask_zero_or_seed (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (himage : (X.subgroupOf M).map projection = imageGroup)
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (kernelValue 633 : Model) ∈ X)
    (m : Fin 2048) (hmX : (kernelValue m.val : Model) ∈ X) :
    m.val = 0 ∨ m.val = 633 := by
  obtain ⟨i,hi⟩ := fixed_masks m (kernel_fixed X himage m hmX 0)
    (kernel_fixed X himage m hmX 1) (kernel_fixed X himage m hmX 2)
  by_cases hi4 : i = 4
  · subst i
    rcases hi with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hp : (kernelValue (pairMask i) : Model) ∈ X := by
    rcases hi with h | h
    · exact h ▸ hmX
    · have hk : kernelValue (pairMask i) = kernelValue m.val * kernelValue 633 := by
        rw [← kernelValue_xor,h]
        change kernelValue (pairMask i) = kernelValue ((pairMask i ^^^ 633) ^^^ 633)
        rw [Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
      rw [hk]
      exact X.mul_mem hmX hseed
  exact (no_swapped_pair X himage hzero i hi4 hp).elim

/-- The literal exceptional kernel intersection, retaining its actual
pair representative in the native Mathieu kernel. -/
theorem kernel_intersection_eq (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (himage : (X.subgroupOf M).map projection = imageGroup)
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (kernelValue 633 : Model) ∈ X) :
    X ⊓ E = zpowers (kernelValue 633 : Model) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨k,hk,rfl⟩ := hz.2
    obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨k,hk⟩
    have he : kernelValue m.val = k := congrArg Subtype.val hm
    have hX : (kernelValue m.val : Model) ∈ X := he.symm ▸ hz.1
    rcases kernel_mask_zero_or_seed X himage hzero hseed m hX with h | h
    · rw [← he,h,kernelValue_zero]
      exact one_mem _
    · rw [← he,h]
      exact mem_zpowers _
  · exact (zpowers_le).mpr ⟨hseed,kernelValue_mem_E 633⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.EightKernel
