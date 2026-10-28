module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Marking
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Certificates.All
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideReduction
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.InvolutionFibers

/-!
# Internal fusion in the max1-centralizer overgroup

The ten checked odd-product witnesses have all their letters in M ∨ C(v).
Apply the dihedral conjugacy lemma inside this subgroup. The actual kernel
orbits and quotient/fiber coverage then give internal conjugators for every
involution in M, oriented from the seed or pair to that involution.
Source context: GLS3 Table 5.3i and the literal ATLAS J4G1-max1W1 words.
-/
public section
namespace Janko4.AdequateLocal
open Subgroup Cardinality Simplicity.Max1Fusion Max1AmalgamRigidity Certificates
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed

theorem d_mem_C : d ∈ C :=
  transported_mem_C _
    OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.cy_commute_a

theorem x_mem_L : (localX matrixA_mul_self matrixB_pow_four : Model) ∈ L :=
  M_le_L (localX matrixA_mul_self matrixB_pow_four).property

theorem d_mem_L : d ∈ L := C_le_L d_mem_C

theorem outsideRepresentative_mem_L (i : Fin 10) :
    (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model) ∈ L :=
  M_le_L (outsideRepresentative matrixA_mul_self matrixB_pow_four i).property

theorem y_mem_L : y ∈ L :=
  M_le_L (localY matrixA_mul_self matrixB_pow_four).property

theorem word0_mem_L : word0 ∈ L := L.mul_mem c_mem_L y_mem_L

theorem word2_mem_L : word2 ∈ L := L.mul_mem c_mem_L (L.inv_mem y_mem_L)

theorem word1_mem_L : word1 ∈ L := L.mul_mem word2_mem_L c_mem_L

theorem word3_mem_L : word3 ∈ L :=
  L.mul_mem (L.mul_mem (L.inv_mem c_mem_L) (L.inv_mem y_mem_L))
    d_mem_L

theorem word9_mem_L : word9 ∈ L :=
  L.mul_mem (L.mul_mem y_mem_L (L.inv_mem c_mem_L)) (L.inv_mem y_mem_L)

theorem fusionWord_mem_L (i : Fin 10) : fusionWord i ∈ L := by
  fin_cases i
  · exact word0_mem_L
  · exact word1_mem_L
  · exact word2_mem_L
  · exact word3_mem_L
  · exact c_mem_L
  · exact word2_mem_L
  · exact word1_mem_L
  · exact word2_mem_L
  · exact word2_mem_L
  · exact word9_mem_L

theorem fusionTarget_eq (i : Fin 10) : fusionTarget i = seed ∨ fusionTarget i = pair := by
  fin_cases i
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fusionTarget_mem_L (i : Fin 10) : fusionTarget i ∈ L := by
  rcases fusionTarget_eq i with h | h
  · rw [h]; exact seed_mem_L
  · rw [h]; exact pair_mem_L

theorem fusionTarget_sq (i : Fin 10) : fusionTarget i ^ 2 = 1 := by
  rcases fusionTarget_eq i with h | h
  · rw [h]; exact seed_sq
  · rw [h]; exact pair_sq

theorem outsideRepresentative_sq (i : Fin 10) :
    (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model) ^ 2 = 1 := by
  fin_cases i
  · change (outsideRepresentative matrixA_mul_self matrixB_pow_four 0 : Model) ^ 2 = 1
    have he : outsideRepresentative matrixA_mul_self matrixB_pow_four 0 =
        localX matrixA_mul_self matrixB_pow_four := by
      simp [outsideRepresentative, outsideMask, KernelCount.binaryProduct_zero]
    rw [he]
    obtain ⟨g, hg⟩ := localX_fuses_first matrixA_mul_self matrixB_pow_four
    apply (MulAut.conj g).injective
    rw [map_pow, map_one]
    change (g * (localX matrixA_mul_self matrixB_pow_four : Model) * g⁻¹) ^ 2 = 1
    rw [← hg]
    exact a_pow_two
  · exact OutsideWordCertificates.square_1 _ _
  · exact OutsideWordCertificates.square_2 _ _
  · exact OutsideWordCertificates.square_3 _ _
  · exact OutsideWordCertificates.square_4 _ _
  · exact OutsideWordCertificates.square_5 _ _
  · exact OutsideWordCertificates.square_6 _ _
  · exact OutsideWordCertificates.square_7 _ _
  · exact OutsideWordCertificates.square_8 _ _
  · exact OutsideWordCertificates.square_9 _ _

/-- Each of the ten words fuses internally, using the actual packed certificate. -/
theorem outside_internal_fusion (i : Fin 10) :
    ∃ l : L, MulAut.conj (l : Model) (fusionTarget i) =
      (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model) := by
  let r : L := ⟨_, outsideRepresentative_mem_L i⟩
  let t : L := ⟨fusionTarget i, fusionTarget_mem_L i⟩
  let w : L := ⟨fusionWord i, fusionWord_mem_L i⟩
  have hr : r ^ 2 = 1 := Subtype.ext (outsideRepresentative_sq i)
  have ht : t ^ 2 = 1 := Subtype.ext (fusionTarget_sq i)
  have hwt : (w * t * w⁻¹) ^ 2 = 1 := by
    change (MulAut.conj w t) ^ 2 = 1
    rw [← map_pow, ht, map_one]
  have hp : (r * (w * t * w⁻¹)) ^ fusionExponent i = 1 :=
    Subtype.ext (all_odd_product_certificates i)
  have hc := isConj_of_involutions_odd_product r (w * t * w⁻¹) hr hwt
    ((fusionExponent_odd i).of_dvd_nat (orderOf_dvd_of_pow_eq_one hp))
  have hw : IsConj t (w * t * w⁻¹) := isConj_iff.mpr ⟨w, rfl⟩
  obtain ⟨l, hl⟩ := isConj_iff.mp (hw.trans hc.symm)
  exact ⟨l, congrArg L.subtype hl⟩

/-- Coverage uses conjugators in the generated subgroup, not merely in Model. -/
theorem max1_internal_fusion (z : Model) (hz : z ∈ M) (ho : orderOf z = 2) :
    ∃ l : L, MulAut.conj (l : Model) seed = z ∨ MulAut.conj (l : Model) pair = z := by
  let zM : M := ⟨z, hz⟩
  have hz2 : orderOf zM = 2 := (Subgroup.orderOf_coe zM).symm.trans ho
  by_cases hk : zM ∈ K
  · obtain ⟨g, hg | hg⟩ := kernel_involution_orbits
      matrixA_mul_self matrixB_pow_four zM hk hz2
    · let gL : L := ⟨g, M_le_L g.property⟩
      have he : seed = (g : Model) * z * (g : Model)⁻¹ := congrArg M.subtype hg
      refine ⟨gL⁻¹, Or.inl ?_⟩
      change (g : Model)⁻¹ * seed * ((g : Model)⁻¹)⁻¹ = z
      rw [he]
      simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    · let gL : L := ⟨g, M_le_L g.property⟩
      have he : pair = (g : Model) * z * (g : Model)⁻¹ := congrArg M.subtype hg
      refine ⟨gL⁻¹, Or.inr ?_⟩
      change (g : Model)⁻¹ * pair * ((g : Model)⁻¹)⁻¹ = z
      rw [he]
      simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  · obtain ⟨i, g, hg⟩ := outside_coverage_of_quotient_and_fibers
      matrixA_mul_self matrixB_pow_four
      (quotient_involution_coverage _ _) (involution_fibers _ _) zM hk hz2
    obtain ⟨l, hl⟩ := outside_internal_fusion i
    let gL : L := ⟨g, M_le_L g.property⟩
    have he : (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model) =
        (g : Model) * z * (g : Model)⁻¹ := congrArg M.subtype hg
    have hf : MulAut.conj ((gL⁻¹ * l : L) : Model) (fusionTarget i) = z := by
      calc
        _ = MulAut.conj (g : Model)⁻¹ (MulAut.conj (l : Model) (fusionTarget i)) := by
          simp only [gL, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
            mul_inv_rev, inv_inv, mul_assoc]
        _ = z := by
          rw [hl, he]
          simp only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
            inv_mul_cancel, mul_one]
    refine ⟨gL⁻¹ * l, ?_⟩
    rcases fusionTarget_eq i with h | h
    · exact Or.inl (h ▸ hf)
    · exact Or.inr (h ▸ hf)

end Janko4.AdequateLocal
