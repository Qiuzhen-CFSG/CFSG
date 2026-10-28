module
public import Theory.SpecificGroups.Monster.Construction.LocalC.Descent
public import Theory.SpecificGroups.Monster.Construction.LocalC.N1Embedding

/-!
# Actual extraspecial conjugation and the central block involution

The local quotient embeds faithfully in the fixed tensor image. Its
extraspecial subgroup acts by the original spin operators, and the
descended automorphism is actual conjugation of this embedded subgroup.
Consequently the short-vector action is the source signed conjugation
formula. The specified nonidentity central involution acts as minus
identity on the tensor summand and identity on the other two summands;
its fixed space is exactly their sum.

The construction here uses the orthogonal spin normalizer from `Pullback`.
Its identification with the source determinant-one normalizer is a separate
remaining obligation, not an assumption of these action and kernel proofs.

Source: Aschbacher, *Sporadic Groups*, Section 27, printed pp. 148–150,
especially the definition of `Bᵣ` and Lemma 27.9.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct
open Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

/-- `Q1` acts trivially on the integral natural factor, not just on its binary quotient. -/
theorem n1LeechRepresentation_of_mem_Q1 (g : N1) (hg : g.val ∈ Q1) :
    n1LeechRepresentation g = 1 :=
  natural_lift_unique g _ 1 (n1LeechRepresentation_natural g)
    (fun v => by rw [map_one, NaturalAction.representation_of_mem_Q1 g hg]; rfl)

theorem n1LeechRepresentation_z : n1LeechRepresentation SpinAction.z = 1 :=
  n1LeechRepresentation_of_mem_Q1 _ z1N_mem_Q1

theorem q1ImageConjugation_z : q1ImageConjugation SpinAction.z = 1 := by
  apply MulEquiv.ext
  intro q
  apply SpinAction.imageRepresentation_faithful
  apply LinearMap.ext
  intro v
  have h := n1SpinEquiv_intertwines SpinAction.z q v
  simp only [n1SpinEquiv_apply, SpinAction.representation_z, map_neg] at h
  exact neg_injective h.symm

theorem cShort_z1C : cShort z1C = 1 := by
  change cShort (pullbackToC (n1Pullback SpinAction.z)) = 1
  rw [cShort_pullback]
  apply (shortAction_kernel_iff sourceLatticeComparison
    (pullbackCompatible (n1Pullback SpinAction.z))).mpr
  intro q
  change q1ImageConjugation SpinAction.z q.val = q.val
  rw [q1ImageConjugation_z]
  rfl

theorem cSymmetric_z1C : cSymmetric z1C = 1 := by
  change cSymmetric (pullbackToC (n1Pullback SpinAction.z)) = 1
  rw [cSymmetric_pullback]
  change (symmetricLeechRepresentation (n1LeechRepresentation SpinAction.z)).toLinearMap = 1
  rw [n1LeechRepresentation_z, map_one]
  rfl

/-- The actual distinguished involution has exactly the source block signs. -/
theorem cRepresentation_z1C (v : B) :
    cRepresentation z1C v = parityEquiv sourceLatticeComparison v := by
  rw [cRepresentation_apply, z1C_minus, cShort_z1C, cSymmetric_z1C]
  rfl

theorem z1C_square : z1C ^ 2 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change z1C.val (z1C.val v) = v
  rw [z1C_minus, z1C_minus, neg_neg]

theorem z1C_central (g : C) : z1C * g = g * z1C := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change z1C.val (g.val v) = g.val (z1C.val v)
  rw [z1C_minus, z1C_minus, map_neg]

theorem z1C_ne_one : z1C ≠ 1 := by
  intro h
  let : Nontrivial MinusSpace := Module.nontrivial_of_finrank_pos
    (by rw [minusSpace_finrank]; norm_num)
  obtain ⟨v,hv⟩ := exists_ne (0 : MinusSpace)
  have he : parityEquiv sourceLatticeComparison (v,0,0) = (v,0,0) := by
    rw [← cRepresentation_z1C, h, map_one]
    rfl
  exact hv ((parity_fixed_iff sourceLatticeComparison (v,0,0)).mp he)

/-- Source 27.9: the fixed space is precisely the sum of the last two summands. -/
theorem cRepresentation_z1C_fixed_iff (v : B) : cRepresentation z1C v = v ↔ v.1 = 0 := by
  rw [cRepresentation_z1C]
  exact parity_fixed_iff sourceLatticeComparison v

/-- The extraspecial automorphism projection before descent. -/
def pullbackConjugation : localPullback →* MulAut Q1Image where
  toFun p := p.val.1.val.2
  map_one' := rfl
  map_mul' _ _ := rfl

theorem pullbackToC_kernel_le_conjugation : pullbackToC.ker ≤ pullbackConjugation.ker := by
  intro p hp
  apply MulEquiv.ext
  exact pullbackTensor_kernel_automorphism p (congrArg Subtype.val hp)

/-- The induced action on the actual extraspecial group. -/
def cConjugation : C →* MulAut Q1Image :=
  tensorDescend pullbackConjugation pullbackToC_kernel_le_conjugation

@[simp] theorem cConjugation_pullback (p : localPullback) :
    cConjugation (pullbackToC p) = p.val.1.val.2 := tensorDescend_pullback _ _ p

/-- The canonical map from the local subgroup of `N/K` into the tensor image. -/
def n1ImageToC : N1Image →* C := n1QuotientToC.comp n1QuotientEquivImage.symm.toMonoidHom

theorem n1ImageToC_map (g : N1) : n1ImageToC (n1ImageMap g) = n1ToC g := by
  change n1QuotientToC (n1QuotientEquivImage.symm (n1ImageMap g)) = _
  rw [← n1QuotientEquivImage_mk, n1QuotientEquivImage.symm_apply_apply]
  rfl

/-- The source extraspecial subgroup inside `C`. -/
def q1ToC : Q1Image →* C := n1ImageToC.comp (Subgroup.inclusion Q1Image_le_N1Image)

theorem q1ToC_faithful : Function.Injective q1ToC :=
  (n1QuotientToC_faithful.comp n1QuotientEquivImage.symm.injective).comp
    (Subgroup.inclusion_injective Q1Image_le_N1Image)

theorem q1ToC_image (q : Q1) : q1ToC (q1ImageMap q) = n1ToC (SpinAction.q1Inclusion q) :=
  n1ImageToC_map (SpinAction.q1Inclusion q)

/-- The central involution is the image of the specified extraspecial center. -/
theorem q1ToC_center : q1ToC q1ImageCenterGenerator = z1C :=
  q1ToC_image ⟨z1N,z1N_mem_Q1⟩

/-- The extraspecial subgroup acts by the actual spin action on the second tensor factor. -/
theorem q1ToC_tmul (q : Q1Image) (a : NaturalSpace) (b : SpinSpace) :
    (q1ToC q).val (a ⊗ₜ[ℝ] b) = a ⊗ₜ[ℝ] SpinAction.imageRepresentation q b := by
  obtain ⟨q,rfl⟩ := q1ImageMap_surjective q
  rw [q1ToC_image, SpinAction.imageRepresentation_map]
  change realLeechRepresentation (n1LeechRepresentation (SpinAction.q1Inclusion q)) a ⊗ₜ[ℝ]
    SpinAction.q1Representation q b = _
  rw [n1LeechRepresentation_of_mem_Q1 _ q.prop, map_one]
  rfl

/-- The descended automorphism is actual conjugation of the embedded extraspecial subgroup. -/
theorem q1ToC_conjugation (g : C) (q : Q1Image) :
    q1ToC (cConjugation g q) = g * q1ToC q * g⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  obtain ⟨p,rfl⟩ := pullbackToC_surjective g
  rw [cConjugation_pullback]
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro a b
  change (q1ToC (p.val.1.val.2 q)).val (pullbackTensor p (a ⊗ₜ[ℝ] b)) =
    pullbackTensor p ((q1ToC q).val (a ⊗ₜ[ℝ] b))
  rw [pullbackTensor_tmul, q1ToC_tmul, q1ToC_tmul, pullbackTensor_tmul, p.val.1.prop.1]

/-- Normality is in the constructed local group, witnessed by actual conjugation. -/
theorem q1ToC_range_normal : q1ToC.range.Normal := by
  constructor
  intro x hx g
  obtain ⟨q,rfl⟩ := hx
  exact ⟨cConjugation g q, q1ToC_conjugation g q⟩

/-- Short elements remain short under the actual conjugation action. -/
def cShortLift (g : C) (q : ShortLift sourceLatticeComparison) : ShortLift sourceLatticeComparison :=
  ⟨cConjugation g q.val, by
    obtain ⟨p,rfl⟩ := pullbackToC_surjective g
    rw [cConjugation_pullback]
    exact (shortLiftPermutation sourceLatticeComparison (pullbackCompatible p) q).prop⟩

/-- The source formula `y(r) ↦ y(g r g⁻¹)` on the fixed signed basis. -/
theorem cShort_vector (g : C) (q : ShortLift sourceLatticeComparison) :
    cShort g (shortVector sourceLatticeComparison q) =
      shortVector sourceLatticeComparison (cShortLift g q) := by
  obtain ⟨p,rfl⟩ := pullbackToC_surjective g
  rw [cShort_pullback]
  change shortAction sourceLatticeComparison (pullbackCompatible p)
    (shortVector sourceLatticeComparison q) = _
  rw [shortAction_vector]
  congr 1
  apply Subtype.ext
  exact (congrArg (fun f : MulAut Q1Image => f q.val) (cConjugation_pullback p)).symm

end Sporadic.Monster.Construction.LocalC
