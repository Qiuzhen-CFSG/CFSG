module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FullCoreOrbits
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Invariant

/-!
# Singular point spaces in the full native James action

Each point of the native twenty-two point design defines the annihilator
of its endpoint star in the binary James module. The established point
coordinates give dimension six; a small checked calculation proves that
this space is totally singular. Transitivity transports both statements.

We extend the endpoint action from the perfect triple cover to the full
matrix extension, including its actual outer generator. Its design action
is proved to be the existing automorphism projection. Thus the literal
binary action transports point spaces under the full extension, rather
than only under its derived subgroup.

These spaces provide invariant elementary preimages for the complement
construction in Aschbacher--Segev (4.8), Invent. Math. 105 (1991), p.599,
DOI 10.1007/BF01232280. Their required intersection with the original cocode
subgroup is a separate obligation. Native matrices and point coordinates
are reused from the attributed M22James and CoreProjectiveAction modules.
-/

public section
noncomputable section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint
open Subgroup Sporadic.Mathieu M22TripleCover
open M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open CoreProjectiveAction
open scoped Matrix

private def outerPerm : Equiv.Perm (Fin 22) where
  toFun := ![0,7,15,9,21,13,16,1,8,3,10,11,12,5,14,2,6,20,18,19,17,4]
  invFun := ![0,7,15,9,21,13,16,1,8,3,10,11,12,5,14,2,6,20,18,19,17,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem scalarLine_image_outer (v : BinarySpace) :
    (fun w => Matrix.vecMul w matrixC) '' scalarLine v =
      scalarLine (Matrix.vecMul v matrixC) := by
  have hj : matrixJ * matrixC = matrixC * (1 + matrixJ) := by decide +kernel
  have hc : Matrix.vecMul (Matrix.vecMul v matrixJ) matrixC =
      Matrix.vecMul v matrixC + Matrix.vecMul (Matrix.vecMul v matrixC) matrixJ := by
    rw [Matrix.vecMul_vecMul, hj, ← Matrix.vecMul_vecMul, Matrix.vecMul_add, Matrix.vecMul_one]
  have hz (a b : BinarySpace) : a + (a + b) = b := by
    ext i
    exact CharTwo.add_cancel_left _ _
  simp only [scalarLine, Set.image_insert_eq, Set.image_singleton, Matrix.add_vecMul, hc, hz]
  ext w
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact or_congr Iff.rfl or_comm

set_option maxRecDepth 4000 in
private theorem outer_rows : ∀ i : Fin 231,
    Matrix.vecMul (projectiveVector i) matrixC ∈
      scalarLine (projectiveVector (pairAction outerPerm⁻¹ i)) := by
  simp only [scalarLine, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide +kernel

private theorem compatible_outer : Compatible unitC outerPerm := by
  intro i
  change (fun w => Matrix.vecMul w matrixC) '' _ = _
  rw [scalarLine_image_outer, scalarLine_of_mem (outer_rows i)]

private theorem compatible_full_exists (x : actionGroup) : ∃ p, Compatible x.val p := by
  let S : Submonoid Matrix12ˣ := {
    carrier := {u | ∃ p, Compatible u p}
    one_mem' := ⟨1, compatible_one⟩
    mul_mem' := by
      rintro u v ⟨p,hp⟩ ⟨q,hq⟩
      exact ⟨p*q,compatible_mul hp hq⟩ }
  have hd : unitD = unitC * coreA := by
    change unitD = unitC * (unitC * unitD)
    rw [←mul_assoc, ←pow_two, unitC_pow_two, one_mul]
  have hS : actionGroup.toSubmonoid ≤ S := by
    rw [actionGroup, Subgroup.closure_toSubmonoid_of_isOfFinOrder
      (fun g _ => isOfFinOrder_of_finite g)]
    apply Submonoid.closure_le.mpr
    rintro g (rfl | rfl)
    · exact ⟨outerPerm,compatible_outer⟩
    · exact ⟨outerPerm*corePermA,hd ▸ compatible_mul compatible_outer compatible_A⟩
  exact hS x.property

/-- The full native matrix extension acts on the same twenty-two endpoint stars. -/
def pointAction : actionGroup →* Equiv.Perm (Fin 22) where
  toFun x := Classical.choose (compatible_full_exists x)
  map_one' := compatible_unique (Classical.choose_spec (compatible_full_exists 1)) compatible_one
  map_mul' x y := compatible_unique (Classical.choose_spec (compatible_full_exists (x*y)))
    (compatible_mul (Classical.choose_spec (compatible_full_exists x))
      (Classical.choose_spec (compatible_full_exists y)))

theorem pointAction_spec (g : actionGroup) : Compatible g.val (pointAction g) :=
  Classical.choose_spec (compatible_full_exists g)

theorem pointAction_cover (g : M22TripleCover) :
    pointAction (coverInclusion g) = corePermutationAction g :=
  compatible_unique (pointAction_spec _) (corePermutationAction_spec g)

theorem pointAction_conjugation (g : actionGroup) (a : M22TripleCover) :
    corePermutationAction (derivedConjugation g a) =
      pointAction g * corePermutationAction a * (pointAction g)⁻¹ := by
  rw [← pointAction_cover, ← pointAction_cover]
  have he : coverInclusion (derivedConjugation g a) = g * coverInclusion a * g⁻¹ := rfl
  rw [he,map_mul,map_mul,map_inv]

theorem pointAction_mem_design (g : actionGroup) : pointAction g ∈ m22DesignAut := by
  apply m22_normalizer_le_designAut
  apply mem_normalizer_iff.mpr
  intro x
  have forward (g : actionGroup) (x : Equiv.Perm (Fin 22)) (hx : x ∈ M22) :
      pointAction g * x * (pointAction g)⁻¹ ∈ M22 := by
    obtain ⟨a,rfl⟩ := corePermutationAction_range_eq_M22.symm ▸ hx
    rw [←pointAction_conjugation]
    exact corePermutationAction_range_eq_M22.le ⟨_,rfl⟩
  constructor
  · exact forward g x
  · intro hx
    have hh := forward g⁻¹ _ hx
    simpa only [map_inv,inv_inv,inv_mul_cancel_left,mul_assoc,mul_inv_cancel,inv_mul_cancel,mul_one] using hh

/-- The design action is the original automorphism projection of the matrix extension. -/
theorem pointAction_projection (g : actionGroup) :
    m22DesignAutToAut ⟨pointAction g,pointAction_mem_design g⟩ = quotientConjugation g := by
  apply MulEquiv.ext
  intro a
  obtain ⟨a,rfl⟩ := M22TripleCover.centralQuotientEquiv.surjective a
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (center M22TripleCover) a
  rw [quotientConjugation_apply]
  apply Subtype.ext
  rw [m22DesignAutToAut_apply_perm]
  change pointAction g * corePermutationAction a * (pointAction g)⁻¹ =
    corePermutationAction (derivedConjugation g a)
  exact (pointAction_conjugation g a).symm

/-- The column annihilator of the endpoint star at an arbitrary native point. -/
@[expose] def pointSpace (p : Fin 22) : Submodule (ZMod 2) BinarySpace where
  carrier := {v | ∀ i : Fin 231, p ∈ endpointPair i →
    ∀ w ∈ scalarLine (projectiveVector i), w ⬝ᵥ v = 0}
  zero_mem' := by intro i hi w hw; simp
  add_mem' := by intro v u hv hu i hi w hw; rw [dotProduct_add,hv i hi w hw,hu i hi w hw,add_zero]
  smul_mem' := by intro a v hv i hi w hw; rw [dotProduct_smul,hv i hi w hw,smul_zero]

theorem pointSpace_one : pointSpace 1 = starAnnihilator := rfl

theorem pointSpace_transport (g : actionGroup) (p : Fin 22) (v : BinarySpace)
    (hv : v ∈ pointSpace p) :
    M22TripleCover.Ambient.binaryAction g v ∈ pointSpace (pointAction g p) := by
  intro i hi w hw
  change w ⬝ᵥ (((g.val : Matrix12ˣ) : Matrix12) *ᵥ v) = 0
  rw [Matrix.dotProduct_mulVec]
  have hj : p ∈ endpointPair (pairAction (pointAction g)⁻¹ i) := by
    rw [pairAction_spec]
    exact Finset.mem_image.mpr ⟨pointAction g p,hi,(pointAction g).symm_apply_apply p⟩
  apply hv _ hj
  rw [← pointAction_spec g i]
  exact Set.mem_image_of_mem _ hw

/-- The original column action induces actual coordinates between point spaces. -/
def pointSpaceEquiv (g : actionGroup) (p : Fin 22) :
    pointSpace p ≃ₗ[ZMod 2] pointSpace (pointAction g p) :=
  { (M22TripleCover.Ambient.binaryAction g).restrict (pointSpace_transport g p) with
    invFun := fun v => ⟨M22TripleCover.Ambient.binaryAction g⁻¹ v.val,by
      have hh := pointSpace_transport g⁻¹ (pointAction g p) v.val v.property
      rw [map_inv] at hh
      change M22TripleCover.Ambient.binaryAction g⁻¹ v.val ∈ pointSpace ((pointAction g).symm (pointAction g p)) at hh
      rwa [Equiv.symm_apply_apply] at hh⟩
    left_inv := by
      intro v
      apply Subtype.ext
      change (M22TripleCover.Ambient.binaryAction g⁻¹ * M22TripleCover.Ambient.binaryAction g) v.val = v.val
      rw [←map_mul,inv_mul_cancel,map_one]
      rfl
    right_inv := by
      intro v
      apply Subtype.ext
      change (M22TripleCover.Ambient.binaryAction g * M22TripleCover.Ambient.binaryAction g⁻¹) v.val = v.val
      rw [←map_mul,mul_inv_cancel,map_one]
      rfl }

private theorem point_transporter (p : Fin 22) :
    ∃ g : M22TripleCover, corePermutationAction g 1 = p := by
  let := m22_isPretransitive
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M22 (1 : Fin 22) p
  obtain ⟨a,ha⟩ := M22TripleCover.Uniqueness.quotientMap_surjective g
  exact ⟨a,by change (M22TripleCover.Uniqueness.quotientMap a).val 1=p; rw [ha]; exact hg⟩

theorem pointSpace_finrank (p : Fin 22) : Module.finrank (ZMod 2) (pointSpace p)=6 := by
  obtain ⟨g,hg⟩ := point_transporter p
  have hh := (pointSpaceEquiv (coverInclusion g) 1).finrank_eq
  rw [pointAction_cover,hg,pointSpace_one] at hh
  exact hh.symm.trans invariant_finrank

set_option maxRecDepth 4000 in
private theorem inclusion_singular : ∀ v : Fin 6 → ZMod 2,
    Unitary.quadraticForm (inclusionMatrix *ᵥ v) = 0 := by decide +kernel

theorem pointSpace_singular (p : Fin 22) (v : BinarySpace) (hv : v ∈ pointSpace p) :
    Unitary.quadraticForm v = 0 := by
  obtain ⟨g,hg⟩ := point_transporter p
  let e := pointSpaceEquiv (coverInclusion g) 1
  have hv' : v ∈ pointSpace (pointAction (coverInclusion g) 1) := by rwa [pointAction_cover,hg]
  obtain ⟨u,hu⟩ := e.surjective ⟨v,hv'⟩
  have he : M22TripleCover.binaryRepresentation g u.val=v := congrArg Subtype.val hu
  rw [←he,Unitary.quadraticForm_invariant]
  rw [←inclusion_coordinates u.property]
  exact inclusion_singular _
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint
end
