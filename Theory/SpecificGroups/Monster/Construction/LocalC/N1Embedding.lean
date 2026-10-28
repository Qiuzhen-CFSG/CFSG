module
public import Theory.SpecificGroups.Monster.Construction.LocalC.Pullback
public import Theory.SpecificGroups.Monster.Construction.LocalC.N1Equivariance
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.TensorAction

/-!
# The faithful triality quotient inside the spin–Leech tensor image

Actual conjugation on `Q1` descends to its extraspecial image in `N/K`.
The faithful spin representation realizes this conjugation, and the full
natural-module comparison supplies the matching integral Leech action.
Thus `N1` maps into the fixed pullback. Transporting the proved triality
tensor kernel identifies the kernel of its map into `C` with `K`, giving
an injective homomorphism from the literal quotient `N1/K`. The specified
central element acts by minus identity on the tensor summand.

Source: Aschbacher, *Sporadic Groups*, Lemmas 27.5–27.6 and printed p. 149.
The source determinant-normalizer identification remains separate.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct
open Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

/-- Actual conjugation in `N/K`, restricted to the relatively normal extraspecial group. -/
def q1ImageConjugation : N1 →* MulAut Q1Image where
  toFun g :=
    { toFun q := ⟨(n1ImageMap g).val * q.val * (n1ImageMap g).val⁻¹,
        Q1Image_normal_in_N1Image.conj_mem
          (⟨q.val,Q1Image_le_N1Image q.prop⟩ : N1Image) q.prop (n1ImageMap g)⟩
      invFun q := ⟨(n1ImageMap g).val⁻¹ * q.val * (n1ImageMap g).val, by
        have h := Q1Image_normal_in_N1Image.conj_mem
          (⟨q.val,Q1Image_le_N1Image q.prop⟩ : N1Image) q.prop (n1ImageMap g)⁻¹
        change (n1ImageMap g).val⁻¹ * q.val * ((n1ImageMap g).val⁻¹)⁻¹ ∈ Q1Image at h
        simpa only [inv_inv] using h⟩
      left_inv q := by apply Subtype.ext; simp [mul_assoc]
      right_inv q := by apply Subtype.ext; simp [mul_assoc]
      map_mul' q r := by apply Subtype.ext; simp [mul_assoc] }
  map_one' := by apply MulEquiv.ext; intro q; apply Subtype.ext; simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro q
    apply Subtype.ext
    simp [map_mul, mul_assoc]

theorem q1ImageConjugation_image (g : N1) (q : Q1) :
    q1ImageConjugation g (q1ImageMap q) = q1ImageMap (q1Conjugation g q) := by
  apply Subtype.ext
  change nQuotientMap g.val * nQuotientMap q.val * (nQuotientMap g.val)⁻¹ =
    nQuotientMap (g.val * q.val * g.val⁻¹)
  simp only [map_mul, map_inv]

/-- Equivariance on the actual extraspecial image, using the fixed source comparison. -/
theorem latticeClass_equivariant (g : N1) (q : Q1Image) :
    latticeClass sourceLatticeComparison (q1ImageConjugation g q) =
      leechModTwoRepresentation (n1LeechRepresentation g)
        (latticeClass sourceLatticeComparison q) := by
  obtain ⟨q,rfl⟩ := q1ImageMap_surjective q
  rw [q1ImageConjugation_image, sourceLatticeClass_image, sourceLatticeClass_image]
  exact sourceQ1LatticeHom_equivariant g q

/-- The genuine spin representation as invertible linear maps. -/
def n1SpinEquiv : N1 →* (SpinSpace ≃ₗ[ℝ] SpinSpace) where
  toFun g :=
    { toLinearMap := SpinAction.representation g
      invFun := SpinAction.representation g⁻¹
      left_inv v := by
        change (SpinAction.representation g⁻¹ * SpinAction.representation g) v = v
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv v := by
        change (SpinAction.representation g * SpinAction.representation g⁻¹) v = v
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by apply LinearEquiv.toLinearMap_injective; exact map_one SpinAction.representation
  map_mul' g h := by
    apply LinearEquiv.toLinearMap_injective
    exact map_mul SpinAction.representation g h

@[simp] theorem n1SpinEquiv_apply (g : N1) (v : SpinSpace) :
    n1SpinEquiv g v = SpinAction.representation g v := rfl

/-- Conjugation on the extraspecial image is realized by the actual spin action. -/
theorem n1SpinEquiv_intertwines (g : N1) (q : Q1Image) (v : SpinSpace) :
    n1SpinEquiv g (SpinAction.imageRepresentation q v) =
      SpinAction.imageRepresentation (q1ImageConjugation g q) (n1SpinEquiv g v) := by
  obtain ⟨q,rfl⟩ := q1ImageMap_surjective q
  rw [q1ImageConjugation_image, SpinAction.imageRepresentation_map,
    SpinAction.imageRepresentation_map]
  change SpinAction.representation g (SpinAction.representation (SpinAction.q1Inclusion q) v) =
    SpinAction.representation (SpinAction.q1Inclusion (q1Conjugation g q))
      (SpinAction.representation g v)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  have h : g * SpinAction.q1Inclusion q = SpinAction.q1Inclusion (q1Conjugation g q) * g := by
    apply Subtype.ext
    change g.val * q.val = (g.val * q.val * g.val⁻¹) * g.val
    simp [mul_assoc]
  rw [h]

/-- The fixed triality map into the orthogonal spin normalizer. -/
def n1SpinNormalizer : N1 →* spinNormalizer where
  toFun g := ⟨(n1SpinEquiv g,q1ImageConjugation g),
    ⟨n1SpinEquiv_intertwines g,SpinAction.representation_isometry g⟩⟩
  map_one' := by apply Subtype.ext; exact Prod.ext (map_one _) (map_one _)
  map_mul' g h := by apply Subtype.ext; exact Prod.ext (map_mul _ g h) (map_mul _ g h)

/-- The two genuine actions give the source pullback homomorphism. -/
def n1Pullback : N1 →* localPullback where
  toFun g := ⟨(n1SpinNormalizer g,n1LeechRepresentation g), latticeClass_equivariant g⟩
  map_one' := by apply Subtype.ext; exact Prod.ext (map_one _) (map_one _)
  map_mul' g h := by apply Subtype.ext; exact Prod.ext (map_mul _ g h) (map_mul _ g h)

/-- The triality homomorphism into the tensor image. -/
def n1ToC : N1 →* C := pullbackToC.comp n1Pullback

/-- The natural marking identifies the source tensor carrier with `B₋`. -/
def naturalTensorComparison : TensorAction.Space ≃ₗ[ℝ] MinusSpace :=
  TensorProduct.congr naturalLeechComparison (LinearEquiv.refl ℝ SpinSpace)

theorem n1ToC_intertwines (g : N1) (v : TensorAction.Space) :
    (n1ToC g).val (naturalTensorComparison v) =
      naturalTensorComparison (TensorAction.representation g v) := by
  have h : (n1ToC g).val.toLinearMap.comp naturalTensorComparison.toLinearMap =
      naturalTensorComparison.toLinearMap.comp (TensorAction.representation g) := by
    apply TensorProduct.ext'
    intro a b
    change realLeechRepresentation (n1LeechRepresentation g) (naturalLeechComparison a) ⊗ₜ[ℝ]
      SpinAction.representation g b =
      naturalLeechComparison (NaturalAction.representation g a) ⊗ₜ[ℝ]
        SpinAction.representation g b
    rw [n1LeechRepresentation_natural]
  exact congrArg (fun f : TensorAction.Space →ₗ[ℝ] MinusSpace => f v) h

/-- The tensor map kills exactly the prescribed four-group. -/
theorem n1ToC_kernel : n1ToC.ker = K.subgroupOf N1 := by
  rw [← TensorAction.representation_kernel]
  ext g
  change n1ToC g = 1 ↔ TensorAction.representation g = 1
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    apply naturalTensorComparison.injective
    rw [← n1ToC_intertwines, h]
    rfl
  · intro h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := naturalTensorComparison.surjective w
    rw [n1ToC_intertwines, h]
    rfl

/-- The faithful inclusion of the actual local quotient `N1/K`. -/
def n1QuotientToC : N1Quotient →* C :=
  QuotientGroup.lift (K.subgroupOf N1) n1ToC n1ToC_kernel.ge

theorem n1QuotientToC_faithful : Function.Injective n1QuotientToC :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr n1ToC_kernel.symm

@[simp] theorem n1QuotientToC_mk (g : N1) :
    n1QuotientToC (QuotientGroup.mk' (K.subgroupOf N1) g) = n1ToC g := rfl

/-- The specified involution in the tensor image. -/
def z1C : C := n1ToC SpinAction.z

theorem z1C_minus (v : MinusSpace) : z1C.val v = -v := by
  obtain ⟨w,rfl⟩ := naturalTensorComparison.surjective v
  rw [z1C, n1ToC_intertwines, TensorAction.representation_z]
  change naturalTensorComparison (-w) = -naturalTensorComparison w
  exact map_neg naturalTensorComparison w

end Sporadic.Monster.Construction.LocalC
