module
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity

/-!
# Lifting a tensor-factor swap through the literal source maps

Transport of natural conjugation through the supplied coordinates gives
linear actions of T and I. The I-action is exactly the original intrinsic
quotient followed by the determinant representation. The ordered matrix
factors consequently have precisely the published symmetric-factor
preimages. Conjugation compatibility then lifts a matrix-factor swap to
those ambient preimages; inversion supplies the source right-conjugation
convention.

The final reduction retains the independent order-eight normalizer theorem
on the fixed binary matrix model. It does not prove that finite-model
statement or assert an unconditional interchange for the source setup.

Source: Aschbacher–Smith, G.2.6(5), printed p.336, and the literal Chapter 15
application 15.3.54(4), printed p.1146.
-/

@[expose] public noncomputable section
open Subgroup
open ClassicalOrthogonal.FourPlusMatrix
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange
open Setup

abbrev MatrixVector := Mat (F := ZMod 2)
abbrev MatrixActor := MatrixVector ≃ₗ[ZMod 2] MatrixVector
abbrev TensorActor := PairSL (F := ZMod 2)
abbrev TensorPlaneActor := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

/-- Binary additive automorphisms are linear; retain the actual underlying functions. -/
def binaryLinearAut : MulAut (Multiplicative MatrixVector) ≃* MatrixActor where
  toFun a :=
    { __ := AddEquiv.toMultiplicative.symm a
      map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm a).toAddMonoidHom }
  invFun f := AddEquiv.toMultiplicative f.toAddEquiv
  left_inv a := by ext v; rfl
  right_inv f := by ext v; rfl
  map_mul' a b := by ext v; rfl

/-- The actual ordered tensor-factor image in the determinant representation. -/
def tensorLeft : Subgroup MatrixActor :=
  (matrixHom.comp (MonoidHom.inl TensorPlaneActor TensorPlaneActor)).range

/-- The second actual ordered tensor-factor image. -/
def tensorRight : Subgroup MatrixActor :=
  (matrixHom.comp (MonoidHom.inr TensorPlaneActor TensorPlaneActor)).range

variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- Coordinate transport of the whole automorphism group of the natural module. -/
def coordinateAut (d : Hypothesis D g) : MulAut D.VL ≃* MatrixActor :=
  (MulAut.congr d.coordinates).trans binaryLinearAut

/-- Literal conjugation by T in determinant coordinates. -/
def tensorT (d : Hypothesis D g) : D.T →* MatrixActor :=
  (coordinateAut d).toMonoidHom.comp
    (D.VL.normalizerMonoidHom.comp (inclusion (Chapter15Collapse.T_normalizes_natural d)))

/-- Literal conjugation by I in determinant coordinates. -/
def tensorI (d : Hypothesis D g) : D.I g →* MatrixActor :=
  (coordinateAut d).toMonoidHom.comp
    (D.VL.normalizerMonoidHom.comp (inclusion d.I_normalizes_VL))

/-- The natural I-action agrees with the original intrinsic quotient, pointwise. -/
theorem tensorI_eq (d : Hypothesis D g) :
    tensorI d = matrixHom.comp
      (d.quotientMatrixEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I g)))) := by
  apply MonoidHom.ext
  intro i
  apply LinearEquiv.ext
  intro v
  have he := d.quotientMatrixEquiv_equivariant i
    (d.coordinates.symm (Multiplicative.ofAdd v))
  apply Multiplicative.ofAdd.injective
  apply d.coordinates.symm.injective
  apply Subtype.ext
  change (d.coordinates.symm (d.coordinates
    (D.VL.normalizerMonoidHom ⟨i, d.I_normalizes_VL i.property⟩
      (d.coordinates.symm (Multiplicative.ofAdd v)))) : G) = _
  rw [d.coordinates.symm_apply_apply, normalizerMonoidHom_apply_apply_coe]
  simpa only [d.coordinates.apply_symm_apply, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, matrixHom, MonoidHom.coe_mk, OneHom.coe_mk,
    MonoidHom.coe_coe, toAdd_ofAdd] using he.symm

/-- Thus the full determinant-action image is the literal I-image. -/
theorem tensorI_range (d : Hypothesis D g) : (tensorI d).range = matrixHom.range := by
  rw [tensorI_eq, MonoidHom.range_comp]
  have hs : Function.Surjective
      (d.quotientMatrixEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I g)))) :=
    d.quotientMatrixEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  rw [MonoidHom.range_eq_top.mpr hs, ← MonoidHom.range_eq_map]

/-- Conjugation is compatible with the literal normalizer actions on both groups. -/
theorem tensor_conjugate (d : Hypothesis D g) (t : D.T) (i : D.I g) :
    tensorI d ((D.I g).normalizerMonoidHom
      ⟨t, (d.LT_normalizes_I_of_star d.star_I_eq_star_LU) (mem_sup_right t.property)⟩ i) =
      tensorT d t * tensorI d i * (tensorT d t)⁻¹ := by
  change (coordinateAut d) _ = (coordinateAut d) _ * (coordinateAut d) _ * ((coordinateAut d) _)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [← map_inv]
  ext v
  change ((t : G) * (i : G) * (t : G)⁻¹) * (v : G) *
      ((t : G) * (i : G) * (t : G)⁻¹)⁻¹ =
    (t : G) * ((i : G) * ((t : G)⁻¹ * (v : G) * ((t : G)⁻¹)⁻¹) * (i : G)⁻¹) * (t : G)⁻¹
  group

/-- T normalizes the actual determinant-action image. -/
theorem tensorT_normalizes (d : Hypothesis D g) :
    (tensorT d).range ≤ normalizer ((matrixHom (F := ZMod 2)).range : Set MatrixActor) := by
  rw [← tensorI_range d]
  apply le_normalizer_iff.mpr
  rintro _ ⟨t, rfl⟩ _ ⟨i, rfl⟩
  exact ⟨_, tensor_conjugate d t i⟩

/-- Coordinate transport preserves the exact order of the natural T-image. -/
theorem tensorT_card (d : Hypothesis D g) :
    Nat.card (tensorT d).range = Nat.card
      (D.VL.normalizerMonoidHom.comp
        (inclusion (Chapter15Collapse.T_normalizes_natural d))).range := by
  rw [tensorT, MonoidHom.range_comp]
  exact card_map_of_injective (coordinateAut d).injective



open InvertedCubicTensor Representation.BinaryQuadraticPair

private theorem matrix_mem_left (p : TensorActor) :
    matrixHom p ∈ tensorLeft ↔
      Hypothesis.pairPermEquiv p ∈ ProductDecomposition.leftFactor := by
  change (∃ a, matrixHom (a, 1) = matrixHom p) ↔ _
  simp only [matrixHom_injective.eq_iff]
  change (∃ a, (a, 1) = p) ↔
    (True ∧ (Hypothesis.pairPermEquiv p).2 = 1)
  have he : (Hypothesis.pairPermEquiv p).2 = 1 ↔ p.2 = 1 :=
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).map_eq_one_iff
  rw [he, true_and]
  constructor
  · rintro ⟨a, rfl⟩; rfl
  · intro h; exact ⟨p.1, Prod.ext rfl h.symm⟩

private theorem matrix_mem_right (p : TensorActor) :
    matrixHom p ∈ tensorRight ↔
      Hypothesis.pairPermEquiv p ∈ ProductDecomposition.rightFactor := by
  change (∃ a, matrixHom (1, a) = matrixHom p) ↔ _
  simp only [matrixHom_injective.eq_iff]
  change (∃ a, (1, a) = p) ↔
    ((Hypothesis.pairPermEquiv p).1 = 1 ∧ True)
  have he : (Hypothesis.pairPermEquiv p).1 = 1 ↔ p.1 = 1 :=
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).map_eq_one_iff
  rw [he, and_true]
  constructor
  · rintro ⟨a, rfl⟩; rfl
  · intro h; exact ⟨p.2, Prod.ext h.symm rfl⟩

/-- The first preimage is marked by the original symmetric quotient map. -/
theorem factorPreimage_left (d : Hypothesis D g) :
    factorPreimage d.quotientSymmetricEquiv ProductDecomposition.leftFactor =
      (tensorLeft.comap (tensorI d)).map (D.I g).subtype := by
  unfold factorPreimage
  congr 1
  ext i
  change moduleProjection d.quotientSymmetricEquiv i ∈ ProductDecomposition.leftFactor ↔
    tensorI d i ∈ tensorLeft
  rw [tensorI_eq]
  change d.quotientSymmetricEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) i) ∈
      ProductDecomposition.leftFactor ↔
    matrixHom (d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) i)) ∈ tensorLeft
  rw [d.quotientSymmetricEquiv_mk, d.quotientMatrixEquiv_mk]
  exact (matrix_mem_left _).symm

/-- The second preimage retains the same ordered matrix-to-symmetric comparison. -/
theorem factorPreimage_right (d : Hypothesis D g) :
    factorPreimage d.quotientSymmetricEquiv ProductDecomposition.rightFactor =
      (tensorRight.comap (tensorI d)).map (D.I g).subtype := by
  unfold factorPreimage
  congr 1
  ext i
  change moduleProjection d.quotientSymmetricEquiv i ∈ ProductDecomposition.rightFactor ↔
    tensorI d i ∈ tensorRight
  rw [tensorI_eq]
  change d.quotientSymmetricEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) i) ∈
      ProductDecomposition.rightFactor ↔
    matrixHom (d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) i)) ∈ tensorRight
  rw [d.quotientSymmetricEquiv_mk, d.quotientMatrixEquiv_mk]
  exact (matrix_mem_right _).symm

/-- A swap of the actual matrix factors lifts through the exact quotient maps.
The inverse of the left-conjugating element gives the source's right conjugation. -/
theorem factorExchange_of_tensor_swap (d : Hypothesis D g) (t : D.T)
    (hswap : tensorLeft.map (MulAut.conj (tensorT d t)).toMonoidHom = tensorRight) :
    FactorExchange d := by
  let c : MulAut (D.I g) := (D.I g).normalizerMonoidHom
    ⟨t, (d.LT_normalizes_I_of_star d.star_I_eq_star_LU) (mem_sup_right t.property)⟩
  have hc : (tensorLeft.comap (tensorI d)).map c.toMonoidHom =
      tensorRight.comap (tensorI d) := by
    apply le_antisymm
    · rintro _ ⟨i, hi, rfl⟩
      change tensorI d (c i) ∈ tensorRight
      rw [tensor_conjugate]
      rw [← hswap]
      exact mem_map_of_mem (MulAut.conj (tensorT d t)).toMonoidHom hi
    · intro i hi
      refine ⟨c.symm i, ?_, c.apply_symm_apply i⟩
      obtain ⟨b, hb, he⟩ := show tensorI d i ∈
          tensorLeft.map (MulAut.conj (tensorT d t)).toMonoidHom from hswap ▸ hi
      have hci := tensor_conjugate d t (c.symm i)
      change tensorI d (c (c.symm i)) = _ at hci
      rw [c.apply_symm_apply] at hci
      have heq : tensorI d (c.symm i) = b :=
        (MulAut.conj (tensorT d t)).injective (hci.symm.trans he.symm)
      change tensorI d (c.symm i) ∈ tensorLeft
      rw [heq]
      exact hb
  refine ⟨(t : G)⁻¹, D.T.inv_mem t.property, ?_⟩
  rw [factorPreimage_left, factorPreimage_right]
  change ((tensorLeft.comap (tensorI d)).map (D.I g).subtype).map
      (MulAut.conj ((t : G)⁻¹)⁻¹).toMonoidHom = _
  rw [inv_inv, map_map, ← hc, map_map]
  rfl

/-- The concrete normalizer calculation is the only remaining input to this
transport theorem. Its premise is a statement about the fixed sixteen-vector
matrix model, independent of the ambient source configuration. -/
theorem factorExchange_of_normalizer_exchange (d : Hypothesis D g)
    (hmodel : ∀ P : Subgroup MatrixActor,
      P ≤ normalizer ((matrixHom (F := ZMod 2)).range : Set MatrixActor) →
      Nat.card P = 8 → ∃ t ∈ P,
        tensorLeft.map (MulAut.conj t).toMonoidHom = tensorRight)
    (hcard : Nat.card (D.VL.normalizerMonoidHom.comp
      (inclusion (Chapter15Collapse.T_normalizes_natural d))).range = 8) :
    FactorExchange d := by
  obtain ⟨u, ⟨t, rfl⟩, ht⟩ := hmodel (tensorT d).range (tensorT_normalizes d)
    ((tensorT_card d).trans hcard)
  exact factorExchange_of_tensor_swap d t ht

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange
