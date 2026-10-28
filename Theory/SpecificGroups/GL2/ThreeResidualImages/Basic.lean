module

public import Theory.SpecificGroups.GL2.ThreeQuaternionUniqueness
public import Theory.SpecificGroups.SL2.BinaryTetrahedral
public import Theory.GroupTheory.PResidual.Defs
public import Theory.PGroupCore
public import Theory.ElementaryAbelian.Basic
public import Theory.SpecificGroups.GL2.ThreeConjugacy

/-!
# The determinant-one and quaternion subgroups of GL₂(3)

The determinant kernel is identified with the actual special linear group.
The binary tetrahedral model embeds Q₈, and quaternion uniqueness identifies
its image by the matrices I, -I and the square roots of -I. Two-perfect
images lie in the determinant kernel because the determinant has two-group
codomain. Small power identities are checked on the 81 matrices.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
F.6.16, printed pp.308–309 (combined manuscript, 1 March 2004).
-/

public section
open Matrix Subgroup
namespace Matrix.GeneralLinearGroup
private abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 3)

/-- The canonical determinant-one subgroup of GL₂(3). -/
@[expose] def threeSpecialLinear : Subgroup (GL (Fin 2) (ZMod 3)) := (det (n := Fin 2) (R := ZMod 3)).ker

instance threeSpecialLinear_normal : threeSpecialLinear.Normal := by
  change (det (n := Fin 2) (R := ZMod 3)).ker.Normal
  infer_instance

/-- The canonical equivalence retains each underlying matrix. -/
def threeSpecialLinearEquiv : threeSpecialLinear ≃* SpecialLinearGroup (Fin 2) (ZMod 3) where
  toFun g := ⟨g.val.val, congrArg Units.val g.property⟩
  invFun g := ⟨SpecialLinearGroup.toGL g, SpecialLinearGroup.coeToGL_det g⟩
  left_inv _ := Subtype.ext (Units.ext rfl)
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem three_mem_specialLinear (x : (GL (Fin 2) (ZMod 3))) : x ∈ threeSpecialLinear ↔ x.val.det = 1 := by
  exact ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩

private noncomputable def threeQuaternionHom : QuaternionGroup 2 →* (GL (Fin 2) (ZMod 3)) :=
  SpecialLinearGroup.toGL.comp
    (GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.toMonoidHom.comp
      SemidirectProduct.inl)

private theorem threeQuaternionHom_injective : Function.Injective threeQuaternionHom :=
  SpecialLinearGroup.toGL_injective.comp
    (GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.injective.comp
      SemidirectProduct.inl_injective)

/-- The actual quaternion subgroup embedded via the binary tetrahedral model. -/
noncomputable def threeQuaternion : Subgroup (GL (Fin 2) (ZMod 3)) := threeQuaternionHom.range

/-- The concrete quaternion image is isomorphic to Q₈. -/
noncomputable def threeQuaternionEquiv : threeQuaternion ≃* QuaternionGroup 2 :=
  (MonoidHom.ofInjective threeQuaternionHom_injective).symm

theorem three_mem_quaternion (x : (GL (Fin 2) (ZMod 3))) : x ∈ threeQuaternion ↔
    x.val = 1 ∨ x.val = -1 ∨ x.val ^ 2 = -1 :=
  three_mem_quaternion_iff _ ⟨threeQuaternionEquiv⟩ x

instance threeQuaternion_normal : threeQuaternion.Normal :=
  three_quaternion_subgroup_normal _ ⟨threeQuaternionEquiv⟩

theorem threeQuaternion_card : Nat.card threeQuaternion = 8 := by
  rw [Nat.card_congr threeQuaternionEquiv.toEquiv, Nat.card_eq_fintype_card,
    QuaternionGroup.card]

theorem threeQuaternion_le_specialLinear : threeQuaternion ≤ threeSpecialLinear := by
  rintro x ⟨q, rfl⟩
  exact SpecialLinearGroup.coeToGL_det _

theorem threeQuaternion_isPGroup : IsPGroup 2 threeQuaternion :=
  IsPGroup.of_card (n := 3) threeQuaternion_card

private theorem pPerfect_hom_eq_one {D A : Type*} [Group D] [Group A]
    (hD : IsPPerfect 2 D) (f : D →* A) (hA : IsPGroup 2 A) (d : D) : f d = 1 := by
  have hk : f.ker = ⊤ := hD f.ker inferInstance
    ((hA.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm)
  exact show d ∈ f.ker from hk ▸ mem_top d

theorem three_range_le_specialLinear {D : Type*} [Group D]
    (hD : IsPPerfect 2 D) (f : D →* (GL (Fin 2) (ZMod 3))) : f.range ≤ threeSpecialLinear := by
  rintro x ⟨d, rfl⟩
  exact pPerfect_hom_eq_one hD ((det (n := Fin 2) (R := ZMod 3)).comp f)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_eq_fintype_card]; decide)) d

theorem three_pPerfect_le_specialLinear (K : Subgroup (GL (Fin 2) (ZMod 3))) (hK : IsPPerfect 2 K) :
    K ≤ threeSpecialLinear := by
  simpa only [range_subtype] using three_range_le_specialLinear hK K.subtype

private theorem matrix_pow_twentyFour : ∀ A : M, A.det ≠ 0 → A ^ 24 = 1 := by
  decide +kernel

private theorem matrix_special_pow_twelve : ∀ A : M, A.det = 1 → A ^ 12 = 1 := by
  decide +kernel

private theorem matrix_cubic_det : ∀ A : M, A ^ 3 = 1 → A.det = 1 := by
  decide +kernel

/-- Every ternary invertible matrix has order dividing 24. -/
theorem three_pow_twentyFour (x : (GL (Fin 2) (ZMod 3))) : x ^ 24 = 1 :=
  Units.ext (matrix_pow_twentyFour x.val x.det_ne_zero)

/-- The determinant-one subgroup has exponent dividing 12. -/
theorem three_special_pow_twelve (x : (GL (Fin 2) (ZMod 3))) (hx : x ∈ threeSpecialLinear) : x ^ 12 = 1 :=
  Units.ext (matrix_special_pow_twelve x.val ((three_mem_specialLinear x).mp hx))

/-- Cubic elements have determinant one. -/
theorem three_cubic_mem_specialLinear (x : (GL (Fin 2) (ZMod 3))) (hx : x ^ 3 = 1) :
    x ∈ threeSpecialLinear :=
  (three_mem_specialLinear x).mpr (matrix_cubic_det x.val (congrArg Units.val hx))

/-- The special linear group does not have exponent dividing six. -/
theorem three_special_exists_pow_six_ne : ∃ x ∈ threeSpecialLinear, x ^ 6 ≠ 1 := by
  refine ⟨threeRotation ^ 2, ?_, ?_⟩
  · change det (threeRotation ^ 2) = 1
    decide +kernel
  · decide +kernel

end Matrix.GeneralLinearGroup
