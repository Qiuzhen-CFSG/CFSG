module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws

/-!
# Concrete standard automorphisms of PSL₃

General linear conjugation preserves the determinant kernel and descends to
`SL₃/Z(SL₃)`. Entrywise field transport and inverse transpose also descend to
this actual projective quotient. Their images generate `standard`; equality
with the full automorphism group is a separate coverage theorem.

The determinant kernel acts by inner automorphisms. Consequently the image
of GL₃ in the outer quotient is abelian: the determinant kills every
commutator. This proves the diagonal part of the solvability argument without
assuming a splitting or certifying simplicity of the matrix group.

Source: GLS3, Theorem 2.5.12(a,b,d,e,i) and the matrix descriptions in §2.7,
`refs/KGroup/GLS3/chapter2.tex`, especially lines 1111–1115. Inverse transpose
is used as a graph representative. The field action reuses the attributed
ATLAS transport in `Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws`;
its source attribution and license are retained in the imported development.
-/

@[expose] public section

open scoped MatrixGroups commutatorElement

namespace Matrix.PSL3.OuterSolvable

variable (F : Type*) [Field F]

/-- The induced action on the actual central quotient of SL₃. -/
def centerAction : MulAut SL(3,F) →* MulAut PSL(3,F) where
  toFun a := QuotientGroup.congr _ _ a
    (Subgroup.characteristic_iff_map_eq.mp inferInstance a)
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) x
    rfl
  map_mul' a b := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) x
    rfl

theorem centerAction_mk (a : MulAut SL(3,F)) (x : SL(3,F)) :
    centerAction F a (QuotientGroup.mk x) = QuotientGroup.mk (a x) := rfl

/-- The determinant kernel in GL₃ is the actual special linear group. -/
def slEquivDetKernel : SL(3,F) ≃*
    (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker where
  toFun x := ⟨SpecialLinearGroup.toGL x, SpecialLinearGroup.coeToGL_det x⟩
  invFun x := ⟨x.val.val, congrArg Units.val x.property⟩
  left_inv _ := rfl
  right_inv _ := Subtype.ext (Units.ext rfl)
  map_mul' x y := Subtype.ext (SpecialLinearGroup.toGL.map_mul x y)

theorem slEquivDetKernel_symm_toGL
    (x : (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker) :
    SpecialLinearGroup.toGL ((slEquivDetKernel F).symm x) = x.val := Units.ext rfl

/-- Conjugation by GL₃, transported from its normal determinant kernel. -/
def linearConjSL : GL (Fin 3) F →* MulAut SL(3,F) :=
  (MulAut.congr (slEquivDetKernel F).symm).toMonoidHom.comp MulAut.conjNormal

theorem linearConjSL_toGL (g : GL (Fin 3) F) (x : SL(3,F)) :
    SpecialLinearGroup.toGL (linearConjSL F g x) =
      g * SpecialLinearGroup.toGL x * g⁻¹ := by
  change SpecialLinearGroup.toGL ((slEquivDetKernel F).symm
    (MulAut.conjNormal g (slEquivDetKernel F x))) = _
  rw [slEquivDetKernel_symm_toGL, MulAut.conjNormal_apply]
  rfl

/-- The inner-diagonal action of GL₃ on PSL₃. -/
def linearConj : GL (Fin 3) F →* MulAut PSL(3,F) :=
  (centerAction F).comp (linearConjSL F)

theorem linearConj_mk (g : GL (Fin 3) F) (x : SL(3,F)) :
    linearConj F g (QuotientGroup.mk x) =
      QuotientGroup.mk (linearConjSL F g x) := rfl

/-- A determinant-one conjugating matrix induces an inner automorphism. -/
theorem linearConj_toGL (x : SL(3,F)) :
    linearConj F (SpecialLinearGroup.toGL x) =
      MulAut.conj (QuotientGroup.mk x) := by
  ext y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) y
  simp only [QuotientGroup.mk'_apply]
  rw [linearConj_mk]
  have h : linearConjSL F (SpecialLinearGroup.toGL x) z = x * z * x⁻¹ := by
    apply SpecialLinearGroup.toGL_injective
    rw [linearConjSL_toGL, map_mul, map_mul, map_inv]
  rw [h]
  rfl

/-- Entrywise coefficient automorphisms, descended through the scalar center. -/
def fieldAction : (F ≃+* F) →* MulAut PSL(3,F) where
  toFun := Atlas.fieldEquivPSL 3
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) x
    rw [Atlas.fieldEquivPSL_mk]
    rfl
  map_mul' a b := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) x
    simp only [MulAut.mul_apply]
    simp only [Atlas.fieldEquivPSL_mk]
    rfl

theorem fieldAction_mk (a : F ≃+* F) (x : SL(3,F)) :
    fieldAction F a (QuotientGroup.mk x) =
      QuotientGroup.mk (SpecialLinearGroup.map a.toRingHom x) :=
  Atlas.fieldEquivPSL_mk 3 a x

private theorem transpose_mul (x y : SL(3,F)) :
    SpecialLinearGroup.transpose (x * y) =
      SpecialLinearGroup.transpose y * SpecialLinearGroup.transpose x := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _

private theorem transpose_transpose (x : SL(3,F)) :
    SpecialLinearGroup.transpose (SpecialLinearGroup.transpose x) = x := by
  apply Subtype.ext
  exact Matrix.transpose_transpose _

private theorem transpose_inv (x : SL(3,F)) :
    SpecialLinearGroup.transpose x⁻¹ = (SpecialLinearGroup.transpose x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← transpose_mul, mul_inv_cancel]
  apply Subtype.ext
  exact Matrix.transpose_one

/-- The inverse-transpose automorphism of SL₃. -/
def graphSL : MulAut SL(3,F) where
  toFun x := (SpecialLinearGroup.transpose x)⁻¹
  invFun x := (SpecialLinearGroup.transpose x)⁻¹
  left_inv x := by
    dsimp only
    rw [transpose_inv, transpose_transpose, inv_inv]
  right_inv x := by
    dsimp only
    rw [transpose_inv, transpose_transpose, inv_inv]
  map_mul' x y := by rw [transpose_mul, _root_.mul_inv_rev]

/-- Inverse transpose on the actual projective quotient. -/
def graph : MulAut PSL(3,F) := centerAction F (graphSL F)

theorem graph_mk (x : SL(3,F)) :
    graph F (QuotientGroup.mk x) =
      QuotientGroup.mk (SpecialLinearGroup.transpose x)⁻¹ := rfl

/-- The graph representative has order dividing two. -/
theorem graph_sq : graph F ^ 2 = 1 := by
  have h : graphSL F ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    change (SpecialLinearGroup.transpose (SpecialLinearGroup.transpose x)⁻¹)⁻¹ = x
    rw [transpose_inv, transpose_transpose, inv_inv]
  rw [graph, ← map_pow, h, map_one]

/-- The image of GL₃ conjugation inside the full automorphism group. -/
def innerDiagonal : Subgroup (MulAut PSL(3,F)) := (linearConj F).range

/-- The subgroup generated by linear, field and graph automorphisms.
This definition makes no assertion of arbitrary-automorphism coverage. -/
def standard : Subgroup (MulAut PSL(3,F)) :=
  innerDiagonal F ⊔ (fieldAction F).range ⊔ Subgroup.zpowers (graph F)

theorem inner_le_innerDiagonal : MulAut.innerSubgroup PSL(3,F) ≤ innerDiagonal F := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) x
  exact ⟨SpecialLinearGroup.toGL y, linearConj_toGL F y⟩

/-- Every inner automorphism belongs to the concrete standard subgroup. -/
theorem inner_le_standard : MulAut.innerSubgroup PSL(3,F) ≤ standard F :=
  (inner_le_innerDiagonal F).trans (le_sup_of_le_left le_sup_left)

theorem linearConj_mem_standard (g : GL (Fin 3) F) : linearConj F g ∈ standard F :=
  (le_sup_of_le_left le_sup_left : innerDiagonal F ≤ standard F) ⟨g, rfl⟩

theorem fieldAction_mem_standard (a : F ≃+* F) : fieldAction F a ∈ standard F :=
  (le_sup_of_le_left le_sup_right : (fieldAction F).range ≤ standard F) ⟨a, rfl⟩

theorem graph_mem_standard : graph F ∈ standard F :=
  (le_sup_right : Subgroup.zpowers (graph F) ≤ standard F) (Subgroup.mem_zpowers _)

/-- The GL₃ action followed by the actual Aut/Inn projection. -/
def linearOuterAction : GL (Fin 3) F →* MulAut.Outer PSL(3,F) :=
  (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))).comp (linearConj F)

/-- The diagonal image inside the actual outer automorphism group. -/
def innerDiagonalOuter : Subgroup (MulAut.Outer PSL(3,F)) :=
  (linearOuterAction F).range

/-- The image of the standard automorphism subgroup in Aut/Inn. -/
def standardOuter : Subgroup (MulAut.Outer PSL(3,F)) :=
  (standard F).map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))

/-- Determinant-one matrices act trivially after quotienting by inner automorphisms. -/
theorem det_ker_le_linearOuterAction_ker :
    (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker ≤ (linearOuterAction F).ker := by
  intro g hg
  let x : SL(3,F) := ⟨g.val, congrArg Units.val hg⟩
  have hx : SpecialLinearGroup.toGL x = g := Units.ext rfl
  change QuotientGroup.mk (linearConj F g) = 1
  rw [← hx, linearConj_toGL, QuotientGroup.eq_one_iff]
  exact ⟨QuotientGroup.mk x, rfl⟩

/-- The diagonal image in the outer group is abelian, by the determinant map. -/
theorem innerDiagonalOuter_isMulCommutative : IsMulCommutative (innerDiagonalOuter F) := by
  refine ⟨⟨?_⟩⟩
  rintro ⟨_, g, rfl⟩ ⟨_, h, rfl⟩
  apply Subtype.ext
  change linearOuterAction F g * linearOuterAction F h =
    linearOuterAction F h * linearOuterAction F g
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  apply det_ker_le_linearOuterAction_ker F
  change GeneralLinearGroup.det ⁅g, h⁆ = 1
  simp [commutatorElement_def]

/-- The diagonal image is therefore solvable. -/
theorem innerDiagonalOuter_isSolvable : Group.IsSolvable (innerDiagonalOuter F) :=
  Group.isSolvable_of_comm (innerDiagonalOuter_isMulCommutative F).is_comm.comm

theorem innerDiagonalOuter_le_standardOuter : innerDiagonalOuter F ≤ standardOuter F := by
  rintro _ ⟨g, rfl⟩
  exact ⟨linearConj F g, linearConj_mem_standard F g, rfl⟩

end Matrix.PSL3.OuterSolvable
