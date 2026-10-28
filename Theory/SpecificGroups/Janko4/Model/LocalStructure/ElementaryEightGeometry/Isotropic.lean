module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Fusion.Geometry
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Nondegenerate

/-!
# A native totally isotropic four-space

Three even sums of the fixed kernel basis and the Figure 1 pair lift span
an elementary group with zero intrinsic form. These are the coefficient
vectors 3, 5, 9, 128 in the native (b) eight. This identifies the candidate
for the normalizer-invariant subspace required by KW (1988), Corollary 2.3.6;
its invariance requires the separate native representation calculation.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup LargeCenterRadicals.OuterHalf
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB nativeMask correctedLift

/-- Three even kernel sums and the original pair lift. -/
def isotropicVector : Fin 4 → Additive (nativeEight 0) :=
  ![kernelVector 0 0 + kernelVector 0 1,
    kernelVector 0 0 + kernelVector 0 2,
    kernelVector 0 0 + kernelVector 0 3,
    liftVector 0 3]

theorem isotropicVector_pairing (i j : Fin 4) :
    intrinsicElementaryForm (nativeEight 0) (isotropicVector i) (isotropicVector j) = 0 := by
  have hk (i : Fin 4) :
      intrinsicElementaryForm (nativeEight 0) (kernelVector 0 i) (liftVector 0 3) = 1 := by
    rw [nativeEight_pairing]
    fin_cases i <;> rfl
  have hl (i : Fin 4) :
      intrinsicElementaryForm (nativeEight 0) (liftVector 0 3) (kernelVector 0 i) = 1 := by
    rw [(intrinsicElementaryForm_isSymm (nativeEight 0)).eq]
    exact hk i
  have haa := intrinsicElementaryForm_isAlt (nativeEight 0) (liftVector 0 3)
  fin_cases i <;> fin_cases j <;>
    simp only [isotropicVector, Matrix.cons_val_zero', Matrix.cons_val_succ',
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      nativeEight_kernel_pairing, hk, hl, haa, add_zero]
  all_goals decide

def isotropicSpace : Submodule (ZMod 2) (Additive (nativeEight 0)) :=
  Submodule.span (ZMod 2) (Set.range isotropicVector)

/-- Linear coordinates in the four explicit isotropic generators. -/
def isotropicCoordinates : (Fin 4 → ZMod 2) →ₗ[ZMod 2] Additive (nativeEight 0) :=
  Fintype.linearCombination (ZMod 2) isotropicVector

private theorem isotropicCoordinates_eq (v : Fin 4 → ZMod 2) :
    isotropicCoordinates v = eightCoordinates 0
      (![v 0 + v 1 + v 2,v 0,v 1,v 2], ![0,0,0,v 3]) := by
  simp only [isotropicCoordinates,Fintype.linearCombination_apply,eightCoordinates,
    kernelSum,liftSum,Fin.sum_univ_succ,isotropicVector,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Fin.sum_univ_zero,add_zero,zero_smul,zero_add,smul_add,add_smul]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, show (2 : Fin 3).succ = 3 from rfl]
  change (v 0 • kernelVector 0 0 + v 0 • kernelVector 0 1) +
      ((v 1 • kernelVector 0 0 + v 1 • kernelVector 0 2) +
        ((v 2 • kernelVector 0 0 + v 2 • kernelVector 0 3) + v 3 • liftVector 0 3)) =
    ((v 0 • kernelVector 0 0 + v 1 • kernelVector 0 0) + v 2 • kernelVector 0 0) +
      (v 0 • kernelVector 0 1 + (v 1 • kernelVector 0 2 + v 2 • kernelVector 0 3)) +
        v 3 • liftVector 0 3
  abel

theorem isotropicCoordinates_injective : Function.Injective isotropicCoordinates := by
  intro v w h
  rw [isotropicCoordinates_eq,isotropicCoordinates_eq] at h
  have he := eightCoordinates_injective 0 h
  funext i
  fin_cases i
  · exact congrArg (fun u => u.1 1) he
  · exact congrArg (fun u => u.1 2) he
  · exact congrArg (fun u => u.1 3) he
  · exact congrArg (fun u => u.2 3) he

theorem isotropicCoordinates_range : LinearMap.range isotropicCoordinates = isotropicSpace :=
  Fintype.range_linearCombination (ZMod 2) isotropicVector

def isotropicSubgroup : Subgroup Model :=
  isotropicSpace.toAddSubgroup.toSubgroup'.map (nativeEight 0).subtype

theorem isotropicSubgroup_le : isotropicSubgroup ≤ nativeEight 0 := map_subtype_le _

instance isotropicSubgroup_elementary : IsElementaryAbelian 2 isotropicSubgroup :=
  IsElementaryAbelian.of_le isotropicSubgroup_le

private theorem space_pairing (x y : Additive (nativeEight 0))
    (hx : x ∈ isotropicSpace) (hy : y ∈ isotropicSpace) :
    intrinsicElementaryForm (nativeEight 0) x y = 0 := by
  have hgen (i : Fin 4) : intrinsicElementaryForm (nativeEight 0) (isotropicVector i) y = 0 := by
    apply Submodule.span_induction (p := fun y _ =>
      intrinsicElementaryForm (nativeEight 0) (isotropicVector i) y = 0) _ _ _ _ hy
    · rintro _ ⟨j,rfl⟩; exact isotropicVector_pairing i j
    · exact map_zero _
    · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
    · intro a b _ hb; rw [map_smul, hb, smul_zero]
  apply Submodule.span_induction (p := fun x _ =>
    intrinsicElementaryForm (nativeEight 0) x y = 0) _ _ _ _ hx
  · rintro _ ⟨i,rfl⟩; exact hgen i
  · exact LinearMap.BilinForm.zero_left _
  · intro a b _ _ ha hb; rw [LinearMap.BilinForm.add_left,ha,hb,add_zero]
  · intro a b _ hb; rw [LinearMap.BilinForm.smul_left,hb,mul_zero]

theorem isotropicSubgroup_form_zero : intrinsicElementaryForm isotropicSubgroup = 0 := by
  ext x y
  obtain ⟨a,ha,he⟩ := x.toMul.property
  obtain ⟨b,hb,hf⟩ := y.toMul.property
  change outerValue (x.toMul : Model) (y.toMul : Model) = 0
  rw [← he,← hf]
  exact space_pairing (Additive.ofMul a) (Additive.ofMul b) ha hb

theorem isotropicSubgroup_ne_bot : isotropicSubgroup ≠ ⊥ := by
  intro h
  have hm : ((isotropicVector 0).toMul : Model) ∈ isotropicSubgroup := by
    change ((isotropicVector 0).toMul : Model) ∈
      isotropicSpace.toAddSubgroup.toSubgroup'.map (nativeEight 0).subtype
    refine ⟨(isotropicVector 0).toMul, ?_, rfl⟩
    change isotropicVector 0 ∈ isotropicSpace
    exact Submodule.subset_span (Set.mem_range_self 0)
  rw [h,mem_bot] at hm
  have hz : isotropicVector 0 = 0 := Additive.toMul.injective (Subtype.ext hm)
  have hp : intrinsicElementaryForm (nativeEight 0) (isotropicVector 0) (liftVector 0 0) = 1 := by
    simp only [isotropicVector, Matrix.cons_val_zero, LinearMap.BilinForm.add_left,
      nativeEight_pairing]
    rfl
  rw [hz,LinearMap.BilinForm.zero_left] at hp
  exact zero_ne_one hp

/-- The concrete zero-form subgroup has the full expected order sixteen. -/
theorem isotropicSubgroup_card : Nat.card isotropicSubgroup = 16 := by
  rw [isotropicSubgroup,card_map_of_injective (nativeEight 0).subtype_injective]
  change Nat.card isotropicSpace = 16
  rw [← isotropicCoordinates_range]
  have he := LinearEquiv.ofInjective isotropicCoordinates isotropicCoordinates_injective
  rw [← Nat.card_congr he.toEquiv,Nat.card_fun,Nat.card_zmod,Nat.card_fin]
  decide


private theorem zero_form_map (A : Subgroup Model) [IsElementaryAbelian 2 A]
    (e : Model ≃* Model) (hA : intrinsicElementaryForm A = 0) :
    letI := IsElementaryAbelian.map (p := 2) e.toMonoidHom (A := A)
    intrinsicElementaryForm (A.map e.toMonoidHom) = 0 := by
  let := IsElementaryAbelian.map (p := 2) e.toMonoidHom (A := A)
  ext x y
  obtain ⟨a,ha,he⟩ := x.toMul.property
  obtain ⟨b,hb,hf⟩ := y.toMul.property
  change outerValue (x.toMul : Model) (y.toMul : Model) = 0
  rw [← he,← hf]
  change outerValue (e a) (e b) = 0
  rw [outerValue_equiv]
  change intrinsicElementaryForm A (Additive.ofMul ⟨a,ha⟩) (Additive.ofMul ⟨b,hb⟩) = 0
  rw [hA]
  rfl

/-- The actual image of the native four-space under an ambient conjugation. -/
def conjugateIsotropic (g : Model) : Subgroup Model :=
  isotropicSubgroup.map (MulAut.conj g).toMonoidHom

instance conjugateIsotropic_elementary (g : Model) : IsElementaryAbelian 2 (conjugateIsotropic g) :=
  IsElementaryAbelian.map (MulAut.conj g).toMonoidHom

theorem conjugateIsotropic_card (g : Model) : Nat.card (conjugateIsotropic g) = 16 := by
  rw [conjugateIsotropic,card_map_of_injective (MulAut.conj g).injective,isotropicSubgroup_card]

theorem conjugateIsotropic_form_zero (g : Model) :
    intrinsicElementaryForm (conjugateIsotropic g) = 0 :=
  zero_form_map isotropicSubgroup (MulAut.conj g) isotropicSubgroup_form_zero

theorem conjugateIsotropic_le (g : Model) :
    conjugateIsotropic g ≤ (nativeEight 0).map (MulAut.conj g).toMonoidHom :=
  Subgroup.map_mono isotropicSubgroup_le

/-- The certified fusion word transports the same four-space to the common
native centralizer representative. -/
theorem fusedIsotropic_le : conjugateIsotropic nativeFusion ≤ nativeEight 1 := by
  rw [← nativeFusion_eight]
  exact conjugateIsotropic_le nativeFusion

/-- A literal pullback of the native zero-form sixteen into any conjugate of
the computed centralizer. Whole-normalizer invariance is a separate assertion. -/
theorem exists_zero_form_of_fused_eight (C : Subgroup Model) (g : Model)
    (hg : C.map (MulAut.conj g).toMonoidHom = nativeEight 1) :
    ∃ Y : Subgroup Model, Y ≤ C ∧ Y ≠ ⊥ ∧
      ∃ _h : IsElementaryAbelian 2 Y, Nat.card Y = 16 ∧ intrinsicElementaryForm Y = 0 := by
  let e := MulAut.conj g
  let Y := (conjugateIsotropic nativeFusion).map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map e.symm.toMonoidHom
  have hC : (nativeEight 1).map e.symm.toMonoidHom = C :=
    (Subgroup.map_symm_eq_iff_map_eq (K := C) (H := nativeEight 1) (e := e)).mpr hg
  have hY : Y ≤ C := by
    rw [← hC]
    exact Subgroup.map_mono fusedIsotropic_le
  have hcard : Nat.card Y = 16 := by
    rw [card_map_of_injective e.symm.injective,conjugateIsotropic_card]
  have hne : Y ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hcard
    contradiction
  exact ⟨Y,hY,hne,inferInstance,hcard,
    zero_form_map _ e.symm (conjugateIsotropic_form_zero nativeFusion)⟩
end Janko4.LocalStructure.ElementaryEightGeometry
