module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.FullAction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Representatives.Coefficients
public import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# The full centralizer preserves the calibrated intrinsic quartic

The ordered product of four linear combinations of the ten operators is a
multilinear map into the matrix algebra. Basis extensionality and the certified
multiplication table identify it with the published alternating quartic times
the top operator. Thus its normalized top coordinate is an actual alternating
form, with the exact saved 210 coefficients and tuple order.

The conjugation identity from `FullAction` carries products to products. The
nonzero top operator is fixed because its line is one dimensional over F₂.
Only after proving that fixation do we read its (0,0) entry to establish
invariance. The resulting homomorphism to the existing quartic stabilizer
has exactly the same kernel as `rho`.

Source: the literal construction and conventions in
`IntrinsicAlgebra/source/README.md`, and the independently specified tensor in
`Theory/Representation/BinaryQuarticMathieu/Basic.lean`.
-/

public section
set_option maxRecDepth 2048
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open BinaryQuarticMathieu (quartic)
open BinaryQuarticMathieu.RankRecognition (basisVector)
attribute [local irreducible] operator topOperator quartic op rho kernelMatrixAction

/-- Literal agreement of the independently published lexicographic enumerations. -/
theorem quarticTuples_eq_quadruple (q : Fin 210) :
    quarticTuples.get q = BinaryQuarticMathieu.quadruple q := by rfl

theorem quarticCoefficient_eq (q : Fin 210) :
    quarticCoefficient q =
      if BinaryQuarticMathieu.coefficientWord.testBit q.val then 1 else 0 := rfl

theorem quartic_basisCoordinate (t : Fin 4 → Fin 10) :
    quartic (fun j => basisVector (t j)) = quarticCoordinate t := by
  classical
  by_cases ht : Function.Injective t
  · let p := Tuple.sort t
    obtain ⟨q, hq, _⟩ := quarticTuples_existsUnique (t ∘ p)
      ((Tuple.monotone_sort t).strictMono_of_injective (ht.comp p.injective))
    have hperm := BinaryQuarticMathieu.RankRecognition.Representatives.basis_permutation
      t q p.symm p.symm.injective (by
        intro i
        rw [← quarticTuples_eq_quadruple, hq]
        simp only [Function.comp_apply, Equiv.apply_symm_apply])
    rw [hperm, ← quarticCoefficient_eq]
    rw [← quarticCoordinate_comp_perm t p, ← hq, quarticCoordinate_tuple]
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp ht
    rw [quartic.map_eq_zero_of_eq _ (congrArg basisVector hij) hne,
      quarticCoordinate_eq_zero_of_repeat t i j hne hij]

noncomputable def operatorProduct : MultilinearMap (ZMod 2)
    (fun _ : Fin 4 => Fin 10 → ZMod 2) SmallMatrix :=
  (MultilinearMap.mkPiAlgebraFin (ZMod 2) 4 SmallMatrix).compLinearMap (fun _ => op)

attribute [local irreducible] operatorProduct

private theorem prod_ofFn_four {M : Type*} [Monoid M] (v : Fin 4 → M) :
    (List.ofFn v).prod = v 0 * v 1 * v 2 * v 3 := by
  simp [List.ofFn_succ, mul_assoc]

private theorem quarticProduct_four (t : Fin 4 → Fin 10) :
    quarticProduct t = operator (t 0) * operator (t 1) * operator (t 2) * operator (t 3) := by
  rw [quarticProduct_eq_list_prod]
  exact prod_ofFn_four (operator ∘ t)

theorem operatorProduct_apply (v : Fin 4 → Fin 10 → ZMod 2) :
    operatorProduct v = op (v 0) * op (v 1) * op (v 2) * op (v 3) := by
  rw [operatorProduct, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebraFin_apply]
  exact prod_ofFn_four (fun i => op (v i))

theorem operatorProduct_eq_quartic (v : Fin 4 → Fin 10 → ZMod 2) :
    operatorProduct v = quartic v • topOperator := by
  have h : operatorProduct =
      ((LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2).smulRight topOperator).compMultilinearMap
        quartic.toMultilinearMap := by
    apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun (ZMod 2) (Fin 10))
    intro t
    simp only [operatorProduct_apply, Pi.basisFun_apply, op_single,
      LinearMap.compMultilinearMap_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
      AlternatingMap.coe_multilinearMap]
    rw [← quarticProduct_four]
    change quarticProduct t = quartic (fun j => basisVector (t j)) • topOperator
    rw [quartic_basisCoordinate, quarticProduct_eq_coordinate]
  exact MultilinearMap.congr_fun h v

/-- The scalar coordinate of the top line, normalized by its (0,0) entry. -/
def topCoefficient : SmallMatrix →ₗ[ZMod 2] ZMod 2 where
  toFun M := M 0 0
  map_add' := by intro M N; rfl
  map_smul' := by intro a M; rfl

private def formOfProduct
    (P : MultilinearMap (ZMod 2) (fun _ : Fin 4 => Fin 10 → ZMod 2) SmallMatrix)
    (Q : BinaryQuarticMathieu.Form) (t : SmallMatrix)
    (h : ∀ v, P v = Q v • t) : BinaryQuarticMathieu.Form where
  toMultilinearMap := topCoefficient.compMultilinearMap P
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    change topCoefficient (P v) = 0
    rw [h, Q.map_eq_zero_of_eq v hij hne, zero_smul, map_zero]

private theorem formOfProduct_apply
    (P : MultilinearMap (ZMod 2) (fun _ : Fin 4 => Fin 10 → ZMod 2) SmallMatrix)
    (Q : BinaryQuarticMathieu.Form) (t : SmallMatrix)
    (h : ∀ v, P v = Q v • t) (v : Fin 4 → Fin 10 → ZMod 2) :
    formOfProduct P Q t h v = P v 0 0 := rfl

/-- The intrinsic alternating four-form extracted from operator multiplication. -/
noncomputable def phi : BinaryQuarticMathieu.Form :=
  formOfProduct operatorProduct quartic topOperator operatorProduct_eq_quartic

theorem phi_apply (v : Fin 4 → Fin 10 → ZMod 2) : phi v = operatorProduct v 0 0 :=
  formOfProduct_apply operatorProduct quartic topOperator operatorProduct_eq_quartic v

/-- Exact calibration to the separately defined literal binary quartic. -/
theorem phi_eq_quartic : phi = quartic := by
  ext v
  rw [phi_apply, operatorProduct_eq_quartic, Matrix.smul_apply, smul_eq_mul,
    topOperator_entry_zero_zero, mul_one]

theorem operatorProduct_eq_phi (v : Fin 4 → Fin 10 → ZMod 2) :
    operatorProduct v = phi v • topOperator := by
  rw [phi_eq_quartic, operatorProduct_eq_quartic]

theorem phi_basis_coefficient (q : Fin 210) :
    phi (fun j => Pi.single (quarticTuples.get q j) 1) = quarticCoefficient q := by
  rw [phi_eq_quartic]
  exact (quartic_basisCoordinate (quarticTuples.get q)).trans (quarticCoordinate_tuple q)

private theorem conjugate_mul (g : SmallMatrixˣ) (A B : SmallMatrix) :
    ((g : SmallMatrix) * A * ↑g⁻¹) * ((g : SmallMatrix) * B * ↑g⁻¹) =
      (g : SmallMatrix) * (A * B) * ↑g⁻¹ := by
  simp only [mul_assoc, Units.inv_mul_cancel_left]

/-- Conjugation carries the full multilinear product to the product of the images. -/
theorem operatorProduct_rho (c : centralizer) (v : Fin 4 → Fin 10 → ZMod 2) :
    operatorProduct (fun i => (rho c : TenMatrix) *ᵥ v i) =
      (kernelMatrixAction c : SmallMatrix) * operatorProduct v * ↑(kernelMatrixAction c)⁻¹ := by
  simp only [operatorProduct_apply, op_rho_conjugation, conjugate_mul]

private theorem conjugate_ne_zero (g : SmallMatrixˣ) {A : SmallMatrix} (h : A ≠ 0) :
    (g : SmallMatrix) * A * ↑g⁻¹ ≠ 0 := by
  intro hz
  exact h ((Units.mul_right_eq_zero g).mp ((Units.mul_left_eq_zero g⁻¹).mp hz))

/-- The unique nonzero top operator is fixed, before any scalar entry is read. -/
theorem kernelMatrixAction_fixes_topOperator (c : centralizer) :
    (kernelMatrixAction c : SmallMatrix) * topOperator * ↑(kernelMatrixAction c)⁻¹ =
      topOperator := by
  let v : Fin 4 → Fin 10 → ZMod 2 := fun j => Pi.single (![0,1,2,3] j) 1
  have hv : operatorProduct v = topOperator := by
    simp only [operatorProduct_apply, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, op_single]
    exact topOperator_eq_product.symm
  have h : (kernelMatrixAction c : SmallMatrix) * topOperator * ↑(kernelMatrixAction c)⁻¹ =
      quartic (fun j => (rho c : TenMatrix) *ᵥ v j) • topOperator := by
    rw [← hv, ← operatorProduct_rho, operatorProduct_eq_quartic]
    rw [hv]
  have hn := conjugate_ne_zero (kernelMatrixAction c) topOperator_ne_zero
  have hs : quartic (fun j => (rho c : TenMatrix) *ᵥ v j) ≠ 0 := by
    intro hs
    rw [h, hs, zero_smul] at hn
    exact hn rfl
  have hone : quartic (fun j => (rho c : TenMatrix) *ᵥ v j) = 1 := by
    have htwo : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide +kernel
    exact htwo _ hs
  rw [h, hone, one_smul]

/-- Preservation holds for every four arguments under the actual full-centralizer action. -/
theorem rho_preserves_quartic (c : centralizer) (v : Fin 4 → Fin 10 → ZMod 2) :
    quartic (fun i => (rho c : TenMatrix) *ᵥ v i) = quartic v := by
  have h := operatorProduct_rho c v
  rw [operatorProduct_eq_quartic, operatorProduct_eq_quartic,
    mul_smul_comm, smul_mul_assoc, kernelMatrixAction_fixes_topOperator] at h
  have he := congrArg (fun M : SmallMatrix => M 0 0) h
  simpa only [Matrix.smul_apply, smul_eq_mul, topOperator_entry_zero_zero, mul_one] using he

theorem rho_preserves_phi (c : centralizer) (v : Fin 4 → Fin 10 → ZMod 2) :
    phi (fun i => (rho c : TenMatrix) *ᵥ v i) = phi v := by
  rw [phi_eq_quartic]
  exact rho_preserves_quartic c v

/-- The faithful conversion of matrix units to linear equivalences uses column action. -/
@[expose] noncomputable def tenMatrixUnitEquiv : TenMatrixˣ ≃*
    ((Fin 10 → ZMod 2) ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)) :=
  (Units.mapEquiv Matrix.toLinAlgEquiv'.toMulEquiv).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 10 → ZMod 2))

theorem tenMatrixUnitEquiv_apply (g : TenMatrixˣ) (v : Fin 10 → ZMod 2) :
    tenMatrixUnitEquiv g v = (g : TenMatrix) *ᵥ v := rfl

noncomputable def rhoLinear : centralizer →*
    ((Fin 10 → ZMod 2) ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)) :=
  tenMatrixUnitEquiv.toMonoidHom.comp rho

theorem rhoLinear_apply (c : centralizer) (v : Fin 10 → ZMod 2) :
    rhoLinear c v = (rho c : TenMatrix) *ᵥ v := tenMatrixUnitEquiv_apply (rho c) v

theorem rhoLinear_ker : rhoLinear.ker = rho.ker :=
  MonoidHom.ker_comp_of_injective rho tenMatrixUnitEquiv.toMonoidHom tenMatrixUnitEquiv.injective

theorem rhoLinear_preserves (c : centralizer) :
    BinaryQuarticMathieu.Preserves quartic (rhoLinear c) := by
  intro v w x y
  have h := rho_preserves_quartic c ![v,w,x,y]
  have he : (fun i => (rho c : TenMatrix) *ᵥ (![v,w,x,y] i)) =
      ![rhoLinear c v, rhoLinear c w, rhoLinear c x, rhoLinear c y] := by
    funext i
    fin_cases i <;> simp only [rhoLinear_apply] <;> rfl
  rw [he] at h
  exact h

theorem rhoLinear_mem_quarticStabilizer (c : centralizer) :
    rhoLinear c ∈ BinaryQuarticMathieu.quarticStabilizer := rhoLinear_preserves c

/-- A homomorphism to the stabilizer of precisely the published tensor. -/
@[expose] noncomputable def rhoToQuarticStabilizer : centralizer →* BinaryQuarticMathieu.quarticStabilizer :=
  rhoLinear.codRestrict _ rhoLinear_mem_quarticStabilizer

theorem rhoToQuarticStabilizer_coe (c : centralizer) :
    (rhoToQuarticStabilizer c : (Fin 10 → ZMod 2) ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)) =
      rhoLinear c := rfl

theorem rhoToQuarticStabilizer_ker : rhoToQuarticStabilizer.ker = rho.ker := by
  rw [rhoToQuarticStabilizer, MonoidHom.ker_codRestrict, rhoLinear_ker]

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
