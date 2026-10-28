module

/-
Adapted from Atlas/Comparisons/Exceptional/PSL2SevenAction.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, by Gerald Höhn
and the ATLAS contributors. ATLAS Research and Attribution License 1.0
applies; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: Lean 4.33 module boundaries, narrow imports, and CFSG order APIs.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases
set_option warningAsError false

@[expose] public section

/-!
# The projective action on eight marked points

Seven affine points and infinity exhaust the projective line over `ZMod 7`.
Translation and inversion generate PSL₂(7), by special-linear transvection
induction. Their action on this marking is checked by finite field arithmetic;
faithfulness comes from the natural projective action.
-/


noncomputable section
namespace Atlas.Comparisons.Exceptional.Seven
open Matrix
open scoped MatrixGroups LinearAlgebra.Projectivization
abbrev F := ZMod 7
local instance pSL2SevenActionPrime1 : Fact (Nat.Prime 7) := ⟨by decide⟩
abbrev L := ℙ F (Fin 2 → F)

def pointVector : Fin 8 → Fin 2 → F :=
  ![![0,1],![1,1],![2,1],![3,1],![4,1],![5,1],![6,1],![1,0]]
theorem pointVector_ne (i : Fin 8) : pointVector i ≠ 0 := by
  have h : ∀ i : Fin 8, pointVector i ≠ 0 := by decide
  exact h i

def point (i : Fin 8) : L := Projectivization.mk F (pointVector i) (pointVector_ne i)
theorem point_injective : Function.Injective point := by
  intro i j h
  have hd : ∀ i j : Fin 8,
      pointVector i 0 * pointVector j 1 = pointVector j 0 * pointVector i 1 → i = j := by decide
  apply hd i j
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at h0 h1
  rw [← h0, ← h1]
  ring

def marking : Fin 8 ≃ L := Equiv.ofBijective point
  ((Nat.bijective_iff_injective_and_card point).mpr ⟨point_injective,by
    rw [Nat.card_fin,Atlas.card_projectiveSpace]
    norm_num⟩)

def permutation : PSL(2,F) →* Equiv.Perm (Fin 8) :=
  marking.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom (PSL(2,F)) L)

theorem permutation_injective : Function.Injective permutation := by
  intro g h he
  apply (MulAction.toPerm_injective (β := L))
  exact marking.symm.permCongrHom.injective he

def upper : SL(2,F) := ⟨!![1,1;0,1], by decide⟩
def inversionMatrix : SL(2,F) := ⟨!![0,-1;1,0], by decide⟩
def translation : Equiv.Perm (Fin 8) where
  toFun := ![1,2,3,4,5,6,0,7]
  invFun := ![6,0,1,2,3,4,5,7]
  left_inv := by decide
  right_inv := by decide

def inversion : Equiv.Perm (Fin 8) where
  toFun := ![7,6,3,2,5,4,1,0]
  invFun := ![7,6,3,2,5,4,1,0]
  left_inv := by decide
  right_inv := by decide

theorem upper_vector (i : Fin 8) : upper.val *ᵥ pointVector i = pointVector (translation i) := by
  have h : ∀ i : Fin 8, upper.val *ᵥ pointVector i = pointVector (translation i) := by decide
  exact h i

def inversionScale : Fin 8 → F := ![-1,1,2,3,4,5,6,1]
theorem inversion_vector (i : Fin 8) :
    inversionMatrix.val *ᵥ pointVector i = inversionScale i • pointVector (inversion i) := by
  have h : ∀ i : Fin 8, inversionMatrix.val *ᵥ pointVector i =
      inversionScale i • pointVector (inversion i) := by decide
  exact h i

theorem permutation_upper : permutation (upper : PSL(2,F)) = translation := by
  apply Equiv.ext
  intro i
  apply marking.injective
  change marking (marking.symm ((upper : PSL(2,F)) • marking i)) = _
  rw [marking.apply_symm_apply]
  change (upper : PSL(2,F)) • point i = point (translation i)
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,point,Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact ⟨1, by simpa only [one_smul,Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using (upper_vector i).symm⟩

theorem permutation_inversion : permutation (inversionMatrix : PSL(2,F)) = inversion := by
  apply Equiv.ext
  intro i
  apply marking.injective
  change marking (marking.symm ((inversionMatrix : PSL(2,F)) • marking i)) = _
  rw [marking.apply_symm_apply]
  change (inversionMatrix : PSL(2,F)) • point i = point (inversion i)
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,point,Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact ⟨inversionScale i, by simpa only [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using (inversion_vector i).symm⟩

theorem upper_powers (c : F) :
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) c = upper ^ c.val := by
  have h : ∀ c : F, Matrix.SpecialLinearGroup.transvection
      (by decide : (0 : Fin 2) ≠ 1) c = upper ^ c.val := by decide
  exact h c

theorem lower_powers (c : F) :
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) c =
      inversionMatrix * upper ^ (-c).val * inversionMatrix⁻¹ := by
  have h : ∀ c : F, Matrix.SpecialLinearGroup.transvection
      (by decide : (1 : Fin 2) ≠ 0) c =
      inversionMatrix * upper ^ (-c).val * inversionMatrix⁻¹ := by decide
  exact h c

theorem sl_generated : Subgroup.closure ({upper,inversionMatrix} : Set SL(2,F)) = ⊤ := by
  let H := Subgroup.closure ({upper,inversionMatrix} : Set SL(2,F))
  have hu : upper ∈ H := Subgroup.subset_closure (by simp)
  have ht : inversionMatrix ∈ H := Subgroup.subset_closure (by simp)
  apply top_unique
  intro g _
  apply Matrix.SL2.transvection_induction (fun g => g ∈ H) ?_ (fun _ _ => H.mul_mem) g
  intro i j hij c
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · rw [upper_powers]; exact H.pow_mem hu _
  · rw [lower_powers]; exact H.mul_mem (H.mul_mem ht (H.pow_mem hu _)) (H.inv_mem ht)
  · exact (hij rfl).elim

def generators : Set PSL(2,F) := {(upper : PSL(2,F)), (inversionMatrix : PSL(2,F))}
theorem psl_generated : Subgroup.closure generators = ⊤ := by
  let π := QuotientGroup.mk' (Subgroup.center SL(2,F))
  have he : generators = π '' ({upper,inversionMatrix} : Set SL(2,F)) := by
    ext g; simp [generators,π, eq_comm]
  rw [he,← MonoidHom.map_closure,sl_generated]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
end Atlas.Comparisons.Exceptional.Seven
