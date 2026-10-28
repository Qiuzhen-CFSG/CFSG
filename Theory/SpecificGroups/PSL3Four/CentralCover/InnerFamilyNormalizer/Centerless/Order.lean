module
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.Centerless
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Mathlib.Data.Set.Card

/-!
# The quaternion supplement of the graph-field fixed subgroup

The actual graph-field fixed subgroup of PSL₃(4) embeds into the projective
special unitary group for the identity Hermitian form. Orthonormalization
compares that carrier with the antidiagonal form in Huppert II.10.12, whose
proved order formula gives 72. This uses the canonical injective map
PSL₃(4) → PGL₃(4) and the actual fixed unitary representatives.

The displayed E₉ and quaternion subgroup have trivial intersection, so
their 72 products are distinct. The order bound therefore shows that they
supplement one another throughout the graph-field fixed subgroup.

Sources: Huppert, II.10.12, and Aschbacher–Smith, combined manuscript of
1 March 2004, the centerless case of 16.4.9(2), printed pp.1191–1192.
-/

public section
noncomputable section
namespace Matrix.PSL3Four.InnerFamilyNormalizer.Centerless
open Subgroup ExtendedCentralizer ProjectiveGraphField
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.IdentityGram

private def antiForm : HermitianForm 3 F where
  conj := fieldFrobenius
  conj_involutive := fieldFrobenius_involutive
  form := !![0,0,1;0,1,0;1,0,0]
  form_hermitian := by
    intro r c
    fin_cases r <;> fin_cases c <;> simp
  form_nondegenerate := by simp [Matrix.det_fin_three]

private theorem antiForm_fixed_card : Nat.card {x : F // antiForm.conj x = x} = 2 := by
  have he : {x : F | antiForm.conj x = x} = {0,1} := by
    ext x
    change fieldFrobenius x = x ↔ x = 0 ∨ x = 1
    rw [fieldFrobenius_apply]
    constructor
    · intro h
      have hh : x * (x - 1) = 0 := by calc
        x * (x - 1) = x ^ 2 - x := by ring
        _ = 0 := sub_eq_zero.mpr h
      simpa only [sub_eq_zero] using mul_eq_zero.mp hh
    · rintro (rfl | rfl) <;> simp
  change Nat.card {x : F // x ∈ {x : F | antiForm.conj x = x}} = 2
  rw [he, Nat.card_coe_set_eq]
  simp

private theorem antiForm_projective_card : Nat.card (ProjectiveSpecialUnitaryMatrixGroup antiForm) = 72 := by
  obtain ⟨_, _, _, _, _, hs⟩ := huppert_II_10_12 antiForm 2
    (by simpa using card_F) antiForm_fixed_card rfl
  exact hs.2.2.2.1

private theorem identityForm_projective_card :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup (identityGram antiForm)) = 72 := by
  obtain ⟨C, e, ep, _, _, _⟩ := exists_identityGram_transport antiForm 2 (by decide)
    (by simpa using card_F) (fun x => fieldFrobenius_apply x)
  rw [← Nat.card_congr ep.toEquiv]
  exact antiForm_projective_card

private def fixedToUnitary : ProjectiveFixer.graphField.fixedSubgroup →*
    ProjectiveSpecialUnitaryMatrixGroup (identityGram antiForm) :=
  (ProjectiveSpecialLinearGroup.toPGL.comp ProjectiveFixer.graphField.fixedSubgroup.subtype).codRestrict
    (ProjectiveSpecialUnitaryMatrixGroup (identityGram antiForm)) (by
      intro x
      obtain ⟨A, rfl⟩ := fixedProjection_surjective x
      refine ⟨SpecialLinearGroup.toGL A.val, ?_, ?_⟩
      · apply ((identityGram antiForm).mem_specialSubgroup_iff _).mpr
        constructor
        · have hh := (mem_unitary_iff A.val).mp A.property
          have ha : (identityGram antiForm).conjTranspose (SpecialLinearGroup.toGL A.val).val =
              (A.val.val.map (fun x => x ^ 2)).transpose := by
            ext r c
            exact fieldFrobenius_apply _
          change (identityGram antiForm).conjTranspose (SpecialLinearGroup.toGL A.val).val *
            1 * A.val.val = 1
          rw [ha, mul_one]
          exact hh
        · apply Units.ext
          exact A.val.property
      · exact (ProjectiveSpecialLinearGroup.toPGL_mk A.val).symm)

private theorem fixedToUnitary_injective : Function.Injective fixedToUnitary := by
  intro x y h
  apply Subtype.ext
  apply ProjectiveSpecialLinearGroup.toPGL_injective
  exact congrArg Subtype.val h

/-- The actual graph-field fixed subgroup has at most 72 elements. -/
theorem fixed_card_le : Nat.card ProjectiveFixer.graphField.fixedSubgroup ≤ 72 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (identityGram antiForm)) :=
    Nat.finite_of_card_ne_zero (by rw [identityForm_projective_card]; decide)
  rw [← identityForm_projective_card]
  exact Nat.card_le_card_of_injective fixedToUnitary fixedToUnitary_injective


/-- The displayed E₉ and quaternion subgroup generate the entire fixed subgroup. -/
theorem fixed_eq_model_sup_quaternion :
    ProjectiveFixer.graphField.fixedSubgroup = ProjectiveFixer.model ⊔ quaternion := by
  apply (Subgroup.eq_of_le_of_card_ge
    (sup_le ProjectiveFixer.graphField_fixes_model quaternion_le_fixed) ?_).symm
  let f : ProjectiveFixer.model × quaternion → (ProjectiveFixer.model ⊔ quaternion : Subgroup PSL) :=
    fun x => ⟨(x.1 : PSL) * (x.2 : PSL), Subgroup.mul_mem _ (mem_sup_left x.1.property) (mem_sup_right x.2.property)⟩
  have hf : Function.Injective f := by
    intro x y h
    exact (mul_injective_of_disjoint quaternion_disjoint_model.symm) (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, ProjectiveFixer.model_card, quaternion_card] at hc
  exact fixed_card_le.trans hc

/-- The graph-field fixed subgroup of PSL₃(4) has order 72. -/
theorem fixed_card : Nat.card ProjectiveFixer.graphField.fixedSubgroup = 72 := by
  apply le_antisymm fixed_card_le
  let f : ProjectiveFixer.model × quaternion → ProjectiveFixer.graphField.fixedSubgroup :=
    fun x => ⟨(x.1 : PSL) * (x.2 : PSL), Subgroup.mul_mem _
      (ProjectiveFixer.graphField_fixes_model x.1.property) (quaternion_le_fixed x.2.property)⟩
  have hf : Function.Injective f := by
    intro x y h
    exact (mul_injective_of_disjoint quaternion_disjoint_model.symm) (congrArg Subtype.val h)
  simpa only [Nat.card_prod, ProjectiveFixer.model_card, quaternion_card] using
    Nat.card_le_card_of_injective f hf

end Matrix.PSL3Four.InnerFamilyNormalizer.Centerless
