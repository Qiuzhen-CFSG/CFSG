module
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.SchreierIntertwining.Operators
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary

/-!
# Structural generation by the certified Mathieu reference matrices

Ten short words in the nineteen reference matrices give the elementary
transvections with coefficients one and omega, except for two coefficient-one
roots. The three-index transvection relation gives those two roots from
omega * (1 + omega) = 1. Additivity supplies the other field coefficients;
elementary generation then gives all of SL₃(4). Every reference label has an
actual Schreier edge preimage, checked by the small finite index table.

Only three-by-three matrix identities are reduced here. The lower certificates
are imported unchanged, and neither SL₃(4) nor the module vectors are enumerated.
The private word checks are elaborated serially to keep their memory bounded.
The discovery data, measurements and provenance are in `source/README.md`.

This is the image-generation ingredient in the point stabilizer comparison
used for James (1973), Lemma 8.3, and Aschbacher–Smith H.12.1, printed pp.393–394.
The reusable elementary-generation and three-index identities are proved in
`SLHigherNaturalFirstCohomology/Elementary.lean`.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
namespace EdgeImage
open Matrix.SpecialLinearGroup
open SchreierCertificate
open Representation.OneCohomology.SLHigherNatural

set_option Elab.async false in
private lemma word_01_one :
    referenceElement 3 * referenceElement 1 * referenceElement 3 * (referenceElement 4)⁻¹ =
      transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : Reference.F) := by
  apply Subtype.ext
  change naturalMatrix 3 * naturalMatrix 1 * naturalMatrix 3 * (naturalMatrix 4).adjugate =
    1 + Matrix.single 0 1 (1 : Reference.F)
  decide +kernel

set_option Elab.async false in
private lemma word_01_omega :
    referenceElement 2 * (referenceElement 13)⁻¹ * referenceElement 6 * referenceElement 5 =
      transvection (show (0 : Fin 3) ≠ 1 by decide) (QuadraticAlgebra.omega : Reference.F) := by
  apply Subtype.ext
  change naturalMatrix 2 * (naturalMatrix 13).adjugate * naturalMatrix 6 * naturalMatrix 5 =
    1 + Matrix.single 0 1 (QuadraticAlgebra.omega : Reference.F)
  decide +kernel

set_option Elab.async false in
private lemma word_02_one :
    referenceElement 1 * referenceElement 11 * referenceElement 1 =
      transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : Reference.F) := by
  apply Subtype.ext
  change naturalMatrix 1 * naturalMatrix 11 * naturalMatrix 1 =
    1 + Matrix.single 0 2 (1 : Reference.F)
  decide +kernel

set_option Elab.async false in
private lemma word_02_omega :
    referenceElement 2 * referenceElement 5 * referenceElement 6 * referenceElement 13 =
      transvection (show (0 : Fin 3) ≠ 2 by decide) (QuadraticAlgebra.omega : Reference.F) := by
  apply Subtype.ext
  change naturalMatrix 2 * naturalMatrix 5 * naturalMatrix 6 * naturalMatrix 13 =
    1 + Matrix.single 0 2 (QuadraticAlgebra.omega : Reference.F)
  decide +kernel

set_option Elab.async false in
private lemma word_10_one :
    referenceElement 3 * referenceElement 2 * referenceElement 7 * referenceElement 9 =
      transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : Reference.F) := by
  apply Subtype.ext
  change naturalMatrix 3 * naturalMatrix 2 * naturalMatrix 7 * naturalMatrix 9 =
    1 + Matrix.single 1 0 (1 : Reference.F)
  decide +kernel

set_option Elab.async false in
private lemma word_10_omega :
    referenceElement 2 * (referenceElement 14)⁻¹ * (referenceElement 13)⁻¹ * referenceElement 17 =
      transvection (show (1 : Fin 3) ≠ 0 by decide) (QuadraticAlgebra.omega : Reference.F) := by
  apply Subtype.ext
  change naturalMatrix 2 * (naturalMatrix 14).adjugate * (naturalMatrix 13).adjugate * naturalMatrix 17 =
    1 + Matrix.single 1 0 (QuadraticAlgebra.omega : Reference.F)
  decide +kernel

set_option Elab.async false in
private lemma word_12_one :
    referenceElement 1 * (referenceElement 9)⁻¹ * referenceElement 13 * (referenceElement 3)⁻¹ =
      transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : Reference.F) := by
  apply Subtype.ext
  change naturalMatrix 1 * (naturalMatrix 9).adjugate * naturalMatrix 13 * (naturalMatrix 3).adjugate =
    1 + Matrix.single 1 2 (1 : Reference.F)
  decide +kernel

set_option Elab.async false in
private lemma word_12_omega :
    (referenceElement 13)⁻¹ * (referenceElement 14)⁻¹ * referenceElement 1 * (referenceElement 17)⁻¹ =
      transvection (show (1 : Fin 3) ≠ 2 by decide) (QuadraticAlgebra.omega : Reference.F) := by
  apply Subtype.ext
  change (naturalMatrix 13).adjugate * (naturalMatrix 14).adjugate * naturalMatrix 1 *
    (naturalMatrix 17).adjugate =
    1 + Matrix.single 1 2 (QuadraticAlgebra.omega : Reference.F)
  decide +kernel

set_option Elab.async false in
private lemma word_20_omega :
    referenceElement 8 * referenceElement 8 * referenceElement 1 * referenceElement 8 =
      transvection (show (2 : Fin 3) ≠ 0 by decide) (QuadraticAlgebra.omega : Reference.F) := by
  apply Subtype.ext
  change naturalMatrix 8 * naturalMatrix 8 * naturalMatrix 1 * naturalMatrix 8 =
    1 + Matrix.single 2 0 (QuadraticAlgebra.omega : Reference.F)
  decide +kernel

set_option Elab.async false in
private lemma word_21_omega :
    referenceElement 5 * referenceElement 11 * referenceElement 6 * referenceElement 14 =
      transvection (show (2 : Fin 3) ≠ 1 by decide) (QuadraticAlgebra.omega : Reference.F) := by
  apply Subtype.ext
  change naturalMatrix 5 * naturalMatrix 11 * naturalMatrix 6 * naturalMatrix 14 =
    1 + Matrix.single 2 1 (QuadraticAlgebra.omega : Reference.F)
  decide +kernel

/-- Every matrix label occurs on an actual Schreier edge. -/
lemma schreierIndex_surjective :
    Function.Surjective (fun ij : Fin 22 × Fin 2 => schreierIndex ij.1 ij.2) := by
  decide +kernel

/-- The subgroup generated by the nineteen certified reference matrices. -/
def referenceClosure : Subgroup Reference.SL :=
  Subgroup.closure (Set.range referenceElement)

private lemma reference_mem (k : Fin 19) : referenceElement k ∈ referenceClosure :=
  Subgroup.subset_closure ⟨k, rfl⟩

private lemma transvection_chain_mem (H : Subgroup Reference.SL)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : Reference.F)
    (ha : transvection hij a ∈ H) (hb : transvection hjk b ∈ H) :
    transvection hik (a * b) ∈ H := by
  apply (H.mul_mem_cancel_left hb).mp
  apply (H.mul_mem_cancel_right ha).mp
  rw [← transvection_chain hij hjk hik a b]
  exact H.mul_mem ha hb

private lemma transvection_add_mem (H : Subgroup Reference.SL)
    {i j : Fin 3} (hij : i ≠ j) (a b : Reference.F)
    (ha : transvection hij a ∈ H) (hb : transvection hij b ∈ H) :
    transvection hij (a + b) ∈ H := by
  rw [transvection_add]
  exact H.mul_mem ha hb

private lemma transvections_one_omega :
    ∀ (i j : Fin 3) (hij : i ≠ j),
      transvection hij (1 : Reference.F) ∈ referenceClosure ∧
      transvection hij (QuadraticAlgebra.omega : Reference.F) ∈ referenceClosure := by
  have h01_one : transvection (show (0 : Fin 3) ≠ 1 by decide)
      (1 : Reference.F) ∈ referenceClosure := by
    rw [← word_01_one]
    exact (referenceClosure.mul_mem
      (referenceClosure.mul_mem (referenceClosure.mul_mem (reference_mem 3) (reference_mem 1)) (reference_mem 3)) (referenceClosure.inv_mem (reference_mem 4)))
  have h01_omega : transvection (show (0 : Fin 3) ≠ 1 by decide)
      (QuadraticAlgebra.omega : Reference.F) ∈ referenceClosure := by
    rw [← word_01_omega]
    exact (referenceClosure.mul_mem
      (referenceClosure.mul_mem (referenceClosure.mul_mem (reference_mem 2) (referenceClosure.inv_mem (reference_mem 13))) (reference_mem 6)) (reference_mem 5))
  have h02_one : transvection (show (0 : Fin 3) ≠ 2 by decide)
      (1 : Reference.F) ∈ referenceClosure := by
    rw [← word_02_one]
    exact (referenceClosure.mul_mem
      (referenceClosure.mul_mem (reference_mem 1) (reference_mem 11)) (reference_mem 1))
  have h02_omega : transvection (show (0 : Fin 3) ≠ 2 by decide)
      (QuadraticAlgebra.omega : Reference.F) ∈ referenceClosure := by
    rw [← word_02_omega]
    exact (referenceClosure.mul_mem
      (referenceClosure.mul_mem (referenceClosure.mul_mem (reference_mem 2) (reference_mem 5)) (reference_mem 6)) (reference_mem 13))
  have h10_one : transvection (show (1 : Fin 3) ≠ 0 by decide)
      (1 : Reference.F) ∈ referenceClosure := by
    rw [← word_10_one]
    exact (referenceClosure.mul_mem
      (referenceClosure.mul_mem (referenceClosure.mul_mem (reference_mem 3) (reference_mem 2)) (reference_mem 7)) (reference_mem 9))
  have h10_omega : transvection (show (1 : Fin 3) ≠ 0 by decide)
      (QuadraticAlgebra.omega : Reference.F) ∈ referenceClosure := by
    rw [← word_10_omega]
    exact (referenceClosure.mul_mem
      (referenceClosure.mul_mem (referenceClosure.mul_mem (reference_mem 2) (referenceClosure.inv_mem (reference_mem 14))) (referenceClosure.inv_mem (reference_mem 13))) (reference_mem 17))
  have h12_one : transvection (show (1 : Fin 3) ≠ 2 by decide)
      (1 : Reference.F) ∈ referenceClosure := by
    rw [← word_12_one]
    exact (referenceClosure.mul_mem
      (referenceClosure.mul_mem (referenceClosure.mul_mem (reference_mem 1) (referenceClosure.inv_mem (reference_mem 9))) (reference_mem 13)) (referenceClosure.inv_mem (reference_mem 3)))
  have h12_omega : transvection (show (1 : Fin 3) ≠ 2 by decide)
      (QuadraticAlgebra.omega : Reference.F) ∈ referenceClosure := by
    rw [← word_12_omega]
    exact (referenceClosure.mul_mem
      (referenceClosure.mul_mem (referenceClosure.mul_mem (referenceClosure.inv_mem (reference_mem 13)) (referenceClosure.inv_mem (reference_mem 14))) (reference_mem 1)) (referenceClosure.inv_mem (reference_mem 17)))
  have h20_omega : transvection (show (2 : Fin 3) ≠ 0 by decide)
      (QuadraticAlgebra.omega : Reference.F) ∈ referenceClosure := by
    rw [← word_20_omega]
    exact (referenceClosure.mul_mem
      (referenceClosure.mul_mem (referenceClosure.mul_mem (reference_mem 8) (reference_mem 8)) (reference_mem 1)) (reference_mem 8))
  have h21_omega : transvection (show (2 : Fin 3) ≠ 1 by decide)
      (QuadraticAlgebra.omega : Reference.F) ∈ referenceClosure := by
    rw [← word_21_omega]
    exact (referenceClosure.mul_mem
      (referenceClosure.mul_mem (referenceClosure.mul_mem (reference_mem 5) (reference_mem 11)) (reference_mem 6)) (reference_mem 14))
  have hw : (QuadraticAlgebra.omega : Reference.F) * (1 + QuadraticAlgebra.omega) = 1 := by
    decide +kernel
  have h20_one : transvection (show (2 : Fin 3) ≠ 0 by decide) (1 : Reference.F) ∈
      referenceClosure := by
    rw [← hw]
    exact transvection_chain_mem referenceClosure (by decide : (2 : Fin 3) ≠ 1)
      (by decide : (1 : Fin 3) ≠ 0) (by decide) _ _ h21_omega
      (transvection_add_mem referenceClosure (by decide) _ _ h10_one h10_omega)
  have h21_one : transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : Reference.F) ∈
      referenceClosure := by
    rw [← hw]
    exact transvection_chain_mem referenceClosure (by decide : (2 : Fin 3) ≠ 0)
      (by decide : (0 : Fin 3) ≠ 1) (by decide) _ _ h20_omega
      (transvection_add_mem referenceClosure (by decide) _ _ h01_one h01_omega)
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact ⟨h01_one, h01_omega⟩
    | exact ⟨h02_one, h02_omega⟩
    | exact ⟨h10_one, h10_omega⟩
    | exact ⟨h12_one, h12_omega⟩
    | exact ⟨h20_one, h20_omega⟩
    | exact ⟨h21_one, h21_omega⟩

/-- All elementary transvections lie in the subgroup generated by the actual
reference matrices; the two missing coefficient-one roots follow from the
three-index relation. -/
lemma transvection_mem_referenceClosure (i j : Fin 3) (hij : i ≠ j) (a : Reference.F) :
    transvection hij a ∈ referenceClosure := by
  have hcases : ∀ a : Reference.F,
      a = 0 ∨ a = 1 ∨ a = QuadraticAlgebra.omega ∨ a = 1 + QuadraticAlgebra.omega := by
    decide +kernel
  obtain ⟨h1, hw⟩ := transvections_one_omega i j hij
  rcases hcases a with rfl | rfl | rfl | rfl
  · simpa only [transvection_coeff_zero] using referenceClosure.one_mem
  · exact h1
  · exact hw
  · exact transvection_add_mem referenceClosure hij _ _ h1 hw

/-- Structural generation of SL₃(4) by the nineteen reference matrices. -/
lemma closure_range_referenceElement : Subgroup.closure (Set.range referenceElement) = ⊤ := by
  apply top_unique
  intro g _
  exact transvection_induction (fun g => g ∈ referenceClosure)
    transvection_mem_referenceClosure (fun _ _ => referenceClosure.mul_mem) g

/-- The matrices belonging to the forty-four actual edges generate SL₃(4). -/
lemma closure_range_schreierReference :
    Subgroup.closure (Set.range (fun ij : Fin 22 × Fin 2 =>
      referenceElement (schreierIndex ij.1 ij.2))) = ⊤ := by
  have hr : Set.range (fun ij : Fin 22 × Fin 2 => referenceElement (schreierIndex ij.1 ij.2)) =
      Set.range referenceElement := by
    ext g
    constructor
    · rintro ⟨ij, rfl⟩
      exact ⟨schreierIndex ij.1 ij.2, rfl⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨ij, hij⟩ := schreierIndex_surjective k
      exact ⟨ij, congrArg referenceElement hij⟩
  rw [hr, closure_range_referenceElement]

end EdgeImage
end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
