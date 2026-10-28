module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGeneration
public import Mathlib.Order.Atoms

/-!
# Maximality in the unitary four-space point geometry

The stabilizer of the isotropic coordinate point is maximal in the actual
antidiagonal special unitary group. Its intersection with the coordinate-plane
stabilizer is maximal inside the point stabilizer. Both statements hold over
any finite field of characteristic two with an involution, so they include
all the binary unitary parameters, including q = 2.

For ambient maximality, conjugating a middle-coordinate transvection gives
an opposite-cell element whenever a subgroup containing the point stabilizer
moves its point. The explicit radical elimination from `UnitaryFourGeneration`
then supplies the coordinate swap that generates the whole group together
with the point stabilizer. Locally, the unitary equation makes the ratio of
the two middle entries of an isotropic column fixed by the involution.
An upper transvection with that parameter and the middle-coordinate swap
reduce every element outside the full flag stabilizer into it. This proves
the local maximality for the full point parabolic and its full overlap.

Source: the genuine U₄(q) flag amalgam in Aschbacher--Smith F.1.12(I)(6),
printed pp.263--264, with the amalgam conventions of F.1.4--7, printed
pp.260--261 of `refs/quasithin.pdf`. These are intrinsic maximality facts
for that model; no primitivity or BN-pair assumption is used.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourGeneration
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointGeometry
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "P" => pointParabolicSU F (form F σ hσ)
local notation "B" => borelSU F (form F σ hσ)

private def upperMatrix (t : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1,0,0,0; 0,1,t,0; 0,0,1,0; 0,0,0,1]

private def upper (t : F) (ht : σ t = t) : SU F (form F σ hσ) :=
  involutionElement F σ hσ (upperMatrix F t)
    (by ext i j; fin_cases i <;> fin_cases j <;>
        simp [upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero])
    (by ext i j; fin_cases i <;> fin_cases j <;>
        simp [upperMatrix, form, gram, HermitianForm.conjTranspose,
          Matrix.mul_apply, Fin.sum_univ_succ, ht, CharTwo.add_self_eq_zero])

private theorem upper_mem_borel (t : F) (ht : σ t = t) : upper F σ hσ t ht ∈ B := by
  constructor
  · change upper F σ hσ t ht ∈ P
    rw [mem_pointParabolicSU]
    simp [upper, involutionElement, upperMatrix]
  · change upper F σ hσ t ht ∈ planeParabolicSU F (form F σ hσ)
    rw [mem_planeParabolicSU]
    simp [upper, involutionElement, upperMatrix]

omit [Finite F] [CharP F 2] in
private theorem inv_val (g : SU F (form F σ hσ)) :
    (g⁻¹).val.val = gram F * (form F σ hσ).conjTranspose g.val.val * gram F := by
  have hu := g.property.1
  change (form F σ hσ).conjTranspose g.val.val * gram F * g.val.val = gram F at hu
  have hl : (gram F * (form F σ hσ).conjTranspose g.val.val * gram F) * g.val.val = 1 := by
    calc
      _ = gram F * ((form F σ hσ).conjTranspose g.val.val * gram F * g.val.val) := by
        simp only [mul_assoc]
      _ = 1 := by rw [hu, gram_sq]
  calc
    (g⁻¹).val.val = ((gram F * (form F σ hσ).conjTranspose g.val.val * gram F) *
        g.val.val) * (g⁻¹).val.val := by rw [hl, one_mul]
    _ = gram F * (form F σ hσ).conjTranspose g.val.val * gram F := by
      rw [mul_assoc, show g.val.val * (g⁻¹).val.val = 1 from g.val.val_inv, mul_one]

private theorem conjugate_upper_entry (g : SU F (form F σ hσ)) :
    (g⁻¹ * upper F σ hσ 1 (map_one σ) * g).val.val 3 0 =
      σ (g.val.val 2 0) * g.val.val 2 0 := by
  change ((g⁻¹).val.val * (upper F σ hσ 1 (map_one σ)).val.val * g.val.val) 3 0 = _
  rw [inv_val]
  have hi := column_isotropic F σ hσ g 0
  simp [upper, upperMatrix, involutionElement, form, gram, HermitianForm.conjTranspose,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  linear_combination hi

/-- Containing the point parabolic and a matrix in the opposite point cell
forces the whole group. -/
theorem eq_top_of_point_and_opposite (H : Subgroup (SU F (form F σ hσ)))
    (hP : P ≤ H) (g : SU F (form F σ hσ)) (hg : g ∈ H)
    (h30 : g.val.val 3 0 ≠ 0) : H = ⊤ := by
  obtain ⟨c, hc⟩ := exists_radical_reverse_mul_mem_point F σ hσ g h30
  have hr : radicalElement F σ hσ c ∈ H := hP (radical_mem_borel F σ hσ c).1
  have hw : reverse F σ hσ ∈ H :=
    (H.mul_mem_cancel_right hr).mp ((H.mul_mem_cancel_right hg).mp (hP hc))
  have hcell (a : SU F (form F σ hσ)) (ha : a.val.val 3 0 ≠ 0) : a ∈ H := by
    obtain ⟨d, hd⟩ := exists_radical_reverse_mul_mem_point F σ hσ a ha
    exact (H.mul_mem_cancel_left (H.mul_mem hw
      (hP (radical_mem_borel F σ hσ d).1))).mp (hP hd)
  let d : RadicalCoordinates F σ := ⟨0,1,0,by simp⟩
  let a := reverse F σ hσ * radicalElement F σ hσ d
  have ha : a ∈ H := H.mul_mem hw (hP (radical_mem_borel F σ hσ d).1)
  apply eq_top_of_point_and_pairSwap F σ hσ H hP
  apply (H.mul_mem_cancel_left ha).mp
  apply hcell
  change (((reverse F σ hσ).val.val * (radicalElement F σ hσ d).val.val) *
    (pairSwap F σ hσ).val.val) 3 0 ≠ 0
  rw [reverse_val]
  simp [gram, radicalElement, radicalMatrix, d, pairSwap, pairSwapMatrix,
    involutionElement, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The point stabilizer is maximal, including in the smallest binary model. -/
theorem pointParabolic_isCoatom : IsCoatom P := by
  rw [SetLike.isCoatom_iff]
  refine ⟨point_ne_top F σ hσ, ?_⟩
  intro H g hP hnot hg
  by_cases h30 : g.val.val 3 0 ≠ 0
  · exact eq_top_of_point_and_opposite F σ hσ H hP g hg h30
  have hmiddle : g.val.val 2 0 ≠ 0 ∨ g.val.val 1 0 ≠ 0 := by
    rw [mem_pointParabolicSU] at hnot
    tauto
  have hcase (a : SU F (form F σ hσ)) (ha : a ∈ H) (ha20 : a.val.val 2 0 ≠ 0) : H = ⊤ := by
    apply eq_top_of_point_and_opposite F σ hσ H hP
      (a⁻¹ * upper F σ hσ 1 (map_one σ) * a)
      (H.mul_mem (H.mul_mem (H.inv_mem ha) (hP (upper_mem_borel F σ hσ 1 (map_one σ)).1)) ha)
    rw [conjugate_upper_entry]
    exact mul_ne_zero (by simpa using ha20) ha20
  rcases hmiddle with h20 | h10
  · exact hcase g hg h20
  · apply hcase (middleSwap F σ hσ * g)
      (H.mul_mem (hP (middleSwap_mem_point F σ hσ)) hg)
    simpa [middleSwap, middleSwapMatrix, involutionElement, Matrix.mul_apply,
      Fin.sum_univ_succ] using h10

omit [CharP F 2] in
private theorem point_last_row (a : SU F (form F σ hσ)) (ha : a ∈ P) :
    a.val.val 3 1 = 0 ∧ a.val.val 3 2 = 0 := by
  obtain ⟨h10,h20,h30⟩ := (mem_pointParabolicSU F _ a).mp ha
  have h00 : a.val.val 0 0 ≠ 0 := by
    intro h00
    apply GeneralLinearGroup.det_ne_zero a.val
    apply Matrix.det_eq_zero_of_column_eq_zero 0
    intro i
    fin_cases i <;> simp_all
  have hs00 : σ (a.val.val 0 0) ≠ 0 := by simpa using h00
  have hu := a.property.1
  change (form F σ hσ).conjTranspose a.val.val * gram F * a.val.val = gram F at hu
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 1) hu
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 2) hu
  simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ, h10,h20,h30, hs00] at h01 h02
  exact ⟨h01,h02⟩

omit [CharP F 2] in
private theorem mem_borel_iff (a : SU F (form F σ hσ)) (ha : a ∈ P) :
    a ∈ B ↔ a.val.val 2 1 = 0 := by
  obtain ⟨h10,h20,h30⟩ := (mem_pointParabolicSU F _ a).mp ha
  have h31 := (point_last_row F σ hσ a ha).1
  change a ∈ P ∧ a ∈ planeParabolicSU F (form F σ hσ) ↔ _
  rw [mem_planeParabolicSU]
  simp [ha, h20,h30,h31]

private def upperPoint (t : F) (ht : σ t = t) : P :=
  ⟨upper F σ hσ t ht, (upper_mem_borel F σ hσ t ht).1⟩

private def middleSwapPoint : P :=
  ⟨middleSwap F σ hσ, middleSwap_mem_point F σ hσ⟩

private theorem exists_upper_mul_mem_borel (a : P) (ha : a.val ∉ B) :
    ∃ (t : F) (ht : σ t = t),
      middleSwapPoint F σ hσ * upperPoint F σ hσ t ht * a ∈ (B).subgroupOf P := by
  have h21 : a.val.val.val 2 1 ≠ 0 := by
    rwa [mem_borel_iff F σ hσ a.val a.property] at ha
  have h31 := (point_last_row F σ hσ a.val a.property).1
  let t := a.val.val.val 1 1 / a.val.val.val 2 1
  have ht : σ t = t := by
    have hi := column_isotropic F σ hσ a.val 1
    simp only [h31, map_zero, mul_zero, zero_mul, add_zero, zero_add] at hi
    dsimp [t]
    rw [map_div₀]
    have hs21 : σ (a.val.val.val 2 1) ≠ 0 := by simpa using h21
    field_simp [h21, hs21]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hi
  refine ⟨t, ht, ?_⟩
  change (middleSwapPoint F σ hσ * upperPoint F σ hσ t ht * a).val ∈ B
  rw [mem_borel_iff F σ hσ _ (SetLike.coe_mem _)]
  change ((middleSwap F σ hσ).val.val * (upper F σ hσ t ht).val.val *
    a.val.val.val) 2 1 = 0
  simp [middleSwap, middleSwapMatrix, upper, upperMatrix, involutionElement,
    Matrix.mul_apply, Fin.sum_univ_succ, t, div_mul_cancel₀ _ h21,
    CharTwo.add_self_eq_zero]

/-- The whole flag stabilizer is maximal inside the whole point parabolic. -/
theorem borel_subgroupOf_point_isCoatom : IsCoatom ((B).subgroupOf P) := by
  rw [SetLike.isCoatom_iff]
  refine ⟨?_, ?_⟩
  · intro h
    exact not_le_of_gt (borel_lt_point F σ hσ) (Subgroup.subgroupOf_eq_top.mp h)
  · intro H g hB hg hgin
    have hu (t : F) (ht : σ t = t) : upperPoint F σ hσ t ht ∈ H :=
      hB (upper_mem_borel F σ hσ t ht)
    obtain ⟨t, ht, htg⟩ := exists_upper_mul_mem_borel F σ hσ g hg
    have hw : middleSwapPoint F σ hσ ∈ H :=
      (H.mul_mem_cancel_right (hu t ht)).mp ((H.mul_mem_cancel_right hgin).mp (hB htg))
    apply top_unique
    intro a _
    by_cases ha : a.val ∈ B
    · exact hB ha
    · obtain ⟨s, hs, hsa⟩ := exists_upper_mul_mem_borel F σ hσ a ha
      exact (H.mul_mem_cancel_left (H.mul_mem hw (hu s hs))).mp (hB hsa)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointGeometry
