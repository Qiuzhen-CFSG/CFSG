module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceFlag
import Mathlib.Tactic.FinCases

/-!
# The two marked elementary rectangular groups

The six rectangular matrix entries give explicit additive coordinates for
both cuts of the binary five-space. Root words prove surjectivity, and
multiplication has no cross terms. The resulting membership tests retain
the actual matrix embedding, not just an abstract elementary-group type.

These are the order-64 assertions of Aschbacher, *Sporadic Groups* (1994),
39.1(3), printed p.213, used in the source Sylow fusion argument of 39.6.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
namespace RectangleCoordinates
abbrev F := ZMod 2
private abbrev trans {i j : Fin 5} (h : i < j) (a : F) : SL :=
  Matrix.SpecialLinearGroup.transvection (ne_of_lt h) a

private theorem trans_mem_rectangle {i j : Fin 5} (h : i < j) (c : ℕ)
    (hi : i.val < c) (hj : c ≤ j.val) (a : F) : trans h a ∈ rectangle c := by
  rcases (by decide : ∀ a : F, a = 0 ∨ a = 1) a with rfl | rfl
  · simp [trans]
  · exact subset_closure ⟨i, j, h, hi, hj, rfl⟩

private def word2 (v : Fin 6 → F) : SL :=
  trans (by decide : (0 : Fin 5) < 2) (v 0) *
  trans (by decide : (0 : Fin 5) < 3) (v 1) *
  trans (by decide : (0 : Fin 5) < 4) (v 2) *
  trans (by decide : (1 : Fin 5) < 2) (v 3) *
  trans (by decide : (1 : Fin 5) < 3) (v 4) *
  trans (by decide : (1 : Fin 5) < 4) (v 5)

private theorem word2_val (v : Fin 6 → F) : (word2 v).val =
  1 + Matrix.single 0 2 (v 0) + Matrix.single 0 3 (v 1) + Matrix.single 0 4 (v 2) + Matrix.single 1 2 (v 3) + Matrix.single 1 3 (v 4) + Matrix.single 1 4 (v 5) := by
  simp [word2, trans, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_of_ne, add_assoc]

private theorem word2_mem (v : Fin 6 → F) : word2 v ∈ rectangle 2 := by
  unfold word2
  repeat' apply Subgroup.mul_mem
  all_goals exact trans_mem_rectangle _ _ (by decide) (by decide) _

private theorem word2_add (v w : Fin 6 → F) : word2 (v + w) = word2 v * word2 w := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, word2_val]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Pi.add_apply, Matrix.single_add]
  simp only [Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (2 : Fin 5) ≠ 0),
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (3 : Fin 5) ≠ 0),
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (4 : Fin 5) ≠ 0),
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (2 : Fin 5) ≠ 1),
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (3 : Fin 5) ≠ 1),
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (4 : Fin 5) ≠ 1), add_zero]
  abel

private def hom2 : Multiplicative (Fin 6 → F) →* SL where
  toFun v := word2 v.toAdd
  map_one' := by apply Subtype.ext; simp [word2_val]
  map_mul' := word2_add

private theorem hom2_range : (hom2).range = rectangle 2 := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact word2_mem _
  · apply (closure_le _).mpr
    rintro _ ⟨i, j, hij, hi, hj, rfl⟩
    fin_cases i <;> fin_cases j <;> norm_num at *
    · refine ⟨Pi.single 0 (1 : F), ?_⟩
      change word2 (Pi.single 0 1) = root _
      apply Subtype.ext
      simp [word2_val, root, Matrix.SpecialLinearGroup.transvection_coe]
    · refine ⟨Pi.single 1 (1 : F), ?_⟩
      change word2 (Pi.single 1 1) = root _
      apply Subtype.ext
      simp [word2_val, root, Matrix.SpecialLinearGroup.transvection_coe]
    · refine ⟨Pi.single 2 (1 : F), ?_⟩
      change word2 (Pi.single 2 1) = root _
      apply Subtype.ext
      simp [word2_val, root, Matrix.SpecialLinearGroup.transvection_coe]
    · refine ⟨Pi.single 3 (1 : F), ?_⟩
      change word2 (Pi.single 3 1) = root _
      apply Subtype.ext
      simp [word2_val, root, Matrix.SpecialLinearGroup.transvection_coe]
    · refine ⟨Pi.single 4 (1 : F), ?_⟩
      change word2 (Pi.single 4 1) = root _
      apply Subtype.ext
      simp [word2_val, root, Matrix.SpecialLinearGroup.transvection_coe]
    · refine ⟨Pi.single 5 (1 : F), ?_⟩
      change word2 (Pi.single 5 1) = root _
      apply Subtype.ext
      simp [word2_val, root, Matrix.SpecialLinearGroup.transvection_coe]

private theorem hom2_injective : Function.Injective (hom2) := by
  intro v w he
  have he' : word2 v.toAdd = word2 w.toAdd := he
  apply Multiplicative.toAdd.injective
  funext k
  fin_cases k
  · have hh := congrArg (fun g : SL => g 0 2) he'
    simp only [word2_val] at hh
    simpa [Matrix.single] using hh
  · have hh := congrArg (fun g : SL => g 0 3) he'
    simp only [word2_val] at hh
    simpa [Matrix.single] using hh
  · have hh := congrArg (fun g : SL => g 0 4) he'
    simp only [word2_val] at hh
    simpa [Matrix.single] using hh
  · have hh := congrArg (fun g : SL => g 1 2) he'
    simp only [word2_val] at hh
    simpa [Matrix.single] using hh
  · have hh := congrArg (fun g : SL => g 1 3) he'
    simp only [word2_val] at hh
    simpa [Matrix.single] using hh
  · have hh := congrArg (fun g : SL => g 1 4) he'
    simp only [word2_val] at hh
    simpa [Matrix.single] using hh

/-- The six entries identify the actual rectangular group with binary six-space. -/
def coordinates2 : rectangle 2 ≃* Multiplicative (Fin 6 → F) :=
  ((MonoidHom.ofInjective (hom2_injective)).trans (MulEquiv.subgroupCongr hom2_range)).symm

/-- The literal rectangular root subgroup has order 64. -/
theorem card2 : Nat.card (rectangle 2) = 64 := by
  rw [Nat.card_congr coordinates2.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 6 → F) ≃ (Fin 6 → F))]
  simp [F]

/-- Vanishing outside the rectangle characterizes membership, retaining the embedding. -/
theorem mem2_iff (g : SL) : g ∈ rectangle 2 ↔
    ∀ i j : Fin 5, ¬ (i.val < 2 ∧ 2 ≤ j.val) → g i j = if i = j then 1 else 0 := by
  constructor
  · intro hg
    rw [← hom2_range] at hg
    obtain ⟨v, rfl⟩ := hg
    intro i j hij
    change (word2 _).val i j = _
    rw [word2_val]
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.single]
  · intro hg
    let v : Fin 6 → F := ![g 0 2,g 0 3,g 0 4,g 1 2,g 1 3,g 1 4]
    have he : g = word2 v := by
      apply Subtype.ext
      rw [word2_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.single, v]
      all_goals exact hg _ _ (by decide)
    rw [he]
    exact word2_mem _

private def word3 (v : Fin 6 → F) : SL :=
  trans (by decide : (0 : Fin 5) < 3) (v 0) *
  trans (by decide : (0 : Fin 5) < 4) (v 1) *
  trans (by decide : (1 : Fin 5) < 3) (v 2) *
  trans (by decide : (1 : Fin 5) < 4) (v 3) *
  trans (by decide : (2 : Fin 5) < 3) (v 4) *
  trans (by decide : (2 : Fin 5) < 4) (v 5)

private theorem word3_val (v : Fin 6 → F) : (word3 v).val =
  1 + Matrix.single 0 3 (v 0) + Matrix.single 0 4 (v 1) + Matrix.single 1 3 (v 2) + Matrix.single 1 4 (v 3) + Matrix.single 2 3 (v 4) + Matrix.single 2 4 (v 5) := by
  simp [word3, trans, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_of_ne, add_assoc]

private theorem word3_mem (v : Fin 6 → F) : word3 v ∈ rectangle 3 := by
  unfold word3
  repeat' apply Subgroup.mul_mem
  all_goals exact trans_mem_rectangle _ _ (by decide) (by decide) _

private theorem word3_add (v w : Fin 6 → F) : word3 (v + w) = word3 v * word3 w := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, word3_val]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Pi.add_apply, Matrix.single_add]
  simp only [Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (3 : Fin 5) ≠ 0),
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (4 : Fin 5) ≠ 0),
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (3 : Fin 5) ≠ 1),
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (4 : Fin 5) ≠ 1),
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (3 : Fin 5) ≠ 2),
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (4 : Fin 5) ≠ 2), add_zero]
  abel

private def hom3 : Multiplicative (Fin 6 → F) →* SL where
  toFun v := word3 v.toAdd
  map_one' := by apply Subtype.ext; simp [word3_val]
  map_mul' := word3_add

private theorem hom3_range : (hom3).range = rectangle 3 := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact word3_mem _
  · apply (closure_le _).mpr
    rintro _ ⟨i, j, hij, hi, hj, rfl⟩
    fin_cases i <;> fin_cases j <;> norm_num at *
    · refine ⟨Pi.single 0 (1 : F), ?_⟩
      change word3 (Pi.single 0 1) = root _
      apply Subtype.ext
      simp [word3_val, root, Matrix.SpecialLinearGroup.transvection_coe]
    · refine ⟨Pi.single 1 (1 : F), ?_⟩
      change word3 (Pi.single 1 1) = root _
      apply Subtype.ext
      simp [word3_val, root, Matrix.SpecialLinearGroup.transvection_coe]
    · refine ⟨Pi.single 2 (1 : F), ?_⟩
      change word3 (Pi.single 2 1) = root _
      apply Subtype.ext
      simp [word3_val, root, Matrix.SpecialLinearGroup.transvection_coe]
    · refine ⟨Pi.single 3 (1 : F), ?_⟩
      change word3 (Pi.single 3 1) = root _
      apply Subtype.ext
      simp [word3_val, root, Matrix.SpecialLinearGroup.transvection_coe]
    · refine ⟨Pi.single 4 (1 : F), ?_⟩
      change word3 (Pi.single 4 1) = root _
      apply Subtype.ext
      simp [word3_val, root, Matrix.SpecialLinearGroup.transvection_coe]
    · refine ⟨Pi.single 5 (1 : F), ?_⟩
      change word3 (Pi.single 5 1) = root _
      apply Subtype.ext
      simp [word3_val, root, Matrix.SpecialLinearGroup.transvection_coe]

private theorem hom3_injective : Function.Injective (hom3) := by
  intro v w he
  have he' : word3 v.toAdd = word3 w.toAdd := he
  apply Multiplicative.toAdd.injective
  funext k
  fin_cases k
  · have hh := congrArg (fun g : SL => g 0 3) he'
    simp only [word3_val] at hh
    simpa [Matrix.single] using hh
  · have hh := congrArg (fun g : SL => g 0 4) he'
    simp only [word3_val] at hh
    simpa [Matrix.single] using hh
  · have hh := congrArg (fun g : SL => g 1 3) he'
    simp only [word3_val] at hh
    simpa [Matrix.single] using hh
  · have hh := congrArg (fun g : SL => g 1 4) he'
    simp only [word3_val] at hh
    simpa [Matrix.single] using hh
  · have hh := congrArg (fun g : SL => g 2 3) he'
    simp only [word3_val] at hh
    simpa [Matrix.single] using hh
  · have hh := congrArg (fun g : SL => g 2 4) he'
    simp only [word3_val] at hh
    simpa [Matrix.single] using hh

/-- The six entries identify the actual rectangular group with binary six-space. -/
def coordinates3 : rectangle 3 ≃* Multiplicative (Fin 6 → F) :=
  ((MonoidHom.ofInjective (hom3_injective)).trans (MulEquiv.subgroupCongr hom3_range)).symm

/-- The literal rectangular root subgroup has order 64. -/
theorem card3 : Nat.card (rectangle 3) = 64 := by
  rw [Nat.card_congr coordinates3.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 6 → F) ≃ (Fin 6 → F))]
  simp [F]

/-- Vanishing outside the rectangle characterizes membership, retaining the embedding. -/
theorem mem3_iff (g : SL) : g ∈ rectangle 3 ↔
    ∀ i j : Fin 5, ¬ (i.val < 3 ∧ 3 ≤ j.val) → g i j = if i = j then 1 else 0 := by
  constructor
  · intro hg
    rw [← hom3_range] at hg
    obtain ⟨v, rfl⟩ := hg
    intro i j hij
    change (word3 _).val i j = _
    rw [word3_val]
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.single]
  · intro hg
    let v : Fin 6 → F := ![g 0 3,g 0 4,g 1 3,g 1 4,g 2 3,g 2 4]
    have he : g = word3 v := by
      apply Subtype.ext
      rw [word3_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.single, v]
      all_goals exact hg _ _ (by decide)
    rw [he]
    exact word3_mem _

end RectangleCoordinates
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The original plane root group has order 64 under the full marking. -/
theorem source_plane_card : Nat.card F.plane = 64 := by
  rw [Nat.card_congr (F.pullbackEquiv Model.plane Model.plane_le_centralizer).toEquiv]
  exact RectangleCoordinates.card2

/-- The original three-space root group has order 64 under the full marking. -/
theorem source_threeSpace_card : Nat.card F.threeSpace = 64 := by
  rw [Nat.card_congr (F.pullbackEquiv Model.threeSpace Model.threeSpace_le_centralizer).toEquiv]
  exact RectangleCoordinates.card3

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
