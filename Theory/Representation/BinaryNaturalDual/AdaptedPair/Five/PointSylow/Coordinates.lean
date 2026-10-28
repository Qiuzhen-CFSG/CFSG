module

public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Five.Basic
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four.Coordinates
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pair

/-!
# The upper stabilizer of the five-dimensional nonsingular pair

For the pair (e₃,e₃*), the inner upper stabilizer is obtained by setting the
four entries (1,3), (2,3), (3,4), (3,5) to zero (displayed indices are one-based).
Restriction to ker(e₃*) in the ordered basis e₁,e₂,e₄,e₅ identifies it with
U₄(2). The group equivalence is restriction, its inverse extends by the identity
on e₃, and the coordinate equivalence intertwines the actual actions.

The remaining six matrix entries have Lean indices (0,1), (0,3), (0,4),
(1,3), (1,4), (3,4). Counting the six independent entries of U₄(2) gives 64;
no enumeration of GL₅(2) is used.

Source: corrected Aschbacher–Smith H.9.1(4), printed p.390; adapted-pair
source audit of 6 October 2026. The general kernel restriction construction
is reused from `VectorStabilizers.Pair`.
-/

public section

open BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers
open BinaryNaturalDual.AdaptedPair.Four
namespace BinaryNaturalDual.AdaptedPair.Five

/-- The simultaneous stabilizer of e₃ and e₃*. -/
abbrev pairFive := pairStabilizer (axis (2 : Fin 5)) (coordinateForm 2)

/-- The actual inner upper pair stabilizer, before applying inner conjugation. -/
@[expose] def upperPointGroup : Subgroup (LinearGroup 5) := upperGroup 5 ⊓ pairFive

/-- The ordered indices e₁,e₂,e₄,e₅ of the kernel basis. -/
@[expose] def complementIndex (i : Fin 4) : Fin 5 := ![0, 1, 3, 4] i

/-- Coordinates on the actual covector kernel, deleting the third coordinate. -/
@[expose] def complementCoordinates : (coordinateForm (2 : Fin 5)).ker ≃ₗ[ZMod 2]
    BinaryLinear.OuterCyclic.Space 4 where
  toFun v i := v.val (complementIndex i)
  invFun w := ⟨![w 0, w 1, 0, w 2, w 3], rfl⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    have hv : v.val 2 = 0 := v.property
    fin_cases i <;> simp [complementIndex, hv]
  right_inv w := by ext i; fin_cases i <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def kernelGroupEquiv : BinaryLinear.GL (coordinateForm (2 : Fin 5)).ker ≃* LinearGroup 4 where
  toFun g := (complementCoordinates.symm.trans g).trans complementCoordinates
  invFun g := (complementCoordinates.trans g).trans complementCoordinates.symm
  left_inv g := by ext v; simp
  right_inv g := by ext v; simp
  map_mul' g h := by ext v; simp

/-- Restriction to the kernel, expressed in its displayed four-coordinate basis. -/
def pairFiveEquiv : pairFive ≃* LinearGroup 4 :=
  (pairStabilizerEquivKernel (by simp [axis] : coordinateForm (2 : Fin 5) (axis 2) = 1)).trans
    kernelGroupEquiv

theorem pairFiveEquiv_apply (g : pairFive) (w : BinaryLinear.OuterCyclic.Space 4) (i : Fin 4) :
    pairFiveEquiv g w i = g.val (complementCoordinates.symm w) (complementIndex i) := by
  rfl

theorem complementCoordinates_axis (j : Fin 4) :
    (complementCoordinates.symm (axis j) : BinaryLinear.OuterCyclic.Space 5) =
      axis (complementIndex j) := by
  ext i
  fin_cases i <;> fin_cases j <;> simp [complementCoordinates, complementIndex, axis]

theorem pairFiveEquiv_matrix (g : pairFive) (i j : Fin 4) :
    coordinateMatrix (pairFiveEquiv g) i j =
      coordinateMatrix g.val (complementIndex i) (complementIndex j) := by
  rw [coordinateMatrix_apply, pairFiveEquiv_apply, complementCoordinates_axis,
    coordinateMatrix_apply]

private theorem pair_matrix_row (g : pairFive) (j : Fin 5) :
    coordinateMatrix g.val 2 j = if (2 : Fin 5) = j then 1 else 0 := by
  rw [coordinateMatrix_apply]
  simpa [axis, Pi.single_apply, eq_comm] using g.property.2 (axis j)

private theorem pair_matrix_col (g : pairFive) (i : Fin 5) :
    coordinateMatrix g.val i 2 = if i = (2 : Fin 5) then 1 else 0 := by
  rw [coordinateMatrix_apply, g.property.1]
  simp [axis, Pi.single_apply]

theorem pairFiveEquiv_mem_upper (g : pairFive) :
    pairFiveEquiv g ∈ upperGroup 4 ↔ g.val ∈ upperGroup 5 := by
  simp only [mem_upperGroup_iff]
  constructor
  · intro h i j hji
    by_cases hi : i = 2
    · subst i
      rw [pair_matrix_row]
      exact if_neg (ne_of_gt (show j < (2 : Fin 5) from hji))
    by_cases hj : j = 2
    · subst j
      rw [pair_matrix_col]
      simp [hi]
    have hie : ∃ a, complementIndex a = i := by
      fin_cases i <;> simp_all [complementIndex]
      all_goals decide
    have hje : ∃ b, complementIndex b = j := by
      fin_cases j <;> simp_all [complementIndex]
      all_goals decide
    obtain ⟨a, rfl⟩ := hie
    obtain ⟨b, rfl⟩ := hje
    rw [← pairFiveEquiv_matrix]
    apply h
    fin_cases a <;> fin_cases b <;> simp_all [complementIndex]
  · intro h i j hji
    rw [pairFiveEquiv_matrix]
    apply h
    fin_cases i <;> fin_cases j <;> simp_all [complementIndex]

/-- Restriction identifies the full upper pair stabilizer with U₄(2). -/
noncomputable def upperPointEquiv : upperPointGroup ≃* upperGroup 4 where
  toFun g := ⟨pairFiveEquiv ⟨g.val, g.property.2⟩,
    (pairFiveEquiv_mem_upper _).mpr g.property.1⟩
  invFun g := ⟨(pairFiveEquiv.symm g.val).val,
    (pairFiveEquiv_mem_upper _).mp (by simpa only [MulEquiv.apply_symm_apply] using g.property),
    (pairFiveEquiv.symm g.val).property⟩
  left_inv g := by
    apply Subtype.ext
    exact congrArg (fun x : pairFive => x.val) (pairFiveEquiv.symm_apply_apply ⟨g.val, g.property.2⟩)
  right_inv g := by apply Subtype.ext; exact pairFiveEquiv.apply_symm_apply g.val
  map_mul' g h := by
    apply Subtype.ext
    exact pairFiveEquiv.map_mul ⟨g.val, g.property.2⟩ ⟨h.val, h.property.2⟩

theorem upperPointEquiv_intertwines (g : upperPointGroup)
    (w : (coordinateForm (2 : Fin 5)).ker) :
    (upperPointEquiv g).val (complementCoordinates w) =
      complementCoordinates (kernelAction (axis 2) (coordinateForm 2)
        ⟨g.val, g.property.2⟩ w) := by
  ext i
  change g.val (complementCoordinates.symm (complementCoordinates w)) (complementIndex i) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem upperPoint_mem_iff (g : LinearGroup 5) (hg : g ∈ upperGroup 5) :
    g ∈ upperPointGroup ↔ coordinateMatrix g 0 2 = 0 ∧ coordinateMatrix g 1 2 = 0 ∧
      coordinateMatrix g 2 3 = 0 ∧ coordinateMatrix g 2 4 = 0 := by
  have hu := (mem_upperGroup_iff g).mp hg
  have hd := upper_diagonal hg
  constructor
  · intro h
    exact ⟨by simpa using pair_matrix_col ⟨g, h.2⟩ 0,
      by simpa using pair_matrix_col ⟨g, h.2⟩ 1,
      by simpa using pair_matrix_row ⟨g, h.2⟩ 3,
      by simpa using pair_matrix_row ⟨g, h.2⟩ 4⟩
  · rintro ⟨h02, h12, h23, h24⟩
    refine ⟨hg, ?_, ?_⟩
    · ext i
      rw [← coordinateMatrix_apply]
      fin_cases i
      · simpa [axis] using h02
      · simpa [axis] using h12
      · simpa [axis] using hd 2
      · simpa [axis] using hu (by decide : (2 : Fin 5) < 3)
      · simpa [axis] using hu (by decide : (2 : Fin 5) < 4)
    · intro v
      change g v 2 = v 2
      rw [← coordinateMatrix_mulVec]
      have hr (j : Fin 5) : coordinateMatrix g 2 j = if j = 2 then 1 else 0 := by
        fin_cases j
        · simpa using hu (by decide : (0 : Fin 5) < 2)
        · simpa using hu (by decide : (1 : Fin 5) < 2)
        · simpa using hd 2
        · simpa using h23
        · simpa using h24
      simp [Matrix.mulVec, dotProduct, hr]

private abbrev FourUpperPosition := {ij : Fin 4 × Fin 4 // ij.1 < ij.2}
private def fourUpperMatrix (f : FourUpperPosition → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => if i = j then 1 else if h : i < j then f ⟨(i, j), h⟩ else 0
private theorem fourUpperMatrix_triangular (f : FourUpperPosition → ZMod 2) :
    (fourUpperMatrix f).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  simp only [fourUpperMatrix, if_neg (ne_of_gt hji), dif_neg (not_lt_of_ge hji.le)]
private theorem fourUpperMatrix_det (f : FourUpperPosition → ZMod 2) :
    (fourUpperMatrix f).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fourUpperMatrix_triangular f)]
  simp [fourUpperMatrix]
private def fourUpperSL (f : FourUpperPosition → ZMod 2) :
    Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨fourUpperMatrix f, fourUpperMatrix_det f⟩
private noncomputable def fourFromParameters (f : FourUpperPosition → ZMod 2) : upperGroup 4 :=
  ⟨slEquivLinear 4 (fourUpperSL f), by
    apply (mem_upperGroup_iff _).mpr
    change (((slEquivLinear 4).symm ((slEquivLinear 4) (fourUpperSL f))).val).IsUpperTriangular
    rw [MulEquiv.symm_apply_apply]
    exact fourUpperMatrix_triangular f⟩
private theorem matrix_fourFromParameters (f : FourUpperPosition → ZMod 2) :
    coordinateMatrix (fourFromParameters f).val = fourUpperMatrix f := by
  change (((slEquivLinear 4).symm ((slEquivLinear 4) (fourUpperSL f))).val) = _
  rw [MulEquiv.symm_apply_apply]
  rfl
private noncomputable def fourParametersEquiv : upperGroup 4 ≃ (FourUpperPosition → ZMod 2) where
  toFun g ij := coordinateMatrix g.val ij.val.1 ij.val.2
  invFun := fourFromParameters
  left_inv g := by
    apply Subtype.ext
    apply coordinateMatrix_injective
    rw [matrix_fourFromParameters]
    ext i j
    by_cases he : i = j
    · subst j
      simp [fourUpperMatrix, upper_diagonal g.property]
    · by_cases hij : i < j
      · simp [fourUpperMatrix, he, hij]
      · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm he)
        simp [fourUpperMatrix, he, hij, (mem_upperGroup_iff g.val).mp g.property hji]
  right_inv f := by
    funext ⟨⟨i, j⟩, hij⟩
    change coordinateMatrix (fourFromParameters f).val i j = f ⟨(i, j), hij⟩
    rw [matrix_fourFromParameters]
    simp [fourUpperMatrix, ne_of_lt hij, hij]

theorem upperFour_card : Nat.card (upperGroup 4) = 64 := by
  rw [Nat.card_congr fourParametersEquiv, Nat.card_fun]
  have hpos : Nat.card FourUpperPosition = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hpos]
  norm_num

theorem upperPointGroup_card : Nat.card upperPointGroup = 64 := by
  rw [Nat.card_congr upperPointEquiv.toEquiv, upperFour_card]

end BinaryNaturalDual.AdaptedPair.Five
