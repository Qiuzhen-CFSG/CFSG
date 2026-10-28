module

public import Theory.SpecificGroups.BinaryFour.SplitBlockPair
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Group.Prod

/-!
# The local groups of the split binary four-dimensional pair

The row involution and simultaneous permutations of the three nonzero binary
columns give the faithful C₂ × S₃ action. The other local group permutes the
four basis vectors `(0010), (0011), (1010), (1111)` as A₄. The checked normal
forms show that these embeddings have exactly the published generated groups
as their images, giving actual multiplicative equivalences.

The common row–column subgroup is C₂ × C₂. Inside the parabolic it is exactly
the stabilizer of `(0100)`, whereas the whole A₄ fixes that vector. This proves
the precise intersection and gives the A₄ inclusion into the marked stabilizer
of the joined group. The generator and evaluation equations retain the original
embeddings throughout. No identification of the whole join or its full marked
stabilizer is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 14.4.4, printed p.1007, the GL₄(2) local-image calculation.
-/

public section

namespace BinaryFourSplitPair
open Equiv
abbrev ParabolicModel := Multiplicative (ZMod 2) × Perm (Fin 3)

private def nonzeroColumn : Fin 3 → Fin 2 → ZMod 2 := ![![1,0], ![0,1], ![1,1]]
private def columnPermFun (p : Perm (Fin 3)) (v : V) : V :=
  ![v 0 * nonzeroColumn (p 0) 0 + v 1 * nonzeroColumn (p 1) 0,
    v 0 * nonzeroColumn (p 0) 1 + v 1 * nonzeroColumn (p 1) 1,
    v 2 * nonzeroColumn (p 0) 0 + v 3 * nonzeroColumn (p 1) 0,
    v 2 * nonzeroColumn (p 0) 1 + v 3 * nonzeroColumn (p 1) 1]
private theorem dot_add (a b c d x y : ZMod 2) :
    (a + b) * x + (c + d) * y = (a * x + c * y) + (b * x + d * y) := by
  rw [add_mul, add_mul, add_add_add_comm]

private def columnPerm (p : Perm (Fin 3)) : MulAut E :=
  AddEquiv.toMultiplicative {
    toFun := columnPermFun p
    invFun := columnPermFun p⁻¹
    left_inv := by revert p; decide +kernel
    right_inv := by revert p; decide +kernel
    map_add' := by
      intro v w
      funext i
      fin_cases i <;> exact dot_add _ _ _ _ _ _ }

private def rowEmbedding : Multiplicative (ZMod 2) →* MulAut E where
  toFun x := if x = 1 then 1 else row
  map_one' := by simp
  map_mul' := by
    intro x y
    apply MulEquiv.ext
    revert x y
    decide +kernel

private def columnVectorFun (p : Perm (Fin 3)) (v : Fin 2 → ZMod 2) : Fin 2 → ZMod 2 :=
  ![v 0 * nonzeroColumn (p 0) 0 + v 1 * nonzeroColumn (p 1) 0,
    v 0 * nonzeroColumn (p 0) 1 + v 1 * nonzeroColumn (p 1) 1]

private theorem columnVector_mul : ∀ p q : Perm (Fin 3), ∀ v : Fin 2 → ZMod 2,
    columnVectorFun (p * q) v = columnVectorFun p (columnVectorFun q v) := by
  decide +kernel

private def columnEmbedding : Perm (Fin 3) →* MulAut E where
  toFun := columnPerm
  map_one' := by apply MulEquiv.ext; decide +kernel
  map_mul' p q := by
    apply MulEquiv.ext
    intro v
    apply funext
    intro i
    fin_cases i
    · exact congrFun (columnVector_mul p q ![v.toAdd 0, v.toAdd 1]) 0
    · exact congrFun (columnVector_mul p q ![v.toAdd 0, v.toAdd 1]) 1
    · exact congrFun (columnVector_mul p q ![v.toAdd 2, v.toAdd 3]) 0
    · exact congrFun (columnVector_mul p q ![v.toAdd 2, v.toAdd 3]) 1

private theorem row_columnEmbedding_commute (x : Multiplicative (ZMod 2))
    (p : Perm (Fin 3)) : columnEmbedding p * rowEmbedding x =
      rowEmbedding x * columnEmbedding p := by
  apply MulEquiv.ext
  revert x p
  decide +kernel

def parabolicEmbedding : ParabolicModel →* MulAut E where
  toFun x := rowEmbedding x.1 * columnEmbedding x.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    rw [mul_assoc (rowEmbedding x.1), ← mul_assoc (rowEmbedding y.1),
      ← row_columnEmbedding_commute, mul_assoc, mul_assoc]

theorem parabolicEmbedding_injective : Function.Injective parabolicEmbedding := by
  have h : ∀ x : ParabolicModel,
      (∀ v : E, parabolicEmbedding x v = v) → x = 1 := by
    decide +kernel
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  exact h x (fun v => DFunLike.congr_fun hx v)


private def tetraBasis : MulAut E := AddEquiv.toMultiplicative {
  toFun := fun v : V => ![v 2 + v 3, v 3, v 0 + v 1 + v 2 + v 3, v 1 + v 3]
  invFun := fun v : V => ![v 0 + v 1 + v 2 + v 3, v 1 + v 3, v 0 + v 1, v 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel }
private def permCoordinates (p : Perm (Fin 4)) : MulAut E :=
  AddEquiv.toMultiplicative {
    toFun := fun v : V => fun i => v (p⁻¹ i)
    invFun := fun v : V => v ∘ p
    left_inv := by intro v; funext i; simp
    right_inv := by intro v; funext i; simp
    map_add' := by intros; rfl }

private def permutationEmbedding : Perm (Fin 4) →* MulAut E where
  toFun := permCoordinates
  map_one' := by apply MulEquiv.ext; intro v; rfl
  map_mul' x y := by apply MulEquiv.ext; intro v; rfl

def quaternionEmbedding : alternatingGroup (Fin 4) →* MulAut E :=
  (MulAut.conj tetraBasis).toMonoidHom.comp
    (permutationEmbedding.comp (alternatingGroup (Fin 4)).subtype)

theorem quaternionEmbedding_injective : Function.Injective quaternionEmbedding := by
  have h : ∀ x : alternatingGroup (Fin 4),
      (∀ v : E, quaternionEmbedding x v = v) → x = 1 := by
    decide +kernel
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  exact h x (fun v => DFunLike.congr_fun hx v)


/-- Standard generators of the row factor and the column S₃. -/
@[expose] def parabolicRow : ParabolicModel := (Multiplicative.ofAdd 1, 1)
@[expose] def parabolicColumn : ParabolicModel := (1, swap 0 2)
@[expose] def parabolicCubic : ParabolicModel := (1, swap 0 1 * swap 1 2)

@[simp] theorem parabolicEmbedding_row : parabolicEmbedding parabolicRow = row := by
  apply MulEquiv.ext
  decide +kernel
@[simp] theorem parabolicEmbedding_column : parabolicEmbedding parabolicColumn = column := by
  apply MulEquiv.ext
  decide +kernel
@[simp] theorem parabolicEmbedding_cubic : parabolicEmbedding parabolicCubic = columnCubic := by
  apply MulEquiv.ext
  decide +kernel

private theorem parabolicModel_normalForm : ∀ x : ParabolicModel,
    ∃ i j : Fin 2, ∃ k : Fin 3,
      x = parabolicRow ^ i.val * parabolicColumn ^ j.val * parabolicCubic ^ k.val := by
  decide +kernel

theorem row_mem_parabolic : row ∈ parabolic := Subgroup.subset_closure (by simp)
theorem column_mem_parabolic : column ∈ parabolic := Subgroup.subset_closure (by simp)
theorem columnCubic_mem_parabolic : columnCubic ∈ parabolic := Subgroup.subset_closure (by simp)

theorem parabolicEmbedding_range : parabolicEmbedding.range = parabolic := by
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    obtain ⟨i,j,k,rfl⟩ := parabolicModel_normalForm x
    simp only [map_mul, map_pow, parabolicEmbedding_row, parabolicEmbedding_column,
      parabolicEmbedding_cubic]
    exact parabolic.mul_mem (parabolic.mul_mem
      (parabolic.pow_mem row_mem_parabolic _) (parabolic.pow_mem column_mem_parabolic _))
      (parabolic.pow_mem columnCubic_mem_parabolic _)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨parabolicRow, parabolicEmbedding_row⟩
    · exact ⟨parabolicColumn, parabolicEmbedding_column⟩
    · exact ⟨parabolicCubic, parabolicEmbedding_cubic⟩

/-- The literal parabolic action is C₂ × S₃. -/
@[expose] noncomputable def parabolicEquiv : parabolic ≃* ParabolicModel :=
  ((MonoidHom.ofInjective parabolicEmbedding_injective).trans
    (MulEquiv.subgroupCongr parabolicEmbedding_range)).symm

@[simp] theorem parabolicEquiv_symm_coe (x : ParabolicModel) :
    (parabolicEquiv.symm x : MulAut E) = parabolicEmbedding x := rfl

theorem parabolicEquiv_action (g : parabolic) (v : E) :
    parabolicEmbedding (parabolicEquiv g) v = g.val v := by
  have h := congrArg (fun a : parabolic => a.val v) (parabolicEquiv.symm_apply_apply g)
  exact h

/-- The double transpositions and the cycling three-cycle in the tetrahedron. -/
@[expose] def quaternionRow : alternatingGroup (Fin 4) :=
  ⟨swap 0 2 * swap 1 3, by change Perm.sign _ = 1; decide +kernel⟩
@[expose] def quaternionColumn : alternatingGroup (Fin 4) :=
  ⟨swap 0 1 * swap 2 3, by change Perm.sign _ = 1; decide +kernel⟩
@[expose] def quaternionCubic : alternatingGroup (Fin 4) :=
  ⟨swap 1 3 * swap 3 2, by change Perm.sign _ = 1; decide +kernel⟩

@[simp] theorem quaternionEmbedding_row : quaternionEmbedding quaternionRow = row := by
  apply MulEquiv.ext
  decide +kernel
@[simp] theorem quaternionEmbedding_column : quaternionEmbedding quaternionColumn = column := by
  apply MulEquiv.ext
  decide +kernel
@[simp] theorem quaternionEmbedding_cubic :
    quaternionEmbedding quaternionCubic = normalizingCubic := by
  apply MulEquiv.ext
  decide +kernel

private theorem quaternionModel_normalForm : ∀ x : alternatingGroup (Fin 4),
    ∃ i j : Fin 2, ∃ k : Fin 3,
      x = quaternionRow ^ i.val * quaternionColumn ^ j.val * quaternionCubic ^ k.val := by
  decide +kernel

theorem row_mem_quaternion : row ∈ quaternion := Subgroup.subset_closure (by simp)
theorem column_mem_quaternion : column ∈ quaternion := Subgroup.subset_closure (by simp)
theorem normalizingCubic_mem_quaternion : normalizingCubic ∈ quaternion :=
  Subgroup.subset_closure (by simp)

theorem quaternionEmbedding_range : quaternionEmbedding.range = quaternion := by
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    obtain ⟨i,j,k,rfl⟩ := quaternionModel_normalForm x
    simp only [map_mul, map_pow, quaternionEmbedding_row, quaternionEmbedding_column,
      quaternionEmbedding_cubic]
    exact quaternion.mul_mem (quaternion.mul_mem
      (quaternion.pow_mem row_mem_quaternion _) (quaternion.pow_mem column_mem_quaternion _))
      (quaternion.pow_mem normalizingCubic_mem_quaternion _)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨quaternionRow, quaternionEmbedding_row⟩
    · exact ⟨quaternionColumn, quaternionEmbedding_column⟩
    · exact ⟨quaternionCubic, quaternionEmbedding_cubic⟩

/-- The literal quaternion-normalizer action is A₄. -/
@[expose] noncomputable def quaternionEquiv : quaternion ≃* alternatingGroup (Fin 4) :=
  ((MonoidHom.ofInjective quaternionEmbedding_injective).trans
    (MulEquiv.subgroupCongr quaternionEmbedding_range)).symm

@[simp] theorem quaternionEquiv_symm_coe (x : alternatingGroup (Fin 4)) :
    (quaternionEquiv.symm x : MulAut E) = quaternionEmbedding x := rfl

theorem quaternionEquiv_action (g : quaternion) (v : E) :
    quaternionEmbedding (quaternionEquiv g) v = g.val v := by
  exact congrArg (fun a : quaternion => a.val v) (quaternionEquiv.symm_apply_apply g)

/-- A basis permuted by the quaternion-normalizer image. -/
@[expose] def tetrahedron : Fin 4 → E := ![
  Multiplicative.ofAdd ![0,0,1,0], Multiplicative.ofAdd ![0,0,1,1],
  Multiplicative.ofAdd ![1,0,1,0], Multiplicative.ofAdd ![1,1,1,1]]

theorem quaternionEmbedding_tetrahedron (p : alternatingGroup (Fin 4)) (i : Fin 4) :
    quaternionEmbedding p (tetrahedron i) = tetrahedron (p.val i) := by
  revert p i
  decide +kernel

theorem quaternion_fixes_point (g : quaternion) : g.val point = point := by
  rw [← quaternionEquiv_action]
  have h : ∀ p : alternatingGroup (Fin 4), quaternionEmbedding p point = point := by
    decide +kernel
  exact h _

theorem parabolic_card : Nat.card parabolic = 12 := by
  rw [Nat.card_congr parabolicEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

theorem quaternion_card : Nat.card quaternion = 12 := by
  rw [Nat.card_congr quaternionEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

abbrev FourModel := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

/-- The actual two independent commuting involutions. -/
@[expose] def fourEmbedding : FourModel →* MulAut E where
  toFun x := (if x.1 = 1 then 1 else row) * (if x.2 = 1 then 1 else column)
  map_one' := by simp
  map_mul' := by
    intro x y
    apply MulEquiv.ext
    revert x y
    decide +kernel

theorem fourEmbedding_injective : Function.Injective fourEmbedding := by
  have h : ∀ x : FourModel, (∀ v : E, fourEmbedding x v = v) → x = 1 := by
    decide +kernel
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  exact h x (fun v => DFunLike.congr_fun hx v)

theorem row_mem_overlap : row ∈ overlap := Subgroup.subset_closure (by simp)
theorem column_mem_overlap : column ∈ overlap := Subgroup.subset_closure (by simp)

theorem fourEmbedding_range : fourEmbedding.range = overlap := by
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    apply overlap.mul_mem
    · split_ifs
      · exact overlap.one_mem
      · exact row_mem_overlap
    · split_ifs
      · exact overlap.one_mem
      · exact column_mem_overlap
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · refine ⟨(Multiplicative.ofAdd 1, 1), ?_⟩
      apply MulEquiv.ext
      decide +kernel
    · refine ⟨(1, Multiplicative.ofAdd 1), ?_⟩
      apply MulEquiv.ext
      decide +kernel

/-- Identification of the embedded common Klein four-group. -/
@[expose] noncomputable def overlapEquiv : overlap ≃* FourModel :=
  ((MonoidHom.ofInjective fourEmbedding_injective).trans
    (MulEquiv.subgroupCongr fourEmbedding_range)).symm

@[simp] theorem overlapEquiv_symm_coe (x : FourModel) :
    (overlapEquiv.symm x : MulAut E) = fourEmbedding x := rfl

theorem overlap_card : Nat.card overlap = 4 := by
  rw [Nat.card_congr overlapEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

theorem overlap_le_parabolic : overlap ≤ parabolic := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact row_mem_parabolic
  · exact column_mem_parabolic

theorem overlap_le_quaternion : overlap ≤ quaternion := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact row_mem_quaternion
  · exact column_mem_quaternion

/-- The parabolic words give a small exhaustive normal form in the actual action. -/
theorem parabolic_normalForm (g : MulAut E) (hg : g ∈ parabolic) :
    ∃ i j : Fin 2, ∃ k : Fin 3,
      g = row ^ i.val * column ^ j.val * columnCubic ^ k.val := by
  rw [← parabolicEmbedding_range] at hg
  obtain ⟨x,rfl⟩ := hg
  obtain ⟨i,j,k,rfl⟩ := parabolicModel_normalForm x
  exact ⟨i,j,k, by simp only [map_mul, map_pow, parabolicEmbedding_row,
    parabolicEmbedding_column, parabolicEmbedding_cubic]⟩

/-- Within the parabolic, the marked point's stabilizer is precisely the overlap. -/
theorem parabolic_fixes_point_iff (g : MulAut E) (hg : g ∈ parabolic) :
    g point = point ↔ g ∈ overlap := by
  constructor
  · intro hf
    obtain ⟨i,j,k,rfl⟩ := parabolic_normalForm g hg
    have h : ∀ i j : Fin 2, ∀ k : Fin 3,
        (row ^ i.val * column ^ j.val * columnCubic ^ k.val) point = point → k = 0 := by
      decide +kernel
    have hk := h i j k hf
    rw [hk]
    simp only [Fin.val_zero, pow_zero, mul_one]
    exact overlap.mul_mem (overlap.pow_mem row_mem_overlap _)
      (overlap.pow_mem column_mem_overlap _)
  · intro hf
    exact quaternion_fixes_point ⟨g, overlap_le_quaternion hf⟩

/-- The two local images meet in their literal common four-group. -/
theorem parabolic_inf_quaternion : parabolic ⊓ quaternion = overlap := by
  apply le_antisymm
  · intro g hg
    exact (parabolic_fixes_point_iff g hg.1).mp (quaternion_fixes_point ⟨g,hg.2⟩)
  · exact le_inf overlap_le_parabolic overlap_le_quaternion

/-- Both local identifications retain the same embedded overlap action. -/
theorem overlap_actions_compatible (g : overlap) (v : E) :
    parabolicEmbedding (parabolicEquiv ⟨g.val, overlap_le_parabolic g.property⟩) v =
    quaternionEmbedding (quaternionEquiv ⟨g.val, overlap_le_quaternion g.property⟩) v := by
  rw [parabolicEquiv_action, quaternionEquiv_action]

/-- The full A₄ image lies in the marked stabilizer for the joined evaluation action. -/
@[expose] def quaternionToPointStabilizer : quaternion →* MulAction.stabilizer joined point :=
  (Subgroup.inclusion (show quaternion ≤ joined from le_sup_right)).codRestrict _
    (fun g => quaternion_fixes_point g)

theorem quaternionToPointStabilizer_injective :
    Function.Injective quaternionToPointStabilizer := by
  intro x y h
  exact Subtype.ext (congrArg (fun a : MulAction.stabilizer joined point => a.val.val) h)

@[simp] theorem quaternionToPointStabilizer_coe (g : quaternion) :
    (quaternionToPointStabilizer g).val.val = g.val := rfl

end BinaryFourSplitPair
