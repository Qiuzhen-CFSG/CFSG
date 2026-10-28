module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceFaithfulness
import Mathlib.Tactic.FinCases

/-!
# The marked row subgroup and its normalizer action

The first row roots generate the additive four-space: a word in the four
root directions has exactly the corresponding four off-diagonal entries.
Commuting with these roots forces every other row of a matrix to be an
identity row. Thus this group is self-centralizing. A matrix centralizing
the distinguished root fixes the first coordinate column, and conjugation
preserves the row group.

Transport through the full marked centralizer proves relative normality,
self-centralization and explicit coordinates in the original group. The
literal quotient of its normalizer by the row group consequently acts
faithfully on it. The stabilizer of the marked point is the original point
centralizer. Finally, twenty-one fused points in the marked plane cannot
all lie in the sixteen-element row group; the resulting outside point is
still in its normalizer.

These are the row-group and faithful-action inputs of Aschbacher,
*Sporadic Groups* (1994), 39.1(2), the first paragraph of 39.3, and the
fusion alternative used in 39.8, pp.213–216. The full normalizer structure,
splitting, source generation and local comparison remain separate proofs;
this module does not assert existence of `SourceComparison`.
-/

public section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear

private def rowWord (a b c d : ZMod 2) : SL :=
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 1) a *
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 2) b *
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 3) c *
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 4) d

private theorem rowWord_val (a b c d : ZMod 2) :
    (rowWord a b c d : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      1 + Matrix.single 0 1 a + Matrix.single 0 2 b + Matrix.single 0 3 c +
      Matrix.single 0 4 d := by
  simp [rowWord, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_of_ne, add_assoc]

private theorem rowWord_mem (a b c d : ZMod 2) : rowWord a b c d ∈ Model.row := by
  have h (j : Fin 5) (hj : 0 < j) (a : ZMod 2) :
      Matrix.SpecialLinearGroup.transvection (ne_of_lt hj) a ∈ Model.row := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · simp
    · exact subset_closure ⟨j, hj, rfl⟩
  exact Model.row.mul_mem (Model.row.mul_mem (Model.row.mul_mem
    (h 1 (by decide) a) (h 2 (by decide) b)) (h 3 (by decide) c)) (h 4 (by decide) d)

private theorem centralizer_row_entries (g : SL)
    (hg : g ∈ Subgroup.centralizer (Model.row : Set SL))
    (j : Fin 5) (hj : j ≠ 0) (k : Fin 5) :
    (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) j k =
      if k = j then g 0 0 else 0 := by
  have hroot : root (show 0 < j from Fin.pos_iff_ne_zero.mpr hj) ∈ Model.row :=
    subset_closure ⟨j, Fin.pos_iff_ne_zero.mpr hj, rfl⟩
  have he := congrArg (fun m : SL => m 0 k) (mem_centralizer_iff.mp hg _ hroot)
  change (((1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) + Matrix.single 0 j 1) * (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) (0 : Fin 5) k =
    ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (1 + Matrix.single 0 j 1) : Matrix (Fin 5) (Fin 5) (ZMod 2)) (0 : Fin 5) k at he
  by_cases hk : k = j
  · subst k
    simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.add_apply, Matrix.single_mul_apply_same, Matrix.mul_single_apply_same,
      one_mul, mul_one, add_right_inj, ite_true] using he
  · simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.add_apply, Matrix.single_mul_apply_same,
      Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, one_mul, add_zero, add_eq_left,
      if_neg hk] using he

private theorem centralizer_row_diagonal (g : SL)
    (hg : g ∈ Subgroup.centralizer (Model.row : Set SL)) : g 0 0 = 1 := by
  have hne : g 0 0 ≠ 0 := by
    intro he
    apply g.det_ne_zero
    apply Matrix.det_eq_zero_of_column_eq_zero 0
    intro i
    by_cases hi : i = 0
    · simpa only [hi] using he
    · simp [centralizer_row_entries g hg i hi 0, Ne.symm hi]
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hne

private theorem row_word_eq (g : SL) (h00 : g 0 0 = 1)
    (hrows : ∀ (i j : Fin 5), i ≠ 0 → g i j = if i = j then 1 else 0) :
    g = rowWord (g 0 1) (g 0 2) (g 0 3) (g 0 4) := by
  apply Subtype.ext
  ext i j
  rw [rowWord_val]
  by_cases hi : i = 0
  · subst i
    fin_cases j <;> simp [h00, Matrix.single]
  · rw [hrows i j hi]
    simp [Matrix.single, Ne.symm hi, Matrix.one_apply]

private theorem row_of_entries (g : SL) (h00 : g 0 0 = 1)
    (hrows : ∀ (i j : Fin 5), i ≠ 0 → g i j = if i = j then 1 else 0) :
    g ∈ Model.row := by
  rw [row_word_eq g h00 hrows]
  exact rowWord_mem _ _ _ _

private theorem centralizer_row_le :
    Subgroup.centralizer (Model.row : Set SL) ≤ Model.row := by
  intro g hg
  apply row_of_entries g (centralizer_row_diagonal g hg)
  intro i j hi
  rw [centralizer_row_entries g hg i hi j, centralizer_row_diagonal g hg]
  simp only [eq_comm]

private theorem row_commutative : IsMulCommutative Model.row := by
  apply isMulCommutative_closure
  rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩
  apply Subtype.ext
  simp [root, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, ne_of_gt hj, ne_of_gt hk, add_comm, add_left_comm]

private theorem centralizer_row_eq :
    Subgroup.centralizer (Model.row : Set SL) = Model.row := by
  apply le_antisymm centralizer_row_le
  let := row_commutative
  intro g hg
  exact mem_centralizer_iff.mpr fun x hx => setLike_mul_comm hx hg


/-- The first-row entries identify the model root group with binary four-space. -/
def modelRowCoordinates : Model.row ≃* Multiplicative (Fin 4 → ZMod 2) where
  toFun g := Multiplicative.ofAdd (fun i => (g : SL) 0 i.succ)
  invFun v := ⟨rowWord (v.toAdd 0) (v.toAdd 1) (v.toAdd 2) (v.toAdd 3), rowWord_mem _ _ _ _⟩
  left_inv g := by
    apply Subtype.ext
    have hg : (g : SL) ∈ Subgroup.centralizer (Model.row : Set SL) :=
      centralizer_row_eq.symm ▸ g.property
    apply Eq.symm
    apply row_word_eq g (centralizer_row_diagonal (g : SL) hg)
    intro i j hi
    rw [centralizer_row_entries g hg i hi j, centralizer_row_diagonal g hg]
    simp only [eq_comm]
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    change (rowWord (v.toAdd 0) (v.toAdd 1) (v.toAdd 2) (v.toAdd 3) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 i.succ = v.toAdd i
    rw [rowWord_val]
    fin_cases i <;> simp [Matrix.single]
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    funext i
    change (((g : SL) * (h : SL) : SL) : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 i.succ =
      (g : SL) 0 i.succ + (h : SL) 0 i.succ
    have hg : (g : SL) ∈ Subgroup.centralizer (Model.row : Set SL) :=
      centralizer_row_eq.symm ▸ g.property
    have hh : (h : SL) ∈ Subgroup.centralizer (Model.row : Set SL) :=
      centralizer_row_eq.symm ▸ h.property
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    fin_cases i <;>
      simp [Fin.sum_univ_succ, centralizer_row_entries (h : SL) hh,
        centralizer_row_diagonal (g : SL) hg, centralizer_row_diagonal (h : SL) hh, add_comm]

/-- All entries of a row element are determined by its four marked coordinates. -/
theorem modelRowCoordinates_matrix (g : Model.row) :
    (g.val : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      1 + Matrix.single 0 1 ((modelRowCoordinates g).toAdd 0) +
        Matrix.single 0 2 ((modelRowCoordinates g).toAdd 1) +
        Matrix.single 0 3 ((modelRowCoordinates g).toAdd 2) +
        Matrix.single 0 4 ((modelRowCoordinates g).toAdd 3) := by
  have hg : (g : SL) ∈ Subgroup.centralizer (Model.row : Set SL) :=
    centralizer_row_eq.symm ▸ g.property
  have he := row_word_eq g (centralizer_row_diagonal g hg) (by
    intro i j hi
    rw [centralizer_row_entries g hg i hi j, centralizer_row_diagonal g hg]
    simp only [eq_comm])
  exact (congrArg Subtype.val he).trans (rowWord_val _ _ _ _)

private theorem centralizer_firstColumn (g : SL) (hg : g ∈ centralizer) :
    ∀ i : Fin 5, g i 0 = if i = 0 then 1 else 0 := by
  have hcomm : transvection * g = g * transvection :=
    (mem_centralizer_singleton_iff.mp hg).symm
  have hzero (i : Fin 5) (hi : i ≠ 0) : g i 0 = 0 := by
    have he := congrArg (fun a : SL => a i 4) hcomm
    change (((1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) + Matrix.single 0 4 1) *
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) i 4 =
      ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (1 + Matrix.single 0 4 1) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) i 4 at he
    simpa [Matrix.add_mul, Matrix.mul_add, hi, eq_comm] using he
  have h00 : g 0 0 = 1 := by
    apply (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1)
    intro he
    apply g.det_ne_zero (Matrix.det_eq_zero_of_column_eq_zero 0 ?_)
    intro i
    by_cases hi : i = 0
    · simpa only [hi] using he
    · exact hzero i hi
  intro i
  by_cases hi : i = 0
  · simpa only [hi, ite_true] using h00
  · simpa only [if_neg hi] using hzero i hi

private theorem row_product_of_firstColumns (g k : SL) (hmul : g * k = 1)
    (hgcol : ∀ i : Fin 5, g i 0 = if i = 0 then 1 else 0)
    (hkcol : ∀ i : Fin 5, k i 0 = if i = 0 then 1 else 0)
    (j : Fin 5) (hj : 0 < j) : g * root hj * k ∈ Model.row := by
  have hsingle :
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * Matrix.single 0 j 1 = Matrix.single 0 j 1 := by
    ext i k
    by_cases hk : k = j
    · subst k
      rw [Matrix.mul_single_apply_same, mul_one, hgcol]
      by_cases hi : i = 0
      · simp [hi, Matrix.single]
      · simp [hi, Ne.symm hi, Matrix.single]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk]
      simp [Matrix.single, Ne.symm hk]
  have he : ((g * root hj * k : SL) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      1 + Matrix.single 0 j 1 * ((k : SL) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
    change (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (1 + Matrix.single 0 j 1) *
      ((k : SL) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = _
    rw [Matrix.mul_add, Matrix.mul_one, hsingle, Matrix.add_mul]
    rw [← Matrix.SpecialLinearGroup.coe_mul, hmul, Matrix.SpecialLinearGroup.coe_one]
  apply row_of_entries
  · rw [he]
    rw [Matrix.add_apply, Matrix.single_mul_apply_same, one_mul]
    change 1 + (k : SL) j 0 = 1
    rw [hkcol, if_neg (ne_of_gt hj), add_zero]
  · intro i l hi
    rw [he]
    rw [Matrix.add_apply, Matrix.single_mul_apply_of_ne _ _ _ _ _ hi, add_zero, Matrix.one_apply]

private theorem normalizes_closure_of_generators {A : Type*} [Group A]
    (C : Subgroup A) (s : Set A)
    (h : ∀ g ∈ C, ∀ a ∈ s, g * a * g⁻¹ ∈ Subgroup.closure s) :
    C ≤ normalizer (Subgroup.closure s : Set A) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg
  change Subgroup.closure s ≤ (Subgroup.closure s).comap (MulAut.conj g).toMonoidHom
  exact (closure_le _).mpr (h g hg)

private theorem centralizer_normalizes_row :
    centralizer ≤ normalizer (Model.row : Set SL) := by
  apply normalizes_closure_of_generators
  rintro g hg _ ⟨j, hj, rfl⟩
  exact row_product_of_firstColumns g g⁻¹ (mul_inv_cancel g)
    (centralizer_firstColumn g hg) (centralizer_firstColumn g⁻¹ (centralizer.inv_mem hg)) j hj


variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

private theorem pullback_centralizer (A : Subgroup SL) (hAC : A ≤ centralizer)
    (hzA : z ∈ F.pullback A)
    (hself : Subgroup.centralizer (A : Set SL) = A) :
    Subgroup.centralizer (F.pullback A : Set G) = F.pullback A := by
  have image_mem (a : A) :
      (F.equiv.symm ⟨a, hAC a.property⟩ : G) ∈ F.pullback A := by
    apply (F.mem_pullback_iff A _).mpr
    simpa only [F.equiv.apply_symm_apply] using a.property
  apply le_antisymm
  · intro x hx
    have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := by
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx z hzA).symm
    apply (F.mem_pullback_iff A ⟨x, hxC⟩).mpr
    rw [← hself]
    apply mem_centralizer_iff.mpr
    intro a ha
    let b := F.equiv.symm ⟨a, hAC ha⟩
    have he : b * ⟨x, hxC⟩ = ⟨x, hxC⟩ * b :=
      Subtype.ext (mem_centralizer_iff.mp hx b (image_mem ⟨a, ha⟩))
    have him := congrArg (fun q => (F.equiv q : SL)) he
    simpa only [map_mul, Subgroup.coe_mul, b, F.equiv.apply_symm_apply] using him
  · intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    let xc : Subgroup.centralizer ({z} : Set G) := ⟨x, F.pullback_le A hx⟩
    let yc : Subgroup.centralizer ({z} : Set G) := ⟨y, F.pullback_le A hy⟩
    have hm : (F.equiv xc : SL) ∈ Subgroup.centralizer (A : Set SL) := by
      rw [hself]
      exact (F.mem_pullback_iff A xc).mp hx
    have he : F.equiv yc * F.equiv xc = F.equiv xc * F.equiv yc :=
      Subtype.ext (mem_centralizer_iff.mp hm _ ((F.mem_pullback_iff A yc).mp hy))
    have hxy : yc * xc = xc * yc := F.equiv.injective (by simpa only [map_mul] using he)
    exact congrArg Subtype.val hxy

/-- The literal marked row subgroup is self-centralizing in the whole group. -/
theorem row_centralizer_eq : Subgroup.centralizer (F.row : Set G) = F.row :=
  pullback_centralizer F Model.row Model.row_le_centralizer (point_mem_row F) centralizer_row_eq

/-- The full original point centralizer normalizes the marked row group. -/
theorem point_centralizer_le_row_normalizer :
    Subgroup.centralizer ({z} : Set G) ≤ normalizer (F.row : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg x hx
  let gc : Subgroup.centralizer ({z} : Set G) := ⟨g, hg⟩
  let xc : Subgroup.centralizer ({z} : Set G) := ⟨x, F.pullback_le _ hx⟩
  apply (F.mem_pullback_iff Model.row (gc * xc * gc⁻¹)).mpr
  have hm := (mem_normalizer_iff.mp
    (centralizer_normalizes_row (F.equiv gc).property) (F.equiv xc)).mp
      ((F.mem_pullback_iff Model.row xc).mp hx)
  simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hm

/-- Normality is relative to the point centralizer, not to the ambient group. -/
theorem row_normal_in_point_centralizer : (F.row.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal :=
  (normal_subgroupOf_iff_le_normalizer (F.pullback_le Model.row)).mpr
    (point_centralizer_le_row_normalizer F)

/-- The literal row normalizer in the source group. -/
abbrev rowNormalizer := normalizer (F.row : Set G)
/-- Quotient by the row group inside its actual normalizer. -/
abbrev rowQuotient := rowNormalizer F ⧸ F.row.subgroupOf (rowNormalizer F)

/-- Conjugation, descended through the proved exact kernel. -/
def rowQuotientAction : rowQuotient F →* MulAut F.row :=
  QuotientGroup.lift _ F.row.normalizerMonoidHom (by
    rw [normalizerMonoidHom_ker, row_centralizer_eq F])

/-- No larger subgroup is killed by the quotient action. -/
theorem rowQuotientAction_injective : Function.Injective (rowQuotientAction F) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [normalizerMonoidHom_ker, row_centralizer_eq F]

/-- The quotient action retains the original ambient conjugation formula. -/
theorem rowQuotientAction_mk_apply (g : rowNormalizer F) (x : F.row) :
    (rowQuotientAction F (QuotientGroup.mk g) x : G) = (g : G) * (x : G) * (g : G)⁻¹ := by
  exact normalizerMonoidHom_apply_apply_coe F.row g x

private def pullbackEquiv (A : Subgroup SL) (hAC : A ≤ centralizer) :
    F.pullback A ≃* A where
  toFun x := ⟨F.equiv ⟨x, F.pullback_le A x.property⟩,
    (F.mem_pullback_iff A ⟨x, F.pullback_le A x.property⟩).mp x.property⟩
  invFun a := ⟨F.equiv.symm ⟨a, hAC a.property⟩,
    (F.mem_pullback_iff A _).mpr (by
      simpa only [F.equiv.apply_symm_apply] using a.property)⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg (fun a : Subgroup.centralizer ({z} : Set G) => (a : G))
      (F.equiv.symm_apply_apply ⟨x, F.pullback_le A x.property⟩)
  right_inv a := by
    apply Subtype.ext
    exact congrArg (fun x : centralizer => (x : SL))
      (F.equiv.apply_symm_apply ⟨a, hAC a.property⟩)
  map_mul' x y := by
    apply Subtype.ext
    exact congrArg (fun a : centralizer => (a : SL))
      (F.equiv.map_mul ⟨x, F.pullback_le A x.property⟩ ⟨y, F.pullback_le A y.property⟩)

/-- Explicit binary four-space coordinates from the same centralizer marking. -/
def rowCoordinates : F.row ≃* Multiplicative (Fin 4 → ZMod 2) :=
  (pullbackEquiv F Model.row Model.row_le_centralizer).trans modelRowCoordinates

/-- The distinguished point keeps its last-coordinate root marking. -/
theorem rowCoordinates_point : rowCoordinates F ⟨z, point_mem_row F⟩ =
    Multiplicative.ofAdd (Pi.single 3 1) := by
  apply Multiplicative.toAdd.injective
  funext i
  change (F.equiv ⟨z, F.pullback_le _ (point_mem_row F)⟩ : SL) 0 i.succ =
    (Pi.single 3 (1 : ZMod 2) : Fin 4 → ZMod 2) i
  rw [F.on_point]
  fin_cases i <;> decide

/-- The original row group has order sixteen. -/
theorem row_card : Nat.card F.row = 16 := by
  rw [Nat.card_congr (rowCoordinates F).toEquiv]
  change Nat.card (Fin 4 → ZMod 2) = 16
  simp

/-- The linear fusion count supplies a conjugate of the point in the row
normalizer but outside its row kernel. -/
theorem linear_fusion_outside_row [Finite G] (hlinear : F.LinearFusion) :
    ∃ a : G, a ∈ F.plane ∧ IsConj z a ∧ a ∈ rowNormalizer F ∧ a ∉ F.row := by
  classical
  have hout : ¬ F.fusion F.plane ⊆ (F.row : Set G) := by
    intro h
    have hc := Set.ncard_le_ncard h
    have hr : (F.row : Set G).ncard = 16 := row_card F
    rw [hlinear.1, hr] at hc
    omega
  obtain ⟨a, ha, hnot⟩ := Set.not_subset.mp hout
  exact ⟨a, ha.1, ha.2,
    point_centralizer_le_row_normalizer F (F.pullback_le Model.plane ha.1), hnot⟩

/-- The point stabilizer in the normalizer action is precisely its original
full centralizer; the quotient map is the literal one. -/
theorem rowQuotientAction_point_fix_iff (g : rowNormalizer F) :
    rowQuotientAction F (QuotientGroup.mk g) ⟨z, point_mem_row F⟩ = ⟨z, point_mem_row F⟩ ↔
      (g : G) ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subtype.ext_iff, mem_centralizer_singleton_iff]
  change (g : G) * z * (g : G)⁻¹ = z ↔ (g : G) * z = z * (g : G)
  exact mul_inv_eq_iff_eq_mul

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
