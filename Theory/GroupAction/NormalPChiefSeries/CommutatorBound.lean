module
public import Theory.GroupAction.NormalPChiefSeries.MovedIntersections

/-!
# Two moved chief factors bound the actual commutator

Representatives of the moved spaces of two distinct chief intervals lie
in [K,U]. Intersecting the original filtration with that commutator and
multiplying its two section indices gives the product bound. The actor K
need not be normal, and no normalization of K by U is required.

Source application: both natural chief factors in Aschbacher--Smith
15.2.4 and 15.2.8, printed pp.1105--1110.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace NoncentralChiefRefinement.SeriesOn
variable {D : Type*} [Group D] [Finite D] {U : Subgroup D} [U.Normal]
  [IsElementaryAbelian 2 U]

/-- Every moved vector has a representative in the actual commutator. -/
theorem moved_card_le_commutator_section (s : SeriesOn U)
    (K : Subgroup D) (i : Fin s.series.length) :
    Nat.card (subspaceCommutator ((s.factorRepresentation i).comp K.subtype) ⊤ ⊤) ≤
      Nat.card (Section (restrictNormalNode ⁅K,U⁆ (s.lower i)) (restrictNormalNode ⁅K,U⁆ (s.upper i))) := by
  let r := restrictionSectionMap ⁅K,U⁆ (s.lower i) (s.upper i)
  let E : Submodule (ZMod 2) (Additive (s.Factor i)) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup r.range)
  have hm : subspaceCommutator ((s.factorRepresentation i).comp K.subtype) ⊤ ⊤ ≤ E := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,_,v,_,rfl⟩
    obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective
      ((s.lower i).val.subgroupOf (s.upper i).val) v.toMul
    have hk : ⁅(k : D),(b : D)⁆ ∈ ⁅K,U⁆ :=
      commutator_mem_commutator k.property (s.upper_le i b.property)
    have hB : ⁅(k : D),(b : D)⁆ ∈ (s.upper i).val :=
      (commutator_le_right (⊤ : Subgroup D) (s.upper i).val)
        (commutator_mem_commutator (mem_top _) b.property)
    change (s.action i (k : D) v.toMul) / v.toMul ∈ r.range
    refine ⟨QuotientGroup.mk' _ (⟨⟨⁅(k : D),(b : D)⁆,hk⟩,hB⟩ :
      (restrictNormalNode ⁅K,U⁆ (s.upper i)).val),?_⟩
    rw [←hb,s.action_mk]
    change restrictionSectionMap ⁅K,U⁆ (s.lower i) (s.upper i) _ = _
    rw [restrictionSectionMap_mk,←map_div]
    apply congrArg (QuotientGroup.mk' _)
    apply Subtype.ext
    simp only [commutatorElement_def,div_eq_mul_inv]
    rfl
  have hc := Nat.card_le_card_of_injective _ (Submodule.inclusion_injective hm)
  have he : Nat.card E = Nat.card r.range := rfl
  rw [he,←Nat.card_congr (MonoidHom.ofInjective (restrictionSectionMap_injective ⁅K,U⁆ _ _)).toEquiv] at hc
  exact hc

/-- Two distinct moved intervals contribute multiplicatively to [K,U]. -/
theorem two_moved_cards_le_commutator (s : SeriesOn U)
    (K : Subgroup D)
    (i j : Fin s.series.length) (hij : i ≠ j) :
    Nat.card (subspaceCommutator ((s.factorRepresentation i).comp K.subtype) ⊤ ⊤) *
      Nat.card (subspaceCommutator ((s.factorRepresentation j).comp K.subtype) ⊤ ⊤) ≤
      Nat.card (⁅K,U⁆ : Subgroup D) := by
  have bound (a b : Fin s.series.length) (hab : a < b) :
      Nat.card (subspaceCommutator ((s.factorRepresentation a).comp K.subtype) ⊤ ⊤) *
        Nat.card (subspaceCommutator ((s.factorRepresentation b).comp K.subtype) ⊤ ⊤) ≤
        Nat.card (⁅K,U⁆ : Subgroup D) := by
    let A := restrictNormalNode ⁅K,U⁆ (s.lower a)
    let B := restrictNormalNode ⁅K,U⁆ (s.upper a)
    let C := restrictNormalNode ⁅K,U⁆ (s.lower b)
    let E := restrictNormalNode ⁅K,U⁆ (s.upper b)
    have hAB : A ≤ B := restrictNormalNode_monotone ⁅K,U⁆ (s.series.step a).le
    have hCE : C ≤ E := restrictNormalNode_monotone ⁅K,U⁆ (s.series.step b).le
    have hBC : B ≤ C := (restrictNormalNode_monotone ⁅K,U⁆)
      (s.series.strictMono.monotone (show a.succ ≤ b.castSucc from by
        apply Fin.le_iff_val_le_val.mpr
        exact hab))

    have ha : Nat.card (subspaceCommutator ((s.factorRepresentation a).comp K.subtype) ⊤ ⊤) ≤
        Nat.card C.val := (s.moved_card_le_commutator_section K a).trans
      (((Nat.le_mul_of_pos_right _ (Nat.card_pos (α := A.val))).trans_eq
        (section_card_mul A B hAB)).trans (card_le_of_le hBC))
    calc
      _ ≤ Nat.card C.val * Nat.card (Section C E) := Nat.mul_le_mul ha
        (s.moved_card_le_commutator_section K b)
      _ = Nat.card E.val := (Nat.mul_comm _ _).trans (section_card_mul C E hCE)
      _ ≤ _ := Nat.card_le_card_of_injective E.val.subtype E.val.subtype_injective
  rcases lt_or_gt_of_ne hij with hl | hl
  · exact bound i j hl
  · rw [Nat.mul_comm]
    exact bound j i hl

end NoncentralChiefRefinement.SeriesOn
