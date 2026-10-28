module
public import Theory.GroupAction.NormalPChiefSeries.Linear
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Sections
public import Theory.GroupTheory.NoncentralChiefRefinement.OrderBound
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Two moved chief sections inside a literal subgroup intersection

If the normal elementary group U normalizes K, every commutator on an
original chief section of U has a representative in K. Its moved space
therefore embeds in the section obtained by intersecting with K. Two
ordered intervals contribute multiplicatively to |U ∩ K|; they need not
remain chief after intersection.

This keeps the actual inclusion-induced relative quotient maps. The
application is to both paired chief factors and an actual C-component
in Aschbacher--Smith 15.2.4, printed pp.1105--1107.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace NoncentralChiefRefinement.SeriesOn
variable {D : Type*} [Group D] [Finite D] {U : Subgroup D} [U.Normal]
  [IsElementaryAbelian 2 U]

/-- The moved part of a chief section is represented inside the literal intersection. -/
theorem moved_card_le_intersection_section (s : SeriesOn U)
    (K : Subgroup D) (hKU : U ≤ normalizer (K : Set D)) (i : Fin s.series.length) :
    Nat.card (subspaceCommutator ((s.factorRepresentation i).comp K.subtype) ⊤ ⊤) ≤
      Nat.card (Section (restrictNormalNode K (s.lower i)) (restrictNormalNode K (s.upper i))) := by
  let r := restrictionSectionMap K (s.lower i) (s.upper i)
  let E : Submodule (ZMod 2) (Additive (s.Factor i)) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup r.range)
  have hm : subspaceCommutator ((s.factorRepresentation i).comp K.subtype) ⊤ ⊤ ≤ E := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,_,v,_,rfl⟩
    obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective
      ((s.lower i).val.subgroupOf (s.upper i).val) v.toMul
    have hk : ⁅(k : D),(b : D)⁆ ∈ K :=
      (le_normalizer_iff_commutator_le_left.mp hKU)
        (commutator_mem_commutator k.property (s.upper_le i b.property))
    have hB : ⁅(k : D),(b : D)⁆ ∈ (s.upper i).val :=
      (commutator_le_right (⊤ : Subgroup D) (s.upper i).val)
        (commutator_mem_commutator (mem_top _) b.property)
    change (s.action i (k : D) v.toMul) / v.toMul ∈ r.range
    refine ⟨QuotientGroup.mk' _ (⟨⟨⁅(k : D),(b : D)⁆,hk⟩,hB⟩ :
      (restrictNormalNode K (s.upper i)).val),?_⟩
    rw [←hb,s.action_mk]
    change restrictionSectionMap K (s.lower i) (s.upper i) _ = _
    rw [restrictionSectionMap_mk,←map_div]
    apply congrArg (QuotientGroup.mk' _)
    apply Subtype.ext
    simp only [commutatorElement_def,div_eq_mul_inv]
    rfl
  have hc := Nat.card_le_card_of_injective _ (Submodule.inclusion_injective hm)
  have he : Nat.card E = Nat.card r.range := rfl
  rw [he,←Nat.card_congr (MonoidHom.ofInjective (restrictionSectionMap_injective K _ _)).toEquiv] at hc
  exact hc

/-- Distinct moved chief intervals contribute independently inside the same
literal intersection, even when the intersected intervals are not chief. -/
theorem two_moved_cards_le_intersection (s : SeriesOn U)
    (K : Subgroup D) (hKU : U ≤ normalizer (K : Set D))
    (i j : Fin s.series.length) (hij : i ≠ j) :
    Nat.card (subspaceCommutator ((s.factorRepresentation i).comp K.subtype) ⊤ ⊤) *
      Nat.card (subspaceCommutator ((s.factorRepresentation j).comp K.subtype) ⊤ ⊤) ≤
      Nat.card (U.subgroupOf K) := by
  have bound (a b : Fin s.series.length) (hab : a < b) :
      Nat.card (subspaceCommutator ((s.factorRepresentation a).comp K.subtype) ⊤ ⊤) *
        Nat.card (subspaceCommutator ((s.factorRepresentation b).comp K.subtype) ⊤ ⊤) ≤
        Nat.card (U.subgroupOf K) := by
    let A := restrictNormalNode K (s.lower a)
    let B := restrictNormalNode K (s.upper a)
    let C := restrictNormalNode K (s.lower b)
    let E := restrictNormalNode K (s.upper b)
    have hAB : A ≤ B := restrictNormalNode_monotone K (s.series.step a).le
    have hCE : C ≤ E := restrictNormalNode_monotone K (s.series.step b).le
    have hBC : B ≤ C := (restrictNormalNode_monotone K)
      (s.series.strictMono.monotone (show a.succ ≤ b.castSucc from by
        apply Fin.le_iff_val_le_val.mpr
        exact hab))
    have hE : E.val ≤ U.subgroupOf K := subgroupOf_mono K (s.upper_le b)
    have ha : Nat.card (subspaceCommutator ((s.factorRepresentation a).comp K.subtype) ⊤ ⊤) ≤
        Nat.card C.val := (s.moved_card_le_intersection_section K hKU a).trans
      (((Nat.le_mul_of_pos_right _ (Nat.card_pos (α := A.val))).trans_eq
        (section_card_mul A B hAB)).trans (card_le_of_le hBC))
    calc
      _ ≤ Nat.card C.val * Nat.card (Section C E) := Nat.mul_le_mul ha
        (s.moved_card_le_intersection_section K hKU b)
      _ = Nat.card E.val := (Nat.mul_comm _ _).trans (section_card_mul C E hCE)
      _ ≤ _ := card_le_of_le hE
  rcases lt_or_gt_of_ne hij with hl | hl
  · exact bound i j hl
  · rw [Nat.mul_comm]
    exact bound j i hl

end NoncentralChiefRefinement.SeriesOn
