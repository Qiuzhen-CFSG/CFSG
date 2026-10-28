module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.DihedralData
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.Edge
import Mathlib.Tactic.FinCases

/-!
# The concrete dihedral marking and its centralizer

The two fixed ATLAS words give an injective homomorphism from
`DihedralGroup 5`; restriction to letters 0 and 1 proves injectivity.
Its range is the literal subgroup B. Four checked commutation identities
place B in the pointwise fixer of the marked edge and place the embedded
A₄ in its full centralizer K. Hence the checked reversal belongs to K.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267.
This module proves neither K ≃ A₅ nor the generation identities; those
require further calculations in these same literal subgroups.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry
open Subgroup Theory.GroupTheory GeneratorPair DihedralData

private theorem inclusion_word (w : List (Fin 3)) :
    inclusion (evalWord ![a, b, b⁻¹] w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [evalWord, map_mul, ih, evalWord]
    congr 1
    fin_cases i
    · exact generatorA_eq_table
    · exact generatorB_eq_table
    · exact (map_inv inclusion b).trans (congrArg Inv.inv
        (show inclusion b = tableB from generatorB_eq_table))

private theorem inclusion_rotation : inclusion rotation = rotationTable := by
  exact (inclusion_word rotationWord).trans
    (by decide +kernel : evalWord ![tableA, tableB, tableB⁻¹] rotationWord = rotationTable)

private theorem inclusion_reflection : inclusion reflection = reflectionTable := by
  exact (inclusion_word reflectionWord).trans
    (by decide +kernel : evalWord ![tableA, tableB, tableB⁻¹] reflectionWord = reflectionTable)

private def dihedralElement : DihedralGroup 5 → Carrier
  | .r i => rotation ^ i.val
  | .sr i => reflection * rotation ^ i.val

private theorem dihedralElement_inclusion (d : DihedralGroup 5) :
    inclusion (dihedralElement d) = permutation d := by
  cases d <;> simp only [dihedralElement, permutation, map_pow, map_mul,
    inclusion_rotation, inclusion_reflection]

private theorem multiplication_checked : ∀ d e : DihedralGroup 5,
    permutation (d * e) = permutation d * permutation e := by decide +kernel

/-- A marked embedding of the actual dihedral group of order ten. -/
def dihedralHom : DihedralGroup 5 →* Carrier where
  toFun := dihedralElement
  map_one' := by apply inclusion_injective; rfl
  map_mul' d e := by
    apply inclusion_injective
    rw [map_mul, dihedralElement_inclusion, dihedralElement_inclusion, dihedralElement_inclusion]
    exact multiplication_checked d e

theorem dihedralHom_injective : Function.Injective dihedralHom := by
  have hi : Function.Injective (fun d : DihedralGroup 5 =>
      (permutation d 0, permutation d 1)) := by decide +kernel
  intro d e h
  apply hi
  have he := congrArg inclusion h
  change inclusion (dihedralElement d) = inclusion (dihedralElement e) at he
  rw [dihedralElement_inclusion, dihedralElement_inclusion] at he
  exact congrArg (fun p : Equiv.Perm (Fin 100) => (p 0, p 1)) he

theorem dihedralHom_rotation : dihedralHom (.r 1) = rotation := by
  calc
    dihedralHom (.r 1) = rotation ^ (1 : ZMod 5).val := rfl
    _ = rotation := by rw [show (1 : ZMod 5).val = 1 from rfl, pow_one]

theorem dihedralHom_reflection : dihedralHom (.sr 0) = reflection := by
  calc
    dihedralHom (.sr 0) = reflection * rotation ^ (0 : ZMod 5).val := rfl
    _ = reflection := by rw [ZMod.val_zero, pow_zero, mul_one]

theorem dihedralHom_range : dihedralHom.range = B := by
  apply le_antisymm
  · rintro _ ⟨d, rfl⟩
    have hr : rotation ∈ B := mem_sup_left (mem_zpowers rotation)
    have hs : reflection ∈ B := mem_sup_right (mem_zpowers reflection)
    cases d with
    | r i => exact B.pow_mem hr i.val
    | sr i => exact B.mul_mem hs (B.pow_mem hr i.val)
  · apply sup_le
    · exact zpowers_le.mpr ⟨.r 1, dihedralHom_rotation⟩
    · exact zpowers_le.mpr ⟨.sr 0, dihedralHom_reflection⟩

noncomputable def dihedralEquiv : B ≃* DihedralGroup 5 :=
  ((MonoidHom.ofInjective dihedralHom_injective).trans
    (MulEquiv.subgroupCongr dihedralHom_range)).symm

theorem card_B : Nat.card B = 10 := by
  rw [Nat.card_congr dihedralEquiv.toEquiv, DihedralGroup.nat_card]

private def xPerm : Equiv.Perm (Fin 100) := (tableA * tableB * tableA * tableB⁻¹) ^ 4
private def yPerm : Equiv.Perm (Fin 100) :=
  (tableB⁻¹ * tableA * tableB) * xPerm * (tableB⁻¹ * tableA * tableB)⁻¹

private theorem inclusion_x : inclusion x = xPerm := by
  simp only [x, xPerm, map_pow, map_mul, map_inv,
    (show inclusion a = tableA from generatorA_eq_table),
    (show inclusion b = tableB from generatorB_eq_table)]

private theorem inclusion_y : inclusion y = yPerm := by
  change inclusion (conjugator * x * conjugator⁻¹) = _
  simp only [conjugator, yPerm, map_mul, map_inv, inclusion_x,
    (show inclusion a = tableA from generatorA_eq_table),
    (show inclusion b = tableB from generatorB_eq_table)]

private theorem rotations_commute :
    Commute rotation x ∧ Commute rotation y ∧ Commute reflection x ∧ Commute reflection y := by
  have h : rotationTable * xPerm = xPerm * rotationTable ∧
      rotationTable * yPerm = yPerm * rotationTable ∧
      reflectionTable * xPerm = xPerm * reflectionTable ∧
      reflectionTable * yPerm = yPerm * reflectionTable := by decide +kernel
  have go (u v : Carrier) (huv : inclusion u * inclusion v = inclusion v * inclusion u) :
      Commute u v := by
    apply inclusion_injective
    simpa only [map_mul] using huv
  exact ⟨go _ _ (by simpa only [inclusion_rotation, inclusion_x] using h.1),
    go _ _ (by simpa only [inclusion_rotation, inclusion_y] using h.2.1),
    go _ _ (by simpa only [inclusion_reflection, inclusion_x] using h.2.2.1),
    go _ _ (by simpa only [inclusion_reflection, inclusion_y] using h.2.2.2)⟩

/-- Both endpoints centralize the fixed dihedral subgroup. -/
theorem X_sup_Y_le_K : X ⊔ Y ≤ K := by
  apply sup_le <;> apply zpowers_le.mpr
  · apply mem_centralizer_iff.mpr
    intro d hd
    have hb : B ≤ centralizer ({x} : Set Carrier) := by
      apply sup_le <;> apply zpowers_le.mpr
      · exact (mem_centralizer_singleton_iff (g := x) (k := rotation)).mpr rotations_commute.1.eq
      · exact (mem_centralizer_singleton_iff (g := x) (k := reflection)).mpr rotations_commute.2.2.1.eq
    exact mem_centralizer_singleton_iff.mp (hb hd)
  · apply mem_centralizer_iff.mpr
    intro d hd
    have hb : B ≤ centralizer ({y} : Set Carrier) := by
      apply sup_le <;> apply zpowers_le.mpr
      · exact (mem_centralizer_singleton_iff (g := y) (k := rotation)).mpr rotations_commute.2.1.eq
      · exact (mem_centralizer_singleton_iff (g := y) (k := reflection)).mpr rotations_commute.2.2.2.eq
    exact mem_centralizer_singleton_iff.mp (hb hd)

/-- The dihedral group lies in the actual pointwise edge fixer. -/
theorem B_le_E : B ≤ E := by
  have h := le_centralizer_iff.mp X_sup_Y_le_K
  apply le_inf
  · exact h.trans ((centralizer_le (show (X : Set Carrier) ⊆ (X ⊔ Y : Subgroup Carrier) from
      fun _ hx => mem_sup_left hx)).trans (centralizer_le_normalizer _))
  · exact h.trans ((centralizer_le (show (Y : Set Carrier) ⊆ (X ⊔ Y : Subgroup Carrier) from
      fun _ hy => mem_sup_right hy)).trans (centralizer_le_normalizer _))

theorem t_mem_K : t ∈ K := by
  have hx : x ∈ K := X_sup_Y_le_K (mem_sup_left (mem_zpowers x))
  have hy : y ∈ K := X_sup_Y_le_K (mem_sup_right (mem_zpowers y))
  exact K.mul_mem (K.mul_mem hx (K.mul_mem hx (K.inv_mem hy))) (K.inv_mem hx)

end Sporadic.LeechRelated.J2.RecognitionGeometry
