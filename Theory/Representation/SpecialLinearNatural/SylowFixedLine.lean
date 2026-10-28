module
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases

/-!
# A Sylow subgroup on the natural two-dimensional special linear module

The upper unipotents fix exactly the first coordinate line. For a vector
outside that line, its displacements exhaust the line. Conjugating both
actors and vectors proves the same assertions for every Sylow subgroup in
the defining characteristic, retaining the literal matrix action.

The Chapter 6 source application constructs the order-four subgroup
C_V(T ∩ L) and its commutator identity on the natural SL₂(4) module.
Source: Aschbacher–Smith, combined manuscript, §6.2, printed pp.680–681.
-/

public noncomputable section
namespace Representation.SpecialLinearTwo
open Subgroup Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]

private def upperLine : Submodule F (Fin 2 → F) where
  carrier := {v | v 1 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro a b ha hb
    change a 1 + b 1 = 0
    rw [show a 1 = 0 from ha, show b 1 = 0 from hb, add_zero]
  smul_mem' a v hv := by
    change a * v 1 = 0
    rw [show v 1 = 0 from hv, mul_zero]

private theorem upperLine_card : Nat.card (upperLine (F := F)) = Nat.card F := by
  let e : upperLine (F := F) ≃ F := {
    toFun v := v.val 0
    invFun a := ⟨![a, 0], by rfl⟩
    left_inv v := by
      apply Subtype.ext
      funext i
      fin_cases i
      · rfl
      · exact v.property.symm
    right_inv _ := rfl }
  exact Nat.card_congr e

private theorem upperLine_fixed (v : Fin 2 → F) :
    v ∈ upperLine ↔ ∀ g ∈ upperUnipotent F, toLin' g v = v := by
  constructor
  · intro hv g hg
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent F g).mp hg
    funext i
    fin_cases i <;>
      simp [toLin'_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, transvection_coe,
        show v 1 = 0 from hv]
  · intro hv
    have hh := congrFun (hv (transvection zero_ne_one (1 : F))
      ((mem_upperUnipotent F _).mpr ⟨1, rfl⟩)) 0
    change v 1 = 0
    simpa [toLin'_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, transvection_coe] using hh

private theorem upperLine_displacement (v w : Fin 2 → F)
    (hv : v ∉ upperLine) (hw : w ∈ upperLine) :
    ∃ g ∈ upperUnipotent F, toLin' g v - v = w := by
  have hv1 : v 1 ≠ 0 := hv
  have hw1 : w 1 = 0 := hw
  refine ⟨transvection zero_ne_one (w 0 / v 1),
    (mem_upperUnipotent F _).mpr ⟨_, rfl⟩, ?_⟩
  funext i
  fin_cases i <;>
    simp [toLin'_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, transvection_coe, hv1, hw1]

/-- The fixed field-line and all its displacements for a Sylow subgroup in
the defining characteristic. -/
theorem sylow_fixed_line_displacements [Finite F] (p : ℕ) [Fact p.Prime]
    [CharP F p] (P : Sylow p (Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∃ W : Submodule F (Fin 2 → F), Nat.card W = Nat.card F ∧
      (∀ v, v ∈ W ↔ ∀ g ∈ (P : Subgroup _), toLin' g v = v) ∧
      (∀ g ∈ (P : Subgroup _), ∀ v, toLin' g v - v ∈ W) ∧
      ∀ v, v ∉ W → ∀ w ∈ W,
        ∃ g ∈ (P : Subgroup _), toLin' g v - v = w := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq
    (Matrix.SpecialLinearGroup (Fin 2) F) (upperUnipotentSylow F p) P
  let W := upperLine.map (toLin' a).toLinearMap
  have hW (v : Fin 2 → F) : v ∈ W ↔ toLin' a⁻¹ v ∈ upperLine := by
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hv
      exact ⟨toLin' a⁻¹ v, hv, by simp⟩
  have hP (g : Matrix.SpecialLinearGroup (Fin 2) F) :
      g ∈ (a • upperUnipotentSylow F p : Sylow p _) ↔
        ∃ b ∈ upperUnipotent F, a * b * a⁻¹ = g := by
    change g ∈ ((a • upperUnipotentSylow F p : Sylow p _) : Subgroup _) ↔ _
    rw [Sylow.coe_subgroup_smul]
    rfl
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact (Nat.card_congr (Submodule.equivMapOfInjective
      (toLin' a).toLinearMap (toLin' a).injective upperLine).toEquiv).symm.trans
      upperLine_card
  · intro v
    rw [hW, upperLine_fixed]
    constructor
    · intro hv g hg
      obtain ⟨b, hb, rfl⟩ := (hP g).mp hg
      have hh := congrArg (toLin' a) (hv b hb)
      simpa using hh
    · intro hv b hb
      have hh := congrArg (toLin' a⁻¹)
        (hv (a * b * a⁻¹) ((hP _).mpr ⟨b, hb, rfl⟩))
      simpa using hh
  · intro g hg v
    obtain ⟨b, hb, rfl⟩ := (hP g).mp hg
    apply (hW _).mpr
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent F b).mp hb
    simp only [map_sub, map_mul, LinearEquiv.mul_apply]
    simp only [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    change (toLin' (transvection zero_ne_one t) (toLin' a⁻¹ v) - toLin' a⁻¹ v) 1 = 0
    simp [toLin'_apply, Matrix.mulVec,
      dotProduct, transvection_coe]
  · intro v hv w hw
    obtain ⟨b, hb, he⟩ := upperLine_displacement (toLin' a⁻¹ v) (toLin' a⁻¹ w)
      (fun h => hv ((hW v).mpr h)) ((hW w).mp hw)
    refine ⟨a * b * a⁻¹, (hP _).mpr ⟨b, hb, rfl⟩, ?_⟩
    have hh := congrArg (toLin' a) he
    simpa using hh

end Representation.SpecialLinearTwo
