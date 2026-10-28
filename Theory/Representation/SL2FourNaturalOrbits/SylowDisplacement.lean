module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.SpecificGroups.SL2.UpperUnipotent
import Mathlib.Tactic.FinCases

/-!
# Displacements of a Sylow two-subgroup on the natural SL₂(4) module

An upper unipotent sends (x,y) to (x+ay,y). For y nonzero, its
displacements exhaust the fixed field-line. Sylow conjugacy transports
this calculation with the same matrix acting on both vectors and actors.

Source application: Aschbacher–Smith, J.2.3 assertion (!),
printed p.433 (PDF p.444), on the literal Ru2 module U/Z.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourNatural
open Subgroup Matrix.SpecialLinearGroup

private lemma upper_eq_transvection (a : F) : upper a = transvection zero_ne_one a := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [upper, transvection_coe]

private lemma mem_upper (g : SL) : g ∈ upperUnipotent F ↔ ∃ a : F, upper a = g := by
  simp only [mem_upperUnipotent, upper_eq_transvection]

private lemma fixed_upper (v : V) :
    (∀ g ∈ upperUnipotent F, action g v = v) ↔ v ∈ upperFixed := by
  rw [mem_upperFixed, ← upper_fixed_iff]
  constructor
  · intro h a
    exact h (upper a) ((mem_upper _).mpr ⟨a, rfl⟩)
  · rintro h g hg
    obtain ⟨a, rfl⟩ := (mem_upper g).mp hg
    exact h a

private lemma upper_displacement (v : V) (hv : v ∉ upperFixed) (w : V)
    (hw : w ∈ upperFixed) : ∃ a : F, action (upper a) v - v = w := by
  have hv1 : v 1 ≠ 0 := fun h => hv ((mem_upperFixed v).mpr h)
  have hw1 := (mem_upperFixed w).mp hw
  refine ⟨w 0 / v 1, ?_⟩
  rw [upper_action]
  funext i
  fin_cases i <;> simp [hw1, hv1]

/-- The actual fixed plane and all displacements, for an arbitrary Sylow.
The same conjugating matrix transports both the subgroup and its fixed line. -/
theorem sylow_fixed_plane_displacements (P : Sylow 2 SL) :
    ∃ W : Submodule (ZMod 2) V, Nat.card W = 4 ∧
      (∀ v, v ∈ W ↔ ∀ g ∈ (P : Subgroup SL), action g v = v) ∧
      ∀ v, v ∉ W → ∀ w ∈ W,
        ∃ g ∈ (P : Subgroup SL), action g v - v = w := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq SL (upperUnipotentSylow F 2) P
  let W := upperFixed.map (action a).toLinearMap
  have hW (v : V) : v ∈ W ↔ action a⁻¹ v ∈ upperFixed := by
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hv
      exact ⟨action a⁻¹ v, hv, by simp⟩
  have hP (g : SL) : g ∈ (a • upperUnipotentSylow F 2 : Sylow 2 SL) ↔
      ∃ b ∈ upperUnipotent F, a * b * a⁻¹ = g := by
    change g ∈ ((a • upperUnipotentSylow F 2 : Sylow 2 SL) : Subgroup SL) ↔ _
    rw [Sylow.coe_subgroup_smul]
    rfl
  have inv_action (b : SL) (v : V) : action b⁻¹ (action b v) = v := by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have action_inv (b : SL) (v : V) : action b (action b⁻¹ v) = v := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  refine ⟨W, ?_, ?_, ?_⟩
  · exact (Nat.card_congr (Submodule.equivMapOfInjective
      (action a).toLinearMap (action a).injective upperFixed).toEquiv).symm.trans card_upperFixed
  · intro v
    rw [hW, ← fixed_upper]
    constructor
    · intro hv g hg
      obtain ⟨b, hb, rfl⟩ := (hP g).mp hg
      have hh := congrArg (action a) (hv b hb)
      simpa only [map_mul, LinearEquiv.mul_apply, action_inv] using hh
    · intro hv b hb
      have hh := congrArg (action a⁻¹) (hv (a * b * a⁻¹)
        ((hP _).mpr ⟨b, hb, rfl⟩))
      simpa only [map_mul, LinearEquiv.mul_apply, inv_action] using hh
  · intro v hv w hw
    obtain ⟨b, hb⟩ := upper_displacement (action a⁻¹ v)
      (fun h => hv ((hW v).mpr h)) (action a⁻¹ w) ((hW w).mp hw)
    refine ⟨a * upper b * a⁻¹,
      (hP _).mpr ⟨upper b, (mem_upper _).mpr ⟨b, rfl⟩, rfl⟩, ?_⟩
    have hh := congrArg (action a) hb
    simpa only [map_sub, map_mul, LinearEquiv.mul_apply, action_inv] using hh

end Representation.SL2FourNatural
