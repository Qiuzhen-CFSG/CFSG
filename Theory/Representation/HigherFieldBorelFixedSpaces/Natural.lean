module

public import Theory.Representation.HigherFieldBorelFixedSpaces.Tensor
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.SpecificGroups.PSL3.CartanActions

/-!
# Natural Borel fixed spaces over larger binary fields

For SL₂ use diag(a,a⁻¹), with a nonidentity unit. For SL₃ use
 diag(a,(a²)⁻¹,a); in characteristic two none of its diagonal entries is one.
These actual Borel elements annihilate the natural and binary-dual fixed
spaces. The tensor theorem then handles their external natural S₃ tensors.

The SL₂ Borel is its own two-residual, and the concrete Sylow subgroups give
odd index for both ranks. For |F| = 2ⁿ with n odd the scalar kernel of
SL₃(F) → PSL₃(F) is trivial. The projective natural representation is defined
through that actual group equivalence and its matrix action is proved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 13.8.20, printed pp.954–955 (PDF pp.971–972).
-/

@[expose] public section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Representation.HigherFieldBorelFixedSpaces
open Representation.BinaryOffender
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev binaryNatural (d : ℕ) : Representation (ZMod 2) SL(d,F) (Fin d → F) :=
  (specialLinearNatural d).restrictScalars

omit [CharP F 2] [Algebra (ZMod 2) F] in
lemma large_field_unit (hF : 2 < Nat.card F) : ∃ a : Fˣ, (a : F) ≠ 1 := by
  have h : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp h
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  exact ⟨a, fun he => ha (Units.ext he)⟩

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
lemma diagonal_two_fixed_eq_zero (a : Fˣ) (ha : (a : F) ≠ 1)
    (v : Fin 2 → F) (hv : (diag2 (a : F) a.ne_zero).val *ᵥ v = v) : v = 0 := by
  have hi : (a : F)⁻¹ ≠ 1 := by
    intro h
    apply ha
    calc
      (a : F) = (a : F) * (a : F)⁻¹ := by rw [h, mul_one]
      _ = 1 := mul_inv_cancel₀ a.ne_zero
  ext i
  fin_cases i
  · have h := congrFun hv 0
    simp [diag2_coe', mulVec, dotProduct, Fin.sum_univ_two] at h
    exact (mul_eq_zero.mp (show ((a : F) - 1) * v 0 = 0 by linear_combination h)).resolve_left
      (sub_ne_zero.mpr ha)
  · have h := congrFun hv 1
    simp [diag2_coe', mulVec, dotProduct, Fin.sum_univ_two] at h
    exact (mul_eq_zero.mp (show ((a : F)⁻¹ - 1) * v 1 = 0 by linear_combination h)).resolve_left
      (sub_ne_zero.mpr hi)

omit [CharP F 2] in
theorem sl2_borel_fixedSpace (hF : 2 < Nat.card F) :
    fixedSpace (binaryNatural (F := F) 2) (rankOneBorel F) = ⊥ := by
  obtain ⟨a, ha⟩ := large_field_unit hF
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  exact diagonal_two_fixed_eq_zero a ha v
    (hv ⟨diag2 (a : F) a.ne_zero, diag_mem_rankOneBorel (a : F) a.ne_zero⟩)

omit [Algebra (ZMod 2) F] in
theorem sl2_borel_residual (hF : 4 ≤ Nat.card F) :
    pResidual 2 (rankOneBorel F) = ⊤ :=
  (pResidual_eq_top_iff _ _).mpr (rankOneBorel_isPPerfect hF)

omit [Algebra (ZMod 2) F] in
theorem sl2_borel_odd_index : Odd (rankOneBorel F).index := by
  have h := (upperUnipotentSylow F 2).not_dvd_index
  have hd := Subgroup.index_dvd_of_le (upperUnipotent F).le_normalizer
  change (rankOneBorel F).index ∣ (upperUnipotent F).index at hd
  have hu : Odd (upperUnipotent F).index := by
    rw [Nat.odd_iff]
    change ¬ 2 ∣ (upperUnipotent F).index at h
    omega
  exact hu.of_dvd_nat hd

omit [CharP F 2] in
theorem sl2_borel_dual_fixedSpace (hF : 2 < Nat.card F) :
    fixedSpace (binaryNatural (F := F) 2).dual (rankOneBorel F) = ⊥ := by
  obtain ⟨a, ha⟩ := large_field_unit hF
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  exact dual_fixed_eq_zero (binaryNatural 2) (diag2 (a : F) a.ne_zero)
    (diagonal_two_fixed_eq_zero a ha) f
    (hf ⟨diag2 (a : F) a.ne_zero, diag_mem_rankOneBorel (a : F) a.ne_zero⟩)
end Representation.HigherFieldBorelFixedSpaces

open Matrix Matrix.SpecialLinearGroup Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open scoped MatrixGroups
namespace Representation.HigherFieldBorelFixedSpaces
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
lemma diagonal_three_fixed_eq_zero (a : Fˣ) (ha : (a : F) ≠ 1)
    (v : Fin 3 → F) (hv : (torusSL F (a,a)).val *ᵥ v = v) : v = 0 := by
  have hs : (a : F) ^ 2 ≠ 1 := by
    intro h
    apply ha
    exact (frobenius_inj F 2) (by simpa [frobenius_def] using h)
  have hi : (((a * a)⁻¹ : Fˣ) : F) ≠ 1 := by
    intro h
    apply hs
    have hm : (a : F) ^ 2 * (((a * a)⁻¹ : Fˣ) : F) = 1 := by
      rw [pow_two, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel]
      rfl
    rwa [h, mul_one] at hm
  ext i
  fin_cases i
  · have h := congrFun hv 0
    simp [torusSL_val, mulVec, dotProduct, Fin.sum_univ_three] at h
    exact (mul_eq_zero.mp (show ((a : F) - 1) * v 0 = 0 by linear_combination h)).resolve_left
      (sub_ne_zero.mpr ha)
  · have h := congrFun hv 1
    simp only [torusSL_val, mulVec_diagonal, Matrix.cons_val_one,
      Matrix.cons_val_zero] at h
    exact (mul_eq_zero.mp (show ((((a * a)⁻¹ : Fˣ) : F) - 1) * v 1 = 0 by
      linear_combination h)).resolve_left (sub_ne_zero.mpr hi)
  · have h := congrFun hv 2
    simp [torusSL_val, mulVec, dotProduct, Fin.sum_univ_three] at h
    exact (mul_eq_zero.mp (show ((a : F) - 1) * v 2 = 0 by linear_combination h)).resolve_left
      (sub_ne_zero.mpr ha)

variable [Algebra (ZMod 2) F]
open Representation.BinaryOffender

theorem sl3_borel_fixedSpace (hF : 2 < Nat.card F) :
    fixedSpace (binaryNatural (F := F) 3) (borelSL F) = ⊥ := by
  obtain ⟨a, ha⟩ := large_field_unit hF
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hm : torusSL F (a,a) ∈ borelSL F := by
    rw [mem_borelSL_iff, torusSL_val]
    simp
  exact diagonal_three_fixed_eq_zero a ha v (hv ⟨torusSL F (a,a), hm⟩)

theorem sl3_borel_dual_fixedSpace (hF : 2 < Nat.card F) :
    fixedSpace (binaryNatural (F := F) 3).dual (borelSL F) = ⊥ := by
  obtain ⟨a, ha⟩ := large_field_unit hF
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hm : torusSL F (a,a) ∈ borelSL F := by
    rw [mem_borelSL_iff, torusSL_val]
    simp
  exact dual_fixed_eq_zero (binaryNatural 3) (torusSL F (a,a))
    (diagonal_three_fixed_eq_zero a ha) f (hf ⟨torusSL F (a,a), hm⟩)

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem sl3_borel_odd_index {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    Odd (borelSL F).index := by
  have h := odd_index_unipotent F hn hF
  have hd := Subgroup.index_dvd_of_le (unipotent_le_borel F)
  have hb : Odd (borel F).index := by
    rw [Nat.odd_iff]
    have hh : ¬ 2 ∣ (borel F).index := fun he => h (he.trans hd)
    omega
  rwa [← borel_comap F, (borel F).index_comap_of_surjective
    (Matrix.PSL3.projection_surjective F)]

end Representation.HigherFieldBorelFixedSpaces

open Matrix Matrix.SpecialLinearGroup Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace Representation.HigherFieldBorelFixedSpaces
open Representation.BinaryOffender
variable {F : Type*} [Field F] [Finite F]

theorem sl3_projection_injective_odd {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2^n) :
    Function.Injective (projection F) := by
  have hmod : Nat.card F % 3 = 2 := by
    obtain ⟨m, rfl⟩ := hn
    rw [hF, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply Subgroup.eq_bot_of_card_eq
  rw [Nat.card_congr (projectionKernelEquivOne F (by omega)).toEquiv]
  exact Nat.card_zmod 1

noncomputable def sl3ProjectiveEquiv {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2^n) :
    SL(3,F) ≃* PSL(3,F) :=
  MulEquiv.ofBijective (projection F)
    ⟨sl3_projection_injective_odd hn hF, projection_surjective F⟩

variable [CharP F 2] [Algebra (ZMod 2) F]

noncomputable def projectiveBinaryNatural {n : ℕ} (hn : Odd n)
    (hF : Nat.card F = 2^n) : Representation (ZMod 2) PSL(3,F) (Fin 3 → F) :=
  (binaryNatural 3).comp (sl3ProjectiveEquiv hn hF).symm.toMonoidHom

omit [CharP F 2] in
lemma projectiveBinaryNatural_projection {n : ℕ} (hn : Odd n)
    (hF : Nat.card F = 2^n) (g : SL(3,F)) (v : Fin 3 → F) :
    projectiveBinaryNatural hn hF (projection F g) v = g.val *ᵥ v := by
  change binaryNatural 3 ((sl3ProjectiveEquiv hn hF).symm (sl3ProjectiveEquiv hn hF g)) v = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem psl3_borel_fixedSpace {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2^n)
    (hlarge : 2 < Nat.card F) :
    fixedSpace (projectiveBinaryNatural hn hF) (borel F) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hm : v ∈ fixedSpace (binaryNatural (F := F) 3) (borelSL F) := by
    intro b
    have h := hv ⟨projection F b, Subgroup.mem_map_of_mem _ b.property⟩
    change projectiveBinaryNatural hn hF (projection F b) v = v at h
    rw [projectiveBinaryNatural_projection] at h
    exact h
  rwa [sl3_borel_fixedSpace hlarge, Submodule.mem_bot] at hm

theorem psl3_borel_dual_fixedSpace {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2^n)
    (hlarge : 2 < Nat.card F) :
    fixedSpace (projectiveBinaryNatural hn hF).dual (borel F) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hm : f ∈ fixedSpace (binaryNatural (F := F) 3).dual (borelSL F) := by
    intro b
    have h := hf ⟨projection F b, Subgroup.mem_map_of_mem _ b.property⟩
    apply LinearMap.ext
    intro v
    have he := congrArg (fun t : Module.Dual (ZMod 2) (Fin 3 → F) => t v) h
    change f (projectiveBinaryNatural hn hF (projection F b)⁻¹ v) = f v at he
    rw [← map_inv, projectiveBinaryNatural_projection] at he
    exact he
  rwa [sl3_borel_dual_fixedSpace hlarge, Submodule.mem_bot] at hm
end Representation.HigherFieldBorelFixedSpaces

namespace Representation.HigherFieldBorelFixedSpaces
open Matrix Matrix.SpecialLinearGroup Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Representation.BinaryOffender
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The F-linear dual natural module, restricted to the prime field. -/
abbrev binaryFieldDual (d : ℕ) :
    Representation (ZMod 2) SL(d,F) (Module.Dual F (Fin d → F)) :=
  (specialLinearNatural d).dual.restrictScalars

omit [CharP F 2] in
theorem sl2_borel_fieldDual_fixedSpace (hF : 2 < Nat.card F) :
    fixedSpace (binaryFieldDual (F := F) 2) (rankOneBorel F) = ⊥ := by
  obtain ⟨a, ha⟩ := large_field_unit hF
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  exact dual_fixed_eq_zero (specialLinearNatural (k := F) 2) (diag2 (a : F) a.ne_zero)
    (diagonal_two_fixed_eq_zero a ha) f
    (hf ⟨diag2 (a : F) a.ne_zero, diag_mem_rankOneBorel (a : F) a.ne_zero⟩)

theorem sl3_borel_fieldDual_fixedSpace (hF : 2 < Nat.card F) :
    fixedSpace (binaryFieldDual (F := F) 3) (borelSL F) = ⊥ := by
  obtain ⟨a, ha⟩ := large_field_unit hF
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hm : torusSL F (a,a) ∈ borelSL F := by
    rw [mem_borelSL_iff, torusSL_val]
    simp
  exact dual_fixed_eq_zero (specialLinearNatural (k := F) 3) (torusSL F (a,a))
    (diagonal_three_fixed_eq_zero a ha) f (hf ⟨torusSL F (a,a), hm⟩)

/-- The genuine projective F-dual action, using the odd-degree projection equivalence. -/
noncomputable def projectiveBinaryFieldDual {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2^n) :
    Representation (ZMod 2) PSL(3,F) (Module.Dual F (Fin 3 → F)) :=
  (binaryFieldDual 3).comp (sl3ProjectiveEquiv hn hF).symm.toMonoidHom

omit [CharP F 2] in
lemma projectiveBinaryFieldDual_projection {n : ℕ} (hn : Odd n)
    (hF : Nat.card F = 2^n) (g : SL(3,F)) (f : Module.Dual F (Fin 3 → F)) :
    projectiveBinaryFieldDual hn hF (Matrix.PSL3.projection F g) f =
      binaryFieldDual 3 g f := by
  change binaryFieldDual 3 ((sl3ProjectiveEquiv hn hF).symm
    (sl3ProjectiveEquiv hn hF g)) f = _
  rw [MulEquiv.symm_apply_apply]

theorem psl3_borel_fieldDual_fixedSpace {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2^n)
    (hlarge : 2 < Nat.card F) :
    fixedSpace (projectiveBinaryFieldDual hn hF) (borel F) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hm : f ∈ fixedSpace (binaryFieldDual (F := F) 3) (borelSL F) := by
    intro b
    have h := hf ⟨Matrix.PSL3.projection F b, Subgroup.mem_map_of_mem _ b.property⟩
    change projectiveBinaryFieldDual hn hF (Matrix.PSL3.projection F b) f = f at h
    rwa [projectiveBinaryFieldDual_projection] at h
  rwa [sl3_borel_fieldDual_fixedSpace hlarge, Submodule.mem_bot] at hm
end Representation.HigherFieldBorelFixedSpaces
