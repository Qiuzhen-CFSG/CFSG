module

public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Card

/-!
# Rank of a faithful group of common-center binary transvections

If an elementary abelian group acts faithfully with all displacements in one
fixed line, scalar displacement embeds it in the dual of the module. The
common fixed space is the annihilator of the image of this embedding.
Rank-nullity and dual annihilator dimension therefore identify fixed
codimension with binary group rank for every subgroup, including the trivial one.

This is the linear-algebra step used in Aschbacher–Smith, combined manuscript
(1 March 2004), proof of 15.3.67, printed p.1153, PDF p.1170.
-/

@[expose] public section

open Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryOffender.CommonCenter
variable {A V : Type*} [Group A]
    [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) A V) (Z : Submodule (ZMod 2) V)
    (e : Z ≃ₗ[ZMod 2] ZMod 2)
    (hd : ∀ a v, ρ a v - v ∈ Z) (hz : ∀ a z, z ∈ Z → ρ a z = z)

/-- The scalar displacement along the common center. -/
noncomputable def displacement (a : A) : Module.Dual (ZMod 2) V :=
  e.toLinearMap.comp ((ρ a - LinearMap.id).codRestrict Z (hd a))

theorem displacement_eq_zero_iff (a : A) (v : V) :
    displacement ρ Z e hd a v = 0 ↔ ρ a v = v := by
  change e ⟨ρ a v - v, hd a v⟩ = 0 ↔ _
  rw [e.map_eq_zero_iff]
  exact (Subtype.ext_iff).trans sub_eq_zero

include hz in
/-- Fixing the center makes scalar displacement additive in the actor. -/
theorem displacement_mul (a b : A) :
    displacement ρ Z e hd (a * b) = displacement ρ Z e hd a + displacement ρ Z e hd b := by
  apply LinearMap.ext
  intro v
  change e ⟨ρ (a*b) v-v, hd (a*b) v⟩ = e ⟨ρ a v-v, hd a v⟩ + e ⟨ρ b v-v, hd b v⟩
  rw [← map_add]
  apply e.congr_arg
  apply Subtype.ext
  change ρ (a*b) v-v = (ρ a v-v)+(ρ b v-v)
  have h := hz a (ρ b v-v) (hd b v)
  rw [map_sub] at h
  rw [map_mul, Module.End.mul_apply]
  calc
    ρ a (ρ b v) - v = (ρ a (ρ b v) - ρ a v) + (ρ a v - v) := by abel
    _ = (ρ b v - v) + (ρ a v - v) := by rw [h]
    _ = _ := add_comm _ _

variable [IsElementaryAbelian 2 A]

/-- Displacement as a binary linear map on the elementary actor. -/
noncomputable def displacementMap : Additive A →ₗ[ZMod 2] Module.Dual (ZMod 2) V :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun := fun a => displacement ρ Z e hd a.toMul
    map_zero' := by
      ext v
      exact (displacement_eq_zero_iff ρ Z e hd 1 v).mpr (by simp)
    map_add' := fun a b => displacement_mul ρ Z e hd hz a.toMul b.toMul }

/-- Faithfulness makes the displacement map injective. -/
theorem displacementMap_injective (hf : Function.Injective ρ) :
    Function.Injective (displacementMap ρ Z e hd hz) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro a ha
  apply Additive.toMul.injective
  apply hf
  apply LinearMap.ext
  intro v
  have he := congrArg (fun l : Module.Dual (ZMod 2) V => l v) ha
  have hfix := (displacement_eq_zero_iff ρ Z e hd a.toMul v).mp he
  change ρ a.toMul v = ρ 1 v
  simpa only [map_one, Module.End.one_apply] using hfix

/-- The common fixed space is the annihilator of the displacement forms. -/
theorem fixedSpace_eq_annihilator :
    fixedSpace ρ ⊤ = (LinearMap.range (displacementMap ρ Z e hd hz)).dualCoannihilator := by
  ext v
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro hv l hl
    obtain ⟨a, rfl⟩ := hl
    exact (displacement_eq_zero_iff ρ Z e hd a.toMul v).mpr (hv ⟨a.toMul, Subgroup.mem_top _⟩)
  · intro hv a
    exact (displacement_eq_zero_iff ρ Z e hd a.val v).mp
      (hv _ ⟨Additive.ofMul a.val, rfl⟩)

include e hd hz in
/-- Common-center displacement duality identifies codimension with binary actor rank. -/
theorem fixedCodim_top [Finite A] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) : fixedCodim ρ ⊤ = Nat.log 2 (Nat.card A) := by
  have hn := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (LinearMap.range (displacementMap ρ Z e hd hz))
  rw [LinearMap.finrank_range_of_inj (displacementMap_injective ρ Z e hd hz hf),
    ← fixedSpace_eq_annihilator ρ Z e hd hz] at hn
  have hc := fixedCodim_add_finrank ρ ⊤
  have hr : Module.finrank (ZMod 2) (Additive A) = Nat.log 2 (Nat.card A) := by
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [Nat.card_zmod] at hcard
    change _ = Nat.log 2 (Nat.card (Additive A))
    rw [hcard, Nat.log_pow Nat.one_lt_two]
  omega

/-- Every subgroup has fixed codimension its binary rank, including the identity subgroup. -/
theorem fixedCodim_eq_rank [Finite A] [FiniteDimensional (ZMod 2) V]
    (hZ : Module.finrank (ZMod 2) Z = 1)
    (hf : Function.Injective ρ)
    (hd : ∀ a v, ρ a v - v ∈ Z) (hz : ∀ a z, z ∈ Z → ρ a z = z)
    (W : Subgroup A) : fixedCodim ρ W = rank W := by
  let _ : IsElementaryAbelian 2 W := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun w =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) (w : A))) }
  let e : Z ≃ₗ[ZMod 2] ZMod 2 := LinearEquiv.ofFinrankEq _ _ (by simpa using hZ)
  have h := fixedCodim_top (ρ.comp W.subtype) Z e (fun w v => hd w v)
    (fun w z hz' => hz w z hz') (hf.comp W.subtype_injective)
  change Module.finrank (ZMod 2) (V ⧸ fixedSpace (ρ.comp W.subtype) ⊤) = rank W at h
  rw [fixedSpace_comp_map, ← MonoidHom.range_eq_map, W.range_subtype] at h
  exact h

end Representation.BinaryOffender.CommonCenter
