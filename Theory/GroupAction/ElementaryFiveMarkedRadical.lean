module
public import Theory.GroupAction.BinaryFixedLineQuotient
public import Theory.SpecificGroups.BinaryLinear.RadicalCardinality

/-!
# The full radical at a marked four in an elementary group of order 32

A group of 64 automorphisms fixing a marked four pointwise and acting
trivially on the quotient is the entire 2+3 radical. Its common fixed group
is that same four and its normalizer is precisely the four's stabilizer.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace MulAut
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

/-- Full size recognizes the actual marked radical and its normalizer. -/
theorem elementary_five_marked_radical
    (hE : Nat.card E = 32) (H : Subgroup E) (hH : Nat.card H = 4)
    (R : Subgroup (MulAut E)) (hR : Nat.card R = 64)
    (hfix : ∀ a ∈ R, ∀ x ∈ H, a x = x)
    (hdisp : ∀ a ∈ R, ∀ x : E, a x * x⁻¹ ∈ H) :
    (∀ a : MulAut E, a ∈ R ↔
      (∀ x ∈ H, a x = x) ∧ ∀ x : E, a x * x⁻¹ ∈ H) ∧
    (∀ x : E, (∀ a ∈ R, a x = x) ↔ x ∈ H) ∧
    (∀ a : MulAut E, a ∈ normalizer (R : Set (MulAut E)) ↔
      ∀ x : E, a x ∈ H ↔ x ∈ H) := by
  let W : Submodule (ZMod 2) (Additive E) :=
    AddSubgroup.toZModSubmodule 2 H.toAddSubgroup
  let e : MulAut E ≃* BinaryLinear.GL (Additive E) := BinaryFixedLine.linearAutEquiv
  let w : W ≃ H :=
    { toFun x := ⟨x.val.toMul,x.property⟩
      invFun x := ⟨Additive.ofMul x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hWcard : Nat.card W = 4 := (Nat.card_congr w).trans hH
  have hEdim : Module.finrank (ZMod 2) (Additive E) = 5 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hh
    simpa only [Nat.card_zmod,hE] using hh.symm
  have hWdim : Module.finrank (ZMod 2) W = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    simpa only [Nat.card_zmod,hWcard] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)).symm
  let : Finite (BinaryLinear.GL (Additive E)) :=
    Finite.of_injective (fun g : BinaryLinear.GL (Additive E) => (g : Additive E → Additive E))
      DFunLike.coe_injective
  have hW : W ≠ ⊥ := by
    apply Submodule.nontrivial_iff_ne_bot.mp
    exact Finite.one_lt_card_iff_nontrivial.mp (by rw [hWcard]; decide)
  have hle : R.map e.toMonoidHom ≤ BinaryLinear.radical W := by
    rintro _ ⟨a,ha,rfl⟩
    refine ⟨?_,?_⟩
    · intro x hx
      exact congrArg Additive.ofMul (hfix a ha x.toMul hx)
    · intro x
      change a x.toMul / x.toMul ∈ H
      simpa only [div_eq_mul_inv] using hdisp a ha x.toMul
  have heq : R.map e.toMonoidHom = BinaryLinear.radical W :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective e.injective,hR]
      have hh := BinaryLinear.radical_card_le W
      norm_num [hEdim,hWdim] at hh
      exact hh)
  have hmem (a : MulAut E) : a ∈ R ↔ e a ∈ BinaryLinear.radical W := by
    rw [←heq]
    exact (mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm
  refine ⟨?_,?_,?_⟩
  · intro a
    constructor
    · intro ha
      exact ⟨hfix a ha,hdisp a ha⟩
    · rintro ⟨ha,hb⟩
      apply (hmem a).mpr
      refine ⟨?_,?_⟩
      · intro x hx
        exact congrArg Additive.ofMul (ha x.toMul hx)
      · intro x
        change a x.toMul / x.toMul ∈ H
        simpa only [div_eq_mul_inv] using hb x.toMul
  · intro x
    have hh := (BinaryLinear.mem_iff_fixed_radical hW (Additive.ofMul x)).symm
    constructor
    · intro hx
      apply hh.mp
      intro g hg
      obtain ⟨a,rfl⟩ := e.surjective g
      exact congrArg Additive.ofMul (hx a ((hmem a).mpr hg))
    · intro hx a ha
      exact congrArg Additive.toMul ((hh.mpr hx) (e a) ((hmem a).mp ha))
  · intro a
    have hh : a ∈ normalizer (R : Set (MulAut E)) ↔
        e a ∈ BinaryLinear.parabolic W := by
      rw [←mem_map_iff_mem (f := e.toMonoidHom) e.injective,map_equiv_normalizer_eq,heq,
        BinaryLinear.normalizer_radical hW]
      rfl
    exact hh
end MulAut
