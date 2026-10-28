module
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Data.ZMod.Basic
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# C-components of a double wreath product

If the solvable residual of D is quasisimple, every C-component of
D wr C₂ is one of the two embedded residual factors. Perfectness puts a
C-component in the index-two base; its identification then follows from
the direct-product component theorem. The equivalence uses the actual base
inclusion, so it can be composed with an ambient two-core quotient map.

Source application: Aschbacher--Smith 14.6.14(4) and14.6.15, printed
pp.1033--1034, with D = Aut(PSL₂(16)).
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.CComponentDoubleWreath
variable (D : Type*) [Group D]
abbrev C2 := Multiplicative (ZMod 2)
abbrev W := RegularWreathProduct D C2
private def swap : C2 := Multiplicative.ofAdd 1
private theorem swap_ne_one : swap ≠ 1 := by decide
private theorem index_cases (i : C2) : i = 1 ∨ i = swap := by revert i; decide
abbrev base : Subgroup (W D) := RegularWreathProduct.rightHom.ker

noncomputable def baseHom : D × D →* W D where
  toFun p := ⟨fun i => if i = 1 then p.1 else p.2,1⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · funext i; simp
    · rfl
  map_mul' p q := by
    apply RegularWreathProduct.ext
    · funext i
      by_cases hi : i = 1 <;> simp [hi,RegularWreathProduct.mul_left]
    · rfl

private theorem baseHom_injective : Function.Injective (baseHom D) := by
  intro p q h
  apply Prod.ext
  · simpa [baseHom] using congrArg (fun w : W D => w.left 1) h
  · simpa [baseHom,swap_ne_one] using congrArg (fun w : W D => w.left swap) h

noncomputable def baseEquiv : D × D ≃* base D :=
  MulEquiv.ofBijective ((baseHom D).codRestrict (base D) (fun _ => rfl))
    ⟨fun p q h => baseHom_injective D (congrArg Subtype.val h), by
      rintro ⟨w,hw⟩
      refine ⟨(w.left 1,w.left swap),Subtype.ext ?_⟩
      apply RegularWreathProduct.ext
      · funext i
        rcases index_cases i with rfl | rfl
        · simp [baseHom]
        · simp [baseHom,swap_ne_one]
      · exact hw.symm⟩

theorem base_index : (base D).index = 2 := by
  rw [index_ker,MonoidHom.range_eq_top.mpr (fun x =>
    ⟨RegularWreathProduct.inl x,rfl⟩),card_top]
  simp [C2,Nat.card_eq_fintype_card]

/-- The perfect C-component lies in the actual index-two base. -/
theorem component_le_base {K : Subgroup (W D)} (hK : K.IsCComponent) :
    K ≤ base D := by
  let := hK.perfect
  exact le_of_isPerfect_of_index_eq_two K (base D) (base_index D)

/-- Identify the actual C-component with one of the two residual factors. -/
theorem component_eq_factor (hr : IsQuasisimple (solvableResidual D))
    {K : Subgroup (W D)} (hK : K.IsCComponent) :
    K = ((solvableResidual D).prod (⊥ : Subgroup D)).map (baseHom D) ∨
      K = ((⊥ : Subgroup D).prod (solvableResidual D)).map (baseHom D) := by
  let e := (baseEquiv D).symm
  have he : (((K.subgroupOf (base D)).map e.toMonoidHom).map (baseHom D)) = K := by
    rw [map_map]
    have hi : (baseHom D).comp e.toMonoidHom = (base D).subtype := by
      apply MonoidHom.ext
      intro x
      exact congrArg Subtype.val ((baseEquiv D).apply_symm_apply x)
    rw [hi,map_subgroupOf_eq_of_le (component_le_base D hK)]
  rcases cComponent_eq_residual_factor (Or.inr hr) (Or.inr hr)
    ((hK.subgroupOf (component_le_base D hK)).map_equiv e) with h | h
  · exact Or.inl (he.symm.trans (congrArg (map (baseHom D)) h))
  · exact Or.inr (he.symm.trans (congrArg (map (baseHom D)) h))

/-- Every C-component has the genuine residual model of the base group. -/
theorem component_equiv (hr : IsQuasisimple (solvableResidual D))
    {K : Subgroup (W D)} (hK : K.IsCComponent) :
    Nonempty (K ≃* solvableResidual D) := by
  rcases component_eq_factor D hr hK with h | h
  · exact ⟨(MulEquiv.subgroupCongr h).trans
      ((((solvableResidual D).prod (⊥ : Subgroup D)).equivMapOfInjective
        (baseHom D) (baseHom_injective D)).symm.trans residualLeftEquiv)⟩
  · exact ⟨(MulEquiv.subgroupCongr h).trans
      ((((⊥ : Subgroup D).prod (solvableResidual D)).equivMapOfInjective
        (baseHom D) (baseHom_injective D)).symm.trans residualRightEquiv)⟩

/-- Prime-order control in each coordinate gives control by the two actual
component factors of the wreath product. -/
theorem mem_component_pair_of_pow_five
    (hr : IsQuasisimple (solvableResidual D))
    (hfive : ∀ x : D, x ^ 5 = 1 → x ∈ solvableResidual D)
    {A B : Subgroup (W D)} (hA : A.IsCComponent) (hB : B.IsCComponent)
    (hne : A ≠ B) {w : W D} (hw : w ^ 5 = 1) : w ∈ A ⊔ B := by
  let L := ((solvableResidual D).prod (⊥ : Subgroup D)).map (baseHom D)
  let R := ((⊥ : Subgroup D).prod (solvableResidual D)).map (baseHom D)
  have hgen : A ⊔ B = L ⊔ R := by
    rcases component_eq_factor D hr hA with ha | ha <;>
      rcases component_eq_factor D hr hB with hb | hb
    · exact (hne (ha.trans hb.symm)).elim
    · rw [ha,hb]
    · rw [ha,hb,sup_comm]
    · exact (hne (ha.trans hb.symm)).elim
  rw [hgen]
  have hright : w.right = 1 := by
    have hp : w.right ^ 5 = 1 := by
      change (RegularWreathProduct.rightHom w) ^ 5 = 1
      rw [←map_pow,hw,map_one]
    rcases index_cases w.right with hh | hh
    · exact hh
    · rw [hh] at hp
      exact (show swap ^ 5 ≠ 1 by decide) hp |>.elim
  let b : base D := ⟨w,hright⟩
  let x := (baseEquiv D).symm b
  have hx : baseHom D x = w := congrArg Subtype.val ((baseEquiv D).apply_symm_apply b)
  have hx5 : x ^ 5 = 1 := by
    apply baseHom_injective D
    rw [map_pow,hx,hw,map_one]
  have h1 : x.1 ∈ solvableResidual D := hfive x.1 (congrArg Prod.fst hx5)
  have h2 : x.2 ∈ solvableResidual D := hfive x.2 (congrArg Prod.snd hx5)
  have he : baseHom D (x.1,1) * baseHom D (1,x.2) = w := by
    rw [←map_mul]
    simpa only [Prod.mk_mul_mk,mul_one,one_mul] using hx
  rw [←he]
  exact mul_mem (mem_sup_left (mem_map_of_mem _ ⟨h1,rfl⟩))
    (mem_sup_right (mem_map_of_mem _ ⟨rfl,h2⟩))
end Theory.GroupTheory.CComponentDoubleWreath
