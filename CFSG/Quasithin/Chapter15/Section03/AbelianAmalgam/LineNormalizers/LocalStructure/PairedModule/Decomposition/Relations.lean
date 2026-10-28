module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.MarkedAction

/-!
# Operator relations in the marked binary line section

The two marked permutations have orders three and two. Their S₃ relation,
together with the norm-zero identity in `ActionData`, gives
`τ y⁻¹ = τ + y⁻¹ τ` on the section. The second factor commutes with these
operators. These are the algebraic inputs to the explicit paired coordinates.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1153,
PDF p.1170, proof of 15.3.67 before the temporary replacement.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
open Descent.QuotientIdentification
variable {G : Type*} [Group G]
variable (V E : Subgroup G) [IsElementaryAbelian 2 (lineV V E)]
variable {Y T : Subgroup G} (d : MarkedDecomposition Y T E)
variable (hcomm : ⁅lineV V E, lineQ E⁆ ≤ E) (a : ActionData V E d)

private lemma perm_three_relation : ∀ r t : Equiv.Perm (Fin 3),
    r ^ 3 = 1 → t ^ 2 = 1 → t ≠ 1 → t * r⁻¹ = r * t := by decide +kernel

include hcomm a in
lemma tau_action_square (x : SectionSpace V E) :
    sectionRepresentation V E ⟨d.tau, d.tau_mem.2⟩
      (sectionRepresentation V E ⟨d.tau, d.tau_mem.2⟩ x) = x := by
  let t := d.equiv (quotientMap E ⟨d.tau, d.tau_mem.2⟩)
  have ht : t ^ 2 = 1 := by
    apply Prod.ext
    · change t.1 ^ 2 = 1
      simpa only [t, a.tau_order] using pow_orderOf_eq_one t.1
    · simp [t, marked_tau_second E d]
  rw [← markedRepresentation_apply V E d hcomm, ← Module.End.mul_apply,
    ← map_mul, ← pow_two, ht, map_one, Module.End.one_apply]

include a in
lemma cycle_action_inverse (x : SectionSpace V E) :
    sectionRepresentation V E a.y x = x + sectionRepresentation V E a.y⁻¹ x := by
  have hn := a.norm_eq_zero (sectionRepresentation V E a.y⁻¹ x)
  have h₁ : sectionRepresentation V E a.y (sectionRepresentation V E a.y⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h₂ : sectionRepresentation V E (a.y * a.y) (sectionRepresentation V E a.y⁻¹ x) =
      sectionRepresentation V E a.y x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
  rw [h₁, h₂] at hn
  have hadd (z : SectionSpace V E) : z + z = 0 := by
    have hh := @two_smul (ZMod 2) (SectionSpace V E) _ _ _ z
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at hh
    exact hh.symm
  have hh := congrArg (fun z => z + sectionRepresentation V E a.y x) hn
  rw [add_assoc, hadd, add_zero, zero_add] at hh
  exact hh.symm.trans (add_comm _ _)

include hcomm a in
lemma tau_rightConjugation_relation (x : SectionSpace V E) :
    sectionRepresentation V E ⟨d.tau, d.tau_mem.2⟩
      (sectionRepresentation V E a.y⁻¹ x) =
    sectionRepresentation V E ⟨d.tau, d.tau_mem.2⟩ x +
      sectionRepresentation V E a.y⁻¹ (sectionRepresentation V E ⟨d.tau, d.tau_mem.2⟩ x) := by
  let r := d.equiv (quotientMap E a.y)
  let t := d.equiv (quotientMap E ⟨d.tau, d.tau_mem.2⟩)
  have ht : t.1 ≠ 1 := by
    intro hh
    have ho := a.tau_order
    change orderOf t.1 = 2 at ho
    rw [hh, orderOf_one] at ho
    contradiction
  have hrel : t * r⁻¹ = r * t := by
    apply Prod.ext
    · exact perm_three_relation r.1 t.1
        (by simpa only [r, a.y_order] using pow_orderOf_eq_one r.1)
        (by simpa only [t, a.tau_order] using pow_orderOf_eq_one t.1) ht
    · simp [r, t, a.y_second, marked_tau_second E d]
  have he : sectionRepresentation V E ⟨d.tau, d.tau_mem.2⟩
      (sectionRepresentation V E a.y⁻¹ x) =
      sectionRepresentation V E a.y (sectionRepresentation V E ⟨d.tau, d.tau_mem.2⟩ x) := by
    rw [← markedRepresentation_apply V E d hcomm ⟨d.tau, d.tau_mem.2⟩,
      ← markedRepresentation_apply V E d hcomm a.y⁻¹,
      ← markedRepresentation_apply V E d hcomm a.y]
    simp only [map_inv]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    exact congrArg (fun z => markedRepresentation V E d hcomm z x) hrel
  rw [he, cycle_action_inverse]

lemma first_action_commutes_second (g : lineNormalizer E)
    (hg : (d.equiv (quotientMap E g)).2 = 1) (c : centralizerImage E) (x : SectionSpace V E) :
    sectionRepresentation V E g (markedRepresentation V E d hcomm (1, c) x) =
      markedRepresentation V E d hcomm (1, c) (sectionRepresentation V E g x) := by
  rw [← markedRepresentation_apply V E d hcomm g]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  apply Prod.ext <;> simp [hg]

include a in
lemma mem_first_fixedImage (x : SectionSpace V E) :
    x ∈ fixedImage V E d.tau ↔ sectionRepresentation V E ⟨d.tau, d.tau_mem.2⟩ x = x := by
  rw [a.fixedImage_eq, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
