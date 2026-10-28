module
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Normal four-groups in the upper unitriangular group

A normal subgroup of UT₃(F) containing a noncentral element contains the entire
highest-root group: commutators with one of the two simple-root groups produce
any prescribed central coefficient. Over a finite field such a subgroup has
order at least twice the field order. Consequently a normal noncentral subgroup
of order four forces the field to have order two.

This is the local normal-subgroup calculation used in the paired A₃ screen of
Aschbacher–Smith, 2.4.32, printed p.547; the projective Sylow transport is in
the parent module.
-/

public section
open Subgroup
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3Even.CubicFourNormalizer
variable (F : Type*) [Field F]

theorem conjugate_displacement (g a : U F) :
    g * a * g⁻¹ * a⁻¹ = ⟨0,0,g.x * a.y - a.x * g.y⟩ := by
  apply U.ext
  · change g.x + a.x + -g.x + -a.x = 0
    ring
  · change g.y + a.y + -g.y + -a.y = 0
    ring
  · change ((g.c + a.c + g.x * a.y) + (g.x * g.y - g.c) +
      (g.x + a.x) * -g.y) + (a.x * a.y - a.c) +
      (g.x + a.x + -g.x) * -a.y = _
    ring

theorem center_le_of_normal_noncentral (A : Subgroup (U F)) [A.Normal]
    (hne : ¬ A ≤ Z F) : Z F ≤ A := by
  obtain ⟨a,ha,haz⟩ := Set.not_subset.mp hne
  intro z hz
  have hzxy := (mem_Z F z).mp hz
  have hcent : ∀ r : F, (⟨0,0,r⟩ : U F) ∈ A := by
    intro r
    by_cases hx : a.x = 0
    · have hy : a.y ≠ 0 := fun h => haz ((mem_Z F a).mpr ⟨hx,h⟩)
      let g : U F := ⟨r / a.y,0,0⟩
      have he : g * a * g⁻¹ * a⁻¹ = (⟨0,0,r⟩ : U F) := by
        rw [conjugate_displacement]
        apply U.ext
        · rfl
        · rfl
        change r / a.y * a.y - a.x * 0 = r
        simp [hy]
      rw [← he]
      exact A.mul_mem (Subgroup.Normal.conj_mem inferInstance a ha g) (A.inv_mem ha)
    · let g : U F := ⟨0,-r / a.x,0⟩
      have he : g * a * g⁻¹ * a⁻¹ = (⟨0,0,r⟩ : U F) := by
        rw [conjugate_displacement]
        apply U.ext
        · rfl
        · rfl
        change 0 * a.y - a.x * (-r / a.x) = r
        field_simp
        ring
      rw [← he]
      exact A.mul_mem (Subgroup.Normal.conj_mem inferInstance a ha g) (A.inv_mem ha)
  convert hcent z.c using 1
  exact U.ext hzxy.1 hzxy.2 rfl

variable [Finite F]

theorem two_mul_field_card_le_of_normal_noncentral
    (A : Subgroup (U F)) [A.Normal] (hne : ¬ A ≤ Z F) :
    2 * Nat.card F ≤ Nat.card A := by
  have hz := center_le_of_normal_noncentral F A hne
  let C := (Z F).subgroupOf A
  have hc : Nat.card C = Nat.card F :=
    (Nat.card_congr (subgroupOfEquivOfLe hz).toEquiv).trans (card_Z F)
  have hnt : C ≠ ⊤ := by
    intro he
    have hle : A ≤ Z F := (Subgroup.subgroupOf_eq_top).mp he
    exact hne hle
  have hi : 2 ≤ C.index := Subgroup.one_lt_index_of_ne_top hnt
  have hm := C.card_mul_index
  rw [hc] at hm
  calc
    2 * Nat.card F = Nat.card F * 2 := Nat.mul_comm _ _
    _ ≤ Nat.card F * C.index := Nat.mul_le_mul_left _ hi
    _ = Nat.card A := hm

theorem field_card_two_of_normal_four_noncentral
    (A : Subgroup (U F)) [A.Normal] (hcard : Nat.card A = 4)
    (hne : ¬ A ≤ Z F) : Nat.card F = 2 := by
  have hb := two_mul_field_card_le_of_normal_noncentral F A hne
  rw [hcard] at hb
  have hp := Finite.one_lt_card (α := F)
  omega

end Matrix.PSL3Even.CubicFourNormalizer
