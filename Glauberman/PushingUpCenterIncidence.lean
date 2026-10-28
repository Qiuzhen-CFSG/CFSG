module
public import Glauberman.PushingUpCenterCovering

/-!
# Exact centralizer incidence in the original natural center

Every subgroup of the original Sylow group escaping O₂(H) has fixed index
at least four on the center of O₂(H). The full Sylow has fixed index at
most four, so containment forces their fixed groups to agree exactly with
Z(S). Thus an element outside O₂(H) cannot commute with a vector outside
Z(S) in Z(O₂(H)). The argument keeps arbitrary central fixed attachments.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem 4.7(d),
printed page 48, for its initial endpoint pair. Transport to the interval
points and the stronger per-element covering conclusions are separate.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

theorem original_psl2_four_center_fixed_eq
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α)
    (A : Subgroup H) (hAS : A ≤ (S : Subgroup H)) (hAQ : ¬ A ≤ pCore 2 H) :
    centerIn (pCore 2 H) ⊓ centralizer (A : Set H) = centerIn (S : Subgroup H) := by
  let V := omegaCenterIn (pCore 2 H)
  obtain ⟨_,hZS⟩ := original_psl2_four_full_center_fixed_spaces hF S α hu K e hf hno
  have hV := (original_psl2_four_omegaCenters_eq_centers hF S α hu K e hf hno).2
  have hlo := (original_psl2_four_omega_fixedIndex_data hF S hu K e hf
    hno.noCharacteristicNormal).1 A hAS hAQ
  have hd := (original_psl2_four_omegaAction_sylow hF S hu K e hf
    hno.noCharacteristicNormal).2.2.1
  have hupper : (centerIn (S : Subgroup H)).relIndex V ≤ 4 := by
    rw [← hZS]
    change ((omegaCenterIn (pCore 2 H)) ⊓ centralizer ((S : Subgroup H) : Set H)).relIndex
      (omegaCenterIn (pCore 2 H)) ≤ 4
    rw [omegaAction_fixed_index]
    exact Nat.pow_le_pow_right (by decide) hd
  have hle : centerIn (S : Subgroup H) ≤ V ⊓ centralizer (A : Set H) := by
    rw [←hZS]
    exact inf_le_inf_left V (centralizer_le hAS)
  have hmul := relIndex_mul_relIndex (centerIn (S : Subgroup H))
    (V ⊓ centralizer (A : Set H)) V hle inf_le_left
  have hpos : 0 < (centerIn (S : Subgroup H)).relIndex (V ⊓ centralizer (A : Set H)) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hi : (centerIn (S : Subgroup H)).relIndex (V ⊓ centralizer (A : Set H)) = 1 := by
    change 4 ≤ (V ⊓ centralizer (A : Set H)).relIndex V at hlo
    nlinarith
  have he : V ⊓ centralizer (A : Set H) = centerIn (S : Subgroup H) :=
    le_antisymm (relIndex_eq_one.mp hi) hle
  simpa only [V,hV] using he

theorem original_psl2_four_center_noncommutation
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α)
    (x y : H) (hxS : x ∈ (S : Subgroup H)) (hxQ : x ∉ pCore 2 H)
    (hyV : y ∈ centerIn (pCore 2 H)) (hyZ : y ∉ centerIn (S : Subgroup H)) :
    ⁅x, y⁆ ≠ 1 := by
  intro hcomm
  have hxy : x * y = y * x := commutatorElement_eq_one_iff_mul_comm.mp hcomm
  have hc : y ∈ centralizer (zpowers x : Set H) := by
    rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    exact hxy.symm
  have hfixed := original_psl2_four_center_fixed_eq hF S α hu K e hf hno
    (zpowers x) (zpowers_le.mpr hxS) (fun h => hxQ (h (mem_zpowers x)))
  exact hyZ (hfixed ▸ (show y ∈ centerIn (pCore 2 H) ⊓ centralizer (zpowers x : Set H) from ⟨hyV,hc⟩))

end Glauberman
