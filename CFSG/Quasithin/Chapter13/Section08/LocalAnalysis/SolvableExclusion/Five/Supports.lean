module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.QuotientAction

/-!
# Lifting the five-primary moved summands

A subgroup of U_H/V₁ has a canonical full inverse image in U_H. Its image
is the original summand, and it contains V₁. Invariance under the actual
star action lifts to relative normalization of this preimage. This avoids
requiring a selected odd-order complement to be normalized in G.

The final cardinality comparison derives the moved-space noncontainment
used by the fixed-space argument: a binary plane cannot be contained in
the image of the order-two source line A₁.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the last
paragraph of 13.8.13, printed p.951. Constructing the two summands and
establishing their invariance remains part of the five-primary analysis.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open Subgroup
variable {G : Type*} [Group G]
variable (UH V₁ : Subgroup G) [(V₁.subgroupOf UH).Normal]

/-- The full inverse image in U_H of a subgroup of the literal tilde quotient. -/
def liftTilde (S : Subgroup (UH ⧸ V₁.subgroupOf UH)) : Subgroup G :=
  (S.comap (QuotientGroup.mk' (V₁.subgroupOf UH))).map UH.subtype

theorem liftTilde_le (S : Subgroup (UH ⧸ V₁.subgroupOf UH)) :
    liftTilde UH V₁ S ≤ UH := map_subtype_le _

theorem tildeImage_liftTilde (S : Subgroup (UH ⧸ V₁.subgroupOf UH)) :
    tildeImage UH V₁ (liftTilde UH V₁ S) = S := by
  unfold tildeImage liftTilde
  rw [show ((S.comap (QuotientGroup.mk' (V₁.subgroupOf UH))).map UH.subtype).subgroupOf UH =
    S.comap (QuotientGroup.mk' (V₁.subgroupOf UH)) from
      comap_map_eq_self_of_injective UH.subtype_injective _]
  exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem denominator_le_liftTilde (S : Subgroup (UH ⧸ V₁.subgroupOf UH))
    (hV : V₁ ≤ UH) : V₁ ≤ liftTilde UH V₁ S := by
  intro v hv
  refine ⟨⟨v, hV hv⟩, ?_, rfl⟩
  change QuotientGroup.mk' (V₁.subgroupOf UH) ⟨v, hV hv⟩ ∈ S
  have hz : QuotientGroup.mk' (V₁.subgroupOf UH) ⟨v, hV hv⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hv
  rw [hz]
  exact S.one_mem

theorem mem_liftTilde (S : Subgroup (UH ⧸ V₁.subgroupOf UH)) (u : UH) :
    (u : G) ∈ liftTilde UH V₁ S ↔ QuotientGroup.mk' (V₁.subgroupOf UH) u ∈ S := by
  constructor
  · rintro ⟨v, hv, he⟩
    exact (show v = u from Subtype.ext he) ▸ hv
  · intro hu
    exact ⟨u, hu, rfl⟩

variable {UH V₁}

/-- Invariance of the actual quotient summand gives relative normalization
of its full inverse image, even if the chosen odd-order lift is not normalized. -/
theorem StarAction.normalizes_liftTilde {H : Subgroup G}
    (a : StarAction H UH V₁) (B : Subgroup G) (hB : B ≤ H)
    (S : Subgroup (UH ⧸ V₁.subgroupOf UH))
    (hS : ∀ b : a.actors B, ∀ x ∈ S, b • x ∈ S) :
    B ≤ normalizer (liftTilde UH V₁ S : Set G) := by
  have forward : ∀ b ∈ B, ∀ u ∈ liftTilde UH V₁ S,
      b * u * b⁻¹ ∈ liftTilde UH V₁ S := by
    intro b hb u hu
    have huU := liftTilde_le UH V₁ S hu
    let h : H := ⟨b, hB hb⟩
    let uU : UH := ⟨u, huU⟩
    let actor : a.actors B :=
      ⟨a.action (QuotientGroup.mk' (pCore 2 H) h),
        mem_map_of_mem a.action (mem_map_of_mem _ hb)⟩
    have hm := hS actor _ ((mem_liftTilde UH V₁ S uU).mp hu)
    change a.action (QuotientGroup.mk' (pCore 2 H) h)
      (QuotientGroup.mk' (V₁.subgroupOf UH) uU) ∈ S at hm
    rw [a.conjugation] at hm
    exact (mem_liftTilde UH V₁ S _).mpr hm
  intro b hb
  apply mem_normalizer_iff.mpr
  intro u
  constructor
  · exact forward b hb u
  · intro hu
    have hm := forward b⁻¹ (B.inv_mem hb) _ hu
    simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hm

theorem tildeImage_sup_denominator (X : Subgroup G) (hX : X ≤ UH) (hV : V₁ ≤ UH) :
    tildeImage UH V₁ (X ⊔ V₁) = tildeImage UH V₁ X := by
  unfold tildeImage
  rw [subgroupOf_sup hX hV, Subgroup.map_sup]
  have hz : (V₁.subgroupOf UH).map (QuotientGroup.mk' (V₁.subgroupOf UH)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [hz, sup_bot_eq]

theorem tildeImage_card_le [Finite G] (X : Subgroup G) (hX : X ≤ UH) :
    Nat.card (tildeImage UH V₁ X) ≤ Nat.card X := by
  have hd := (X.subgroupOf UH).card_map_dvd (QuotientGroup.mk' (V₁.subgroupOf UH))
  rw [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv] at hd
  exact Nat.le_of_dvd Nat.card_pos hd

/-- The two-dimensional moved space cannot lie in the image of a source
line. This supplies the noncontainment required by `fixedPreimage_le_DH`. -/
theorem moved_not_le_line_sup_denominator [Finite G]
    (Uγ A₁ : Subgroup G) (hA : A₁ ≤ UH) (hV : V₁ ≤ UH)
    (hline : Nat.card A₁ = 2)
    (hmoved : 2 < Nat.card (tildeImage UH V₁ ⁅UH, Uγ⁆)) :
    ¬ ⁅UH, Uγ⁆ ≤ A₁ ⊔ V₁ := by
  intro h
  have hi : tildeImage UH V₁ ⁅UH, Uγ⁆ ≤ tildeImage UH V₁ (A₁ ⊔ V₁) :=
    map_mono (fun _ hx => h hx)
  rw [tildeImage_sup_denominator A₁ hA hV] at hi
  have hc := (card_le_of_le hi).trans (tildeImage_card_le A₁ hA)
  omega

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
