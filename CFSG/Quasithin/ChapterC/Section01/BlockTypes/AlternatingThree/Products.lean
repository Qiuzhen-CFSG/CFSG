module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import Mathlib.GroupTheory.NoncommPiCoprod
/-!
# Sixth powers in central products of alternating-three blocks

The two-core of an A₃ block is its elementary commutator layer, and the
quotient has order three. Cubing therefore lands in the two-core, so every
sixth power is one. A finite family of commuting blocks inherits this law
through its multiplication homomorphism, without any independence premise.

Source application: the non-A₃-product clause of Aschbacher--Smith 15.1.22,
printed pp.1098--1100. Actual model residuals can disprove this law.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- Cubing lands in the elementary two-core of the original A₃ block. -/
theorem IsAlternatingBlock.pow_six {H : Type*} [Group H]
    (h : IsAlternatingBlock H 3) (a : H) : a ^ 6 = 1 := by
  have hc : Nat.card (H ⧸ pCore 2 H) = 3 := by
    obtain ⟨e⟩ := h.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  let : IsElementaryAbelian 2 (pCore 2 H) := by
    rw [h.2.1.core_eq_blockU_of_quotient_three hc]
    exact h.2.1.elementary
  have ha : a ^ 3 ∈ pCore 2 H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (pCore 2 H)) (a^3) = 1
    rw [map_pow,←hc]
    exact pow_card_eq_one'
  have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) (a^3) ha
  simpa only [←pow_mul] using hh

/-- Every element of a central product of A₃ blocks has sixth power one. -/
theorem alternatingThree_product_pow_six
    (F : Set (Subgroup G))
    (hF : ∀ A ∈ F, IsAlternatingBlock A 3)
    (hc : F.Pairwise (fun A B => ⁅A,B⁆ = ⊥))
    {x : G} (hx : x ∈ sSup F) : x ^ 6 = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hcomm : Pairwise fun i j : F => ∀ x y : G, x ∈ i.val → y ∈ j.val → Commute x y := by
    intro i j hne x y hx hy
    have h := (commutator_eq_bot_iff_le_centralizer.mp
      (hc i.property j.property (fun he => hne (Subtype.ext he)))) hx
    exact (mem_centralizer_iff.mp h y hy).symm
  let f := Subgroup.noncommPiCoprod hcomm
  have hf : f.range = sSup F := (Subgroup.noncommPiCoprod_range (hcomm := hcomm)).trans (sSup_eq_iSup' F).symm
  obtain ⟨u,rfl⟩ := hf ▸ hx
  have hu : u ^ 6 = 1 := by
    funext i
    exact (hF i.val i.property).pow_six (u i)
  rw [←map_pow,hu,map_one]
end CFSG.Quasithin.ChapterC
