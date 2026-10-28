module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CyclicComponent
public import CFSG.Quasithin.ChapterF.Section06.Elementary
public import Theory.GroupTheory.PerfectSylowTwo
/-!
# Excluding the smallest amalgam in the cyclic component branch

The common Sylow intersection meets each component in an actual Sylow
subgroup. A component has even order by the odd-order theorem, and its
perfectness excludes a Sylow subgroup of order at most two by transfer.
Thus the source's order-two intersection cannot occur once the cyclic
three-core argument constructs a component.

Source: Aschbacher–Smith F.6.18, fourth proof paragraph, printed p.310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ K : Subgroup G}
theorem intersection_card_gt_two_of_component
    (h : IsGoldschmidtTriple G₁ G₂) (hK : IsComponent G K) :
    2 < Nat.card (G₁ ⊓ G₂ : Subgroup G) := by
  obtain ⟨P, hP⟩ := h.subnormal_intersection_sylow K hK.1
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have heven : Even (Nat.card K) := by
    by_contra! hh
    have ho := Nat.not_even_iff_odd.mp hh
    exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K ho)
  have hp := perfect_sylow_two_card_gt_two P heven
  have hle : Nat.card P ≤ Nat.card (G₁ ⊓ G₂ : Subgroup G) := by
    let f : P → (G₁ ⊓ G₂ : Subgroup G) := fun x => ⟨x.val.val, by
      have hx : x.val ∈ (P : Subgroup K) := x.property
      rw [hP] at hx
      exact hx⟩
    apply Nat.card_le_card_of_injective f
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (G₁ ⊓ G₂ : Subgroup G) => (z : G)) hxy
  exact hp.trans_le hle

theorem intersection_card_gt_two_of_cyclic_three_core
    {H : Type*} [Group H] [Finite H] (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂) (hc : IsCyclic (pCore 3 G)) :
    2 < Nat.card (G₁ ⊓ G₂ : Subgroup G) := by
  obtain ⟨K, hK, _⟩ := Cyclic.exists_component_of_cyclic_three_core_quotient e h hc
  exact intersection_card_gt_two_of_component h hK
end CFSG.Quasithin.ChapterF.SourceAssembly
