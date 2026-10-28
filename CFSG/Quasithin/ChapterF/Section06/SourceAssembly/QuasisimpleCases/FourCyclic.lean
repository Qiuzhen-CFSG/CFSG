module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.FourComponent
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.RemainingBranch
/-!
# The cyclic-three-core case with common Sylow order four

If a component contains exactly one local residual, its Sylow subgroup
lies in the opposite two-core, which here has order two. Perfect transfer
and the odd-order theorem exclude this. The source component reduction
therefore yields the quasisimple two-residual alternative without needing
the still-independent full rigidity theorem.

Source: Aschbacher–Smith F.6.17–18, printed pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}

theorem no_single_residual_component_of_intersection_four
    (h : IsGoldschmidtTriple G₁ G₂) (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4) :
    ¬ Nonempty (SingleResidualComponent G₁ G₂) := by
  rintro ⟨d⟩
  let K := d.component
  let : K.Normal := d.normal
  let : IsQuasisimple K := d.isComponent.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  let Q := (pCore 2 G₂).map G₂.subtype
  have hQ : Nat.card Q = 2 := by
    let U := Q.subgroupOf (G₂ ⊓ G₁)
    have hi : U.index = 2 := h.symm.left_core_index
    have hc := U.index_mul_card
    have hTs : Nat.card (G₂ ⊓ G₁ : Subgroup G) = 4 := by
      simpa only [inf_comm] using hT
    rw [hi, hTs] at hc
    rw [← Nat.card_congr (subgroupOfEquivOfLe h.symm.local_twoCore_le_intersection).toEquiv]
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hc
  obtain ⟨P, hP⟩ := sylow_in_normal_eq_right_core_intersection h K d.right_escapes
  have hPcard : Nat.card P ≤ 2 := by
    have he : Nat.card ((P : Subgroup K).map K.subtype) = Nat.card P :=
      card_map_of_injective K.subtype_injective
    rw [← he, hP]
    exact (card_le_of_le inf_le_left).trans_eq hQ
  have heven : Even (Nat.card K) := by
    by_contra! hh
    exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K (Nat.not_even_iff_odd.mp hh))
  have hh := perfect_sylow_two_card_gt_two P heven
  omega

theorem cyclic_four_quasisimple_source
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂) (hc : IsCyclic (pCore 3 G))
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4) :
    pResidual 2 G = generalizedFitting G ∧ IsQuasisimple (pResidual 2 G) := by
  rcases source_F_6_17_reduction hA hH e h hc with hq | hq | hq
  · exact hq
  · exact (no_single_residual_component_of_intersection_four h hT hq).elim
  · exact (no_single_residual_component_of_intersection_four h.symm
      (by simpa only [inf_comm] using hT) hq).elim
end CFSG.Quasithin.ChapterF.SourceAssembly
