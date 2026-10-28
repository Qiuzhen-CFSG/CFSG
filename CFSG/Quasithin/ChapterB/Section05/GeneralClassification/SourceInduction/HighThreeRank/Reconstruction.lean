module
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Reconstructing the actual outer A₆–C₃ configuration

The two centralizer equalities determine the outer generator. Conjugation on
C₃ has only two possible values, so an element acting nontrivially on C₃
supplements the product. The preimage of the inner automorphisms on either
factor is its product with its centralizer; this proves that the same element
acts outer on both factors. Centerlessness of A₆ makes the product internal,
with multiplication of the specified inclusions as its isomorphism.

This supplies the last group-theoretic step of B.5.7. It does not construct
the A₆ identification or the two centralizer equalities from an FF-module.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.106.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank
variable {G : Type*} [Group G] [Finite G]

/-- The literal group shape follows from the two relative centralizers;
no complement, outer automorphism or generating element is assumed. -/
theorem outerShape_of_centralizers (L X : Subgroup G) [L.Normal] [X.Normal]
    (eL : L ≃* alternatingGroup (Fin 6))
    (eX : X ≃* Multiplicative (ZMod 3))
    (hL : centralizer (L : Set G) = X)
    (hX : centralizer (X : Set G) = L ⊔ X)
    (hn : ¬ X ≤ center G) : Nonempty (OuterSixThreeShape G) := by
  classical
  let : IsCyclic X := eX.isCyclic.mpr inferInstance
  let : CommGroup X := IsCyclic.commGroup
  have hc : L ≤ centralizer (X : Set G) := hX.symm ▸ le_sup_left
  have hd : Disjoint L X := by
    apply disjoint_def.mpr
    intro x hxL hxX
    have hz : (⟨x, hxL⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro l
      apply Subtype.ext
      exact (show x ∈ centralizer (L : Set G) from hL.symm ▸ hxX) l l.property
    have hz' := (Subgroup.centerCongr eL ⟨_, hz⟩).property
    change eL ⟨x, hxL⟩ ∈ center (alternatingGroup (Fin 6)) at hz'
    rw [alternatingGroup.center_eq_bot (by simp)] at hz'
    have he : eL ⟨x, hxL⟩ = 1 := mem_bot.mp hz'
    have : (⟨x, hxL⟩ : L) = 1 := eL.injective (he.trans eL.map_one.symm)
    exact congrArg Subtype.val this
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting L X hd hc
  have hC : centralizer (X : Set G) ≠ ⊤ := by
    exact fun h => hn (centralizer_eq_top_iff_subset.mp h)
  obtain ⟨t, ht⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hC)
  have htC : t ∉ centralizer (X : Set G) := ht.2
  let f : G →* MulAut X := MulAut.conjNormal
  have hker : f.ker = centralizer (X : Set G) :=
    MulAut.conjNormal_ker_eq_centralizer X
  have ht1 : f t ≠ 1 := by
    intro h
    exact htC (hker ▸ h)
  have hcard : Nat.card (MulAut X) = 2 := by
    rw [IsCyclic.card_mulAut, Nat.card_congr eX.toEquiv]
    norm_num
    decide
  have dichotomy (g : G) : f g = 1 ∨ f g = f t := by
    by_cases hg : f g = 1
    · exact Or.inl hg
    · obtain ⟨a, ha, hu⟩ := (Nat.card_eq_two_iff' (1 : MulAut X)).mp hcard
      exact Or.inr ((hu _ hg).trans (hu _ ht1).symm)
  have hgen : (L ⊔ X) ⊔ zpowers t = ⊤ := by
    apply top_unique
    intro g _
    rcases dichotomy g with hg | hg
    · exact (show L ⊔ X ≤ (L ⊔ X) ⊔ zpowers t from le_sup_left) (hX ▸ (hker ▸ hg))
    · have hgt : g * t⁻¹ ∈ f.ker := by
        change f (g * t⁻¹) = 1
        rw [map_mul, map_inv, hg, mul_inv_cancel]
      have hgt' : g * t⁻¹ ∈ (L ⊔ X) ⊔ zpowers t :=
        (show L ⊔ X ≤ (L ⊔ X) ⊔ zpowers t from le_sup_left) (hX ▸ (hker ▸ hgt))
      have htt : t ∈ (L ⊔ X) ⊔ zpowers t :=
        (show zpowers t ≤ (L ⊔ X) ⊔ zpowers t from le_sup_right) (mem_zpowers t)
      simpa using ((L ⊔ X) ⊔ zpowers t).mul_mem hgt' htt
  have htLX : t ∉ L ⊔ X := hX ▸ htC
  refine ⟨⟨L, X, e, he, eL, eX, t, hgen, ?_, ?_⟩⟩
  · refine ⟨MulAut.conjNormal t, fun _ => rfl, ?_⟩
    intro htinner
    have hm : t ∈ (MulAut.innerSubgroup L).comap (MulAut.conjNormal : G →* MulAut L) :=
      htinner
    rw [MulAut.conjNormal_comap_innerSubgroup, hL] at hm
    exact htLX hm
  · refine ⟨MulAut.conjNormal t, fun _ => rfl, ?_⟩
    intro htinner
    have hm : t ∈ (MulAut.innerSubgroup X).comap f := htinner
    change t ∈ (MulAut.innerSubgroup X).comap (MulAut.conjNormal : G →* MulAut X) at hm
    rw [MulAut.conjNormal_comap_innerSubgroup,
      sup_of_le_right (le_centralizer X)] at hm
    exact htC hm

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank
