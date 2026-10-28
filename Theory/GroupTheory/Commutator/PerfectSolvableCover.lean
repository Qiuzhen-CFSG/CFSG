module

public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Removing a commuting solvable factor from a perfect subgroup

A set-product cover of a perfect subgroup by D and a commuting solvable L
already puts it in D. Pull the cover back to X × L. Its solvable residual
surjects onto X and has trivial image in L, so each element of X lies in D.

This is the factor-selection argument in Aschbacher–Smith, Lemma 2.4.6
and Proposition E.6.23, printed pp.528 and 254.
-/

public section
open Subgroup
namespace Subgroup
theorem perfect_le_of_commuting_solvable_cover {G : Type*} [Group G] [Finite G] (X D L : Subgroup G)
    [Group.IsPerfect X] [Group.IsSolvable L]
    (hc : L ≤ centralizer (X : Set G))
    (hcover : ∀ x ∈ X, ∃ d ∈ D, ∃ l ∈ L, d * l = x) : X ≤ D := by
  let f : X × L →* G := X.subtype.noncommCoprod L.subtype
    (fun x l => (mem_centralizer_iff.mp (hc l.property) x x.property))
  let P := D.comap f
  let a : P →* X := (MonoidHom.fst X L).comp P.subtype
  let b : P →* L := (MonoidHom.snd X L).comp P.subtype
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨d, hd, l, hl, he⟩ := hcover x x.property
    have hh : f (x, (⟨l, hl⟩ : L)⁻¹) = d := by
      change (x : G) * l⁻¹ = d
      rw [← he, mul_inv_cancel_right]
    exact ⟨⟨(x, (⟨l, hl⟩ : L)⁻¹), show f (x, (⟨l, hl⟩ : L)⁻¹) ∈ D from hh.symm ▸ hd⟩, rfl⟩
  have hab : (solvableResidual P).map a = ⊤ := by
    rw [map_solvableResidual_eq a ha, solvableResidual_eq_top]
  have hbb : (solvableResidual P).map b = ⊥ :=
    eq_bot_mono (map_solvableResidual_le b) solvableResidual_eq_bot
  intro x hx
  obtain ⟨y, hy, he⟩ := mem_map.mp (show (⟨x, hx⟩ : X) ∈
    (solvableResidual P).map a from hab.symm ▸ mem_top _)
  have hby : b y = 1 := by
    exact mem_bot.mp (hbb ▸ mem_map_of_mem b hy)
  have hay : (y.val.1 : G) = x := congrArg Subtype.val he
  have hbly : (y.val.2 : G) = 1 := congrArg Subtype.val hby
  have hmem : f y.val ∈ D := y.property
  change (y.val.1 : G) * (y.val.2 : G) ∈ D at hmem
  simpa only [hay, hbly, mul_one] using hmem

end Subgroup
