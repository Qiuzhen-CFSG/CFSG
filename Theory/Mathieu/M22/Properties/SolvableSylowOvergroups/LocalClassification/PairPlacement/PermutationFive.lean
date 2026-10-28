module

public import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Support
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Finite.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# A fixed point for an order-24 subgroup of S₅

For an orbit of size k, restriction to it and its complement embeds the group
in S_k × S_(5-k), bounding its order by k!(5-k)!. Orbit–stabilizer also makes
k divide 24. Consequently each orbit has size one or four, and a four-point
orbit has an invariant singleton complement.

This elementary permutation result supplies the five-hexad step for
Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973), using the pair action
associated to E.4.3(2). The argument specializes the orbit bound already used
in `Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.
LocalGeometry.SevenConstruction.MarkingConstruction`.
-/

namespace Sporadic.Mathieu.M22SolvableSylow.LocalClassification

open Equiv Subgroup MulAction

private theorem orbit_card_bound (H : Subgroup (Perm (Fin 5))) (x : Fin 5) :
    Nat.card H ≤ (Nat.card (orbit H x)).factorial * (5 - Nat.card (orbit H x)).factorial := by
  classical
  let p : Fin 5 → Prop := fun y => y ∈ orbit H x
  have hinv (g : Perm (Fin 5)) (hg : g ∈ H) (a : Fin 5) : p (g a) ↔ p a := by
    change g • a ∈ orbit H x ↔ a ∈ orbit H x
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨⟨g, hg⟩⁻¹ * h, by
        change (⟨g, hg⟩⁻¹ : H) • (h • x) = a
        change h • x = (⟨g, hg⟩ : H) • a at hh
        rw [hh, inv_smul_smul]⟩
    · rintro ⟨h, hh⟩
      exact ⟨⟨g, hg⟩ * h, by simp [mul_smul, hh]⟩
  have hle : H ≤ (Perm.subtypeCongrHom p).range := by
    intro g hg
    refine ⟨(g.subtypePerm (hinv g hg), g.subtypePerm (fun a => not_congr (hinv g hg a))), ?_⟩
    apply Equiv.ext
    intro a
    change (Perm.subtypeCongr _ _) a = g a
    by_cases ha : p a
    · rw [Perm.subtypeCongr.left_apply _ _ ha]; rfl
    · rw [Perm.subtypeCongr.right_apply _ _ ha]; rfl
  have hcard := Subgroup.card_le_of_le hle
  have hr : Nat.card (Perm.subtypeCongrHom p).range =
      Nat.card (Perm {a // p a} × Perm {a // ¬ p a}) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_coeSort_range
      (Perm.subtypeCongrHom_injective p)]
  rw [hr] at hcard
  simpa [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_subtype_compl, p] using hcard

open scoped Classical in
private theorem orbit_card_options (H : Subgroup (Perm (Fin 5))) (hH : Nat.card H = 24)
    (x : Fin 5) : Fintype.card (orbit H x) = 1 ∨ Fintype.card (orbit H x) = 4 := by
  classical
  have hb := orbit_card_bound H x
  rw [hH, Nat.card_eq_fintype_card] at hb
  have hpos : 0 < Fintype.card (orbit H x) := Fintype.card_pos_iff.mpr
    ⟨⟨x, mem_orbit_self x⟩⟩
  have hle : Fintype.card (orbit H x) ≤ 5 := by
    simpa using Fintype.card_subtype_le (fun y => y ∈ orbit H x)
  have hd : Fintype.card (orbit H x) ∣ 24 := by
    rw [← hH, Nat.card_eq_fintype_card]
    exact ⟨_, (card_orbit_mul_card_stabilizer_eq_card_group H x).symm⟩
  interval_cases hn : Fintype.card (orbit H x) <;> norm_num [hn, Nat.factorial] at *

/-- Every order-24 subgroup of the actual five-point symmetric group fixes a point. -/
public theorem s5_exists_fixed_point_of_card_eq_24 (H : Subgroup (Perm (Fin 5))) (hH : Nat.card H = 24) :
    ∃ x : Fin 5, ∀ g : H, (g : Perm (Fin 5)) x = x := by
  classical
  rcases orbit_card_options H hH 0 with h | h
  · exact ⟨0, mem_fixedPoints_iff_card_orbit_eq_one.mpr h⟩
  have hc : Fintype.card ↥(orbit H (0 : Fin 5))ᶜ = 1 := by
    rw [Fintype.card_compl_set, Fintype.card_fin, h]
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hc
  refine ⟨x, fun g => ?_⟩
  have hn : (g : Perm (Fin 5)) x ∉ orbit H (0 : Fin 5) := by
    intro hm
    apply x.property
    change g • (x : Fin 5) ∈ orbit H (0 : Fin 5) at hm
    have hm' := mem_orbit_of_mem_orbit g⁻¹ hm
    simpa using hm'
  exact congrArg Subtype.val (hx ⟨(g : Perm (Fin 5)) x, hn⟩)

end Sporadic.Mathieu.M22SolvableSylow.LocalClassification
