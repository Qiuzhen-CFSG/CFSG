module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.Action
public import Theory.GroupAction.Invariant

/-!
# The exceptional image forces the space into the residual

An automorphism of order seven on a group of order eight fixes only the
identity, by the fixed-point congruence modulo seven. The same congruence
on any invariant subgroup forces that subgroup to be trivial or full.
Cauchy's theorem supplies such an automorphism in the image of order 21.
Applying this to `V ∩ X`, which contains the nontrivial root group, proves
`V ≤ X`. Irreducibility is a consequence, not an extra source premise.

The counting proof follows the general pattern of
`Theory/GroupAction/ThirtyOneOnThirtyTwoIrreducible.lean`.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
Lemma 16.5.13, printed p.1202.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
open Subgroup

private theorem invariant_subgroups_of_seven
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 8)
    (A : Subgroup (MulAut E)) (hA : Nat.card A = 7) :
    ∀ D : Subgroup E, (∀ a : A, ∀ x : E, x ∈ D → a • x ∈ D) →
      D = ⊥ ∨ D = ⊤ := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp : IsPGroup 7 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hfixed : FixedPoints.subgroup A E = ⊥ := by
    have hmod := hp.card_modEq_card_fixedPoints E
    change Nat.ModEq 7 (Nat.card E) (Nat.card (FixedPoints.subgroup A E)) at hmod
    have hbound := Subgroup.card_le_card_group (H := FixedPoints.subgroup A E)
    have hpos : 0 < Nat.card (FixedPoints.subgroup A E) := Nat.card_pos
    rw [hE] at hmod hbound
    change 1 = Nat.card (FixedPoints.subgroup A E) % 7 at hmod
    have hcases : Nat.card (FixedPoints.subgroup A E) = 1 ∨
        Nat.card (FixedPoints.subgroup A E) = 8 := by omega
    rcases hcases with h | h
    · exact Subgroup.card_eq_one.mp h
    · have htop : FixedPoints.subgroup A E = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (h.trans hE.symm)
      have hbot : A = ⊥ := by
        apply bot_unique
        intro a ha
        apply Subgroup.mem_bot.mpr
        apply MulEquiv.ext
        intro x
        have hx : x ∈ FixedPoints.subgroup A E := by rw [htop]; trivial
        exact hx ⟨a, ha⟩
      simp [hbot] at hA
  intro D hD
  let : IsInvariant A E D := ⟨by
    intro a x
    constructor
    · exact hD a x
    · intro hx
      simpa only [inv_smul_smul] using hD a⁻¹ (a • x) hx⟩
  have hfixedD : FixedPoints.subgroup A D = ⊥ := by
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply hfixed.le
    intro a
    exact congrArg Subtype.val (hx a)
  have hmod := hp.card_modEq_card_fixedPoints D
  change Nat.ModEq 7 (Nat.card D) (Nat.card (FixedPoints.subgroup A D)) at hmod
  rw [hfixedD, Subgroup.card_bot] at hmod
  have hbound := Subgroup.card_le_card_group (H := D)
  rw [hE] at hbound
  have hcases : Nat.card D = 1 ∨ Nat.card D = 8 := by
    change Nat.card D % 7 = 1 at hmod
    omega
  exact hcases.elim (fun h => Or.inl (Subgroup.card_eq_one.mp h))
    (fun h => Or.inr (Subgroup.eq_top_of_card_eq D (h.trans hE.symm)))

variable {G : Type*} [Group G] [Finite G]

/-- The order-21 image really is irreducible on the actual subgroup of order eight. -/
theorem invariant_subgroups_of_order_twentyOne {V X : Subgroup G}
    (hV : Nat.card V = 8) (himage : Nat.card (action V X).range = 21)
    (W : Subgroup G) (hWV : W ≤ V)
    (hW : actingGroup V X ≤ normalizer (W : Set G)) : W = ⊥ ∨ W = V := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let := Fintype.ofFinite (action V X).range
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (G := (action V X).range) 7
    (by rw [← Nat.card_eq_fintype_card, himage]; decide)
  let A := zpowers (a : MulAut V)
  have hA : Nat.card A = 7 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha]
  have hle : A ≤ (action V X).range := zpowers_le.mpr a.property
  have hd := invariant_subgroups_of_seven hV A hA (W.subgroupOf V) (by
    intro c v hv
    obtain ⟨m, hm⟩ := hle c.property
    change (c : MulAut V) v ∈ W.subgroupOf V
    rw [← hm]
    exact (mem_normalizer_iff.mp (hW m.property) (v : G)).mp hv)
  rcases hd with hd | hd
  · left
    have he := congrArg (map V.subtype) hd
    rwa [map_subgroupOf_eq_of_le hWV, Subgroup.map_bot] at he
  · right
    have he := congrArg (map V.subtype) hd
    rwa [map_subgroupOf_eq_of_le hWV, ← MonoidHom.range_eq_map, range_subtype] at he

/-- The nontrivial root subgroup in `X ∩ V` forces `V ≤ X` in alternative (iv). -/
theorem space_le_residual_of_order_twentyOne {V X Z : Subgroup G}
    (hV : Nat.card V = 8) (himage : Nat.card (action V X).range = 21)
    (hZ : Z ≠ ⊥) (hZV : Z ≤ V) (hZX : Z ≤ X) : V ≤ X :=
  space_le_residual_of_irreducible hZ hZV hZX
    (invariant_subgroups_of_order_twentyOne hV himage)

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
