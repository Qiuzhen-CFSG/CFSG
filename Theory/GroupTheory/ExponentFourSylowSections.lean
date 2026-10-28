module

public import Theory.GroupTheory.DihedralEightSections
public import Mathlib.Data.ZMod.Basic

/-!
# Exponent bounds on Sylow subgroups of sections

A Sylow subgroup of a quotient of a subgroup lifts to a Sylow of that
subgroup, which embeds into an ambient Sylow. A power identity therefore
passes from the ambient Sylow to every Sylow of the section. In particular,
a C₂ × D₈ Sylow excludes order-eight elements in all section Sylows, and
its order sixteen excludes a factor thirty-two in section orders.

These literal-map obstructions are used for the sporadic component cases
of Aschbacher--Smith F.6.18, printed p.310.
-/

public section
noncomputable section
open Subgroup
namespace Theory.GroupTheory

/-- Power identities of Sylow two-subgroups pass to actual subgroup quotients. -/
theorem sylow_pow_eq_one_of_section
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (T : Sylow 2 G) (n : ℕ) (hpow : ∀ t : T, t ^ n = 1)
    (K : Subgroup G) (f : K →* H) (hf : Function.Surjective f)
    (P : Sylow 2 H) (p : P) : p ^ n = 1 := by
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hf 2 P
  let eQ : ((S : Subgroup K).map f) ≃* P :=
    MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup hS)
  let q : S →* P := eQ.toMonoidHom.comp (f.subgroupMap (S : Subgroup K))
  have hq : Function.Surjective q :=
    eQ.surjective.comp (f.subgroupMap_surjective (S : Subgroup K))
  obtain ⟨U, hU⟩ := (S.isPGroup'.map K.subtype).exists_le_sylow
  let i : S →* U := (Subgroup.inclusion hU).comp
    (K.subtype.subgroupMap (S : Subgroup K))
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : U => (u : G)) h
  let e : U ≃* T := U.equiv T
  obtain ⟨s, rfl⟩ := hq p
  have hs : s ^ n = 1 := by
    apply hi
    apply e.injective
    simpa only [map_pow, map_one] using hpow (e (i s))
  rw [← map_pow, hs, map_one]

/-- The split group of order sixteen has exponent four. -/
theorem split_sixteen_pow_four
    (t : Multiplicative (ZMod 2) × DihedralGroup 4) : t ^ 4 = 1 := by
  revert t
  decide +kernel

/-- Its order is exactly sixteen. -/
theorem split_sixteen_card :
    Nat.card (Multiplicative (ZMod 2) × DihedralGroup 4) = 16 := by
  rw [Nat.card_prod, DihedralGroup.nat_card]
  norm_num [Nat.card_eq_fintype_card]

/-- Section Sylows beneath C₂ × D₈ satisfy the same fourth-power identity. -/
theorem split_sixteen_sylow_section_pow_four
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) (f : K →* H) (hf : Function.Surjective f)
    (P : Sylow 2 H) (p : P) : p ^ 4 = 1 := by
  apply sylow_pow_eq_one_of_section T 4 _ K f hf P p
  intro t
  apply eT.injective
  simpa only [map_pow, map_one] using split_sixteen_pow_four (eT t)

/-- A section under a Sylow of order at most sixteen has no thirty-two factor. -/
theorem not_thirty_two_dvd_card_section_of_sylow_le_sixteen
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (T : Sylow 2 G) (hT : Nat.card T ≤ 16)
    (K : Subgroup G) (f : K →* H) (hf : Function.Surjective f) :
    ¬ 32 ∣ Nat.card H := by
  intro hd
  let P : Sylow 2 H := default
  have hdiv := P.pow_dvd_card_of_pow_dvd_card (n := 5) hd
  have hlarge : 32 ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos hdiv
  have hsmall := sylow_card_section_le T K f hf P
  omega

end Theory.GroupTheory
