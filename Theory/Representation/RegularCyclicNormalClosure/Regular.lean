module

public import Theory.Representation.RegularCyclicNormalClosure.Basic
public import Mathlib.FieldTheory.Finiteness

/-!
# Consequences of a regular cyclic action

A nonidentity element of the regular actor fixes no nonzero vector in its
moved space. Splitting off the fixed space shows that every such element
has the same fixed space as the whole actor. An orbit bijection gives
|C| = 2^d - 1, where d is the moved dimension; in particular C has odd
order, and order three forces d = 2.

These are consequences of the published input for the regular cyclic
normal-closure problem, not a proof of the nonnormal case of that theorem.
Source: the regular-action setup in Aschbacher–Smith E.6.24, printed p.255
(PDF p.266), and GLS, volume 2, C.14, equations (14.2)–(14.3).
-/

public section

open Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

private theorem action_injective (a : A) : Function.Injective (ρ a) := by
  intro v w he
  have := congrArg (ρ a⁻¹) he
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] using this

private theorem moved_mem_action (c : C) {v : W} (hv : v ∈ displacementSpan ρ C ⊤) :
    ρ c v ∈ displacementSpan ρ C ⊤ := by
  have hm := Submodule.mem_map_of_mem (f := ρ c) hv
  rwa [displacementSpan_map_of_normalized ρ C c
    (mem_normalizer_iff_map_conj_eq.mp (le_normalizer c.property))] at hm

/-- Every nonidentity element of the regular cyclic subgroup has no nonzero
fixed vector in its moved space. -/
theorem Input.eq_zero_of_mem_moved_of_fixed (h : Input ρ C) {c : C} (hc : c ≠ 1)
    {v : W} (hv : v ∈ displacementSpan ρ C ⊤) (hfix : ρ c v = v) : v = 0 := by
  by_contra hne
  obtain ⟨x, hx, huniq⟩ := h.regular v hv hne v hv hne
  have h1 : ρ (1 : C) v = v := by simp
  exact hc ((huniq c hfix).trans (huniq 1 h1).symm)

/-- All nonidentity cyclic subgroups of C have the same fixed space as C. -/
theorem Input.fixedSpace_zpowers (h : Input ρ C) {c : A} (hc : c ∈ C) (hne : c ≠ 1) :
    fixedSpace ρ (zpowers c) = fixedSpace ρ C := by
  apply le_antisymm
  · intro v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ fixedSpace ρ C ⊔ displacementSpan ρ C ⊤ by
        rw [h.split.sup_eq_top]; trivial)
    have hfix : ρ c w = w := by
      have hf := hv ⟨c, mem_zpowers c⟩
      change ρ c (u + w) = u + w at hf
      rwa [map_add, (show ρ c u = u from hu ⟨c, hc⟩), add_right_inj] at hf
    have hw0 := h.eq_zero_of_mem_moved_of_fixed
      (c := ⟨c, hc⟩) (fun he => hne (congrArg Subtype.val he)) hw hfix
    simpa only [hw0, add_zero] using hu
  · intro v hv a
    exact hv ⟨a, (zpowers_le.mpr hc) a.property⟩

/-- Regularity identifies the order of C with the number of nonzero moved vectors. -/
theorem Input.card_eq [Finite W] (h : Input ρ C) :
    Nat.card C = 2 ^ Module.finrank (ZMod 2) (displacementSpan ρ C ⊤) - 1 := by
  classical
  let D := displacementSpan ρ C ⊤
  let : Nontrivial D := Module.nontrivial_of_finrank_pos (R := ZMod 2)
    (lt_trans Nat.zero_lt_one h.moved_dimension_gt_one)
  obtain ⟨v, hv⟩ := exists_ne (0 : D)
  have hv0 : (v : W) ≠ 0 := fun he => hv (Subtype.ext he)
  let f : C → {w : D // w ≠ 0} := fun c =>
    ⟨⟨ρ c v, moved_mem_action c v.property⟩, fun he =>
      hv0 (action_injective (ρ := ρ) (c : A) (by simpa using congrArg (fun w : D => (w : W)) he))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c d he
      have hf' : ρ c v = ρ d v := congrArg (fun w : {w : D // w ≠ 0} => (w.val : W)) he
      obtain ⟨x, hx, hu⟩ := h.regular v v.property hv0 (ρ d v)
        (moved_mem_action d v.property)
        (fun hd => hv0 (action_injective (ρ := ρ) (d : A) (by simpa using hd)))
      exact (hu c hf').trans (hu d rfl).symm
    · intro w
      obtain ⟨c, hc, _⟩ := h.regular v v.property hv0 w.val w.val.property
        (fun he => w.property (Subtype.ext he))
      exact ⟨c, Subtype.ext (Subtype.ext hc)⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  let := Fintype.ofFinite D
  let := Fintype.ofFinite {w : D // w ≠ 0}
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- The cyclic subgroup has odd order, as required in the source's regular-action setup. -/
theorem Input.odd_card [Finite W] (h : Input ρ C) : Odd (Nat.card C) := by
  rw [h.card_eq]
  have he : Even (2 ^ Module.finrank (ZMod 2) (displacementSpan ρ C ⊤)) :=
    even_two.pow_of_ne_zero (by have := h.moved_dimension_gt_one; omega)
  exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide)) he odd_one

/-- The exceptional order-three case has moved dimension two. -/
theorem Input.moved_finrank_eq_two_of_card_three [Finite W]
    (h : Input ρ C) (hc : Nat.card C = 3) :
    Module.finrank (ZMod 2) (displacementSpan ρ C ⊤) = 2 := by
  have he := h.card_eq
  have hp : 0 < 2 ^ Module.finrank (ZMod 2) (displacementSpan ρ C ⊤) := pow_pos (by decide) _
  have hpow : 2 ^ Module.finrank (ZMod 2) (displacementSpan ρ C ⊤) = 2 ^ 2 := by omega
  exact (Nat.pow_right_injective (by decide : 1 < 2)) hpow

end Representation.RegularCyclicNormalClosure
