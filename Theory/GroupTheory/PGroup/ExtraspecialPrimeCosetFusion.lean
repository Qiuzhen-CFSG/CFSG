module

public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms


/-!
# Inner fusion in noncentral cosets of extraspecial groups

Commutation with a noncentral element is a nontrivial homomorphism to the
center. Since the center has prime order, this homomorphism is surjective.
It adjusts any representative within its central coset by inner conjugation.

This supplies the element-fusion step in Aschbacher, *Sporadic Groups*
(1994), 47.3(3)–(4), printed p.262; the application retains the normalizer's
actual action on the intrinsic Frattini quotient.
-/

public section

open Subgroup
open scoped commutatorElement
namespace IsExtraspecial
variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P] [IsExtraspecial p P]
include p

private theorem commutator_central (a b : P) : ⁅a, b⁆ ∈ center P := by
  rw [← commutator_eq_center (p := p)]
  exact commutator_mem_commutator (mem_top _) (mem_top _)

/-- A noncentral central coset of an extraspecial group is one inner conjugacy class. -/
theorem isConj_of_center_quotient_eq_prime {x y : P} (hx : x ∉ center P)
    (hxy : QuotientGroup.mk' (center P) x = QuotientGroup.mk' (center P) y) :
    IsConj x y := by
  let f : P →* center P := {
    toFun a := ⟨⁅a, x⁆, commutator_central (p := p) a x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' a b := by
      apply Subtype.ext
      change ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        mem_center_iff.mp (commutator_central (p := p) b x) a,
        mul_inv_cancel_right]
      exact mem_center_iff.mp (commutator_central (p := p) a x) ⁅b, x⁆ }
  have hne : f.range ≠ ⊥ := by
    intro hf
    apply hx
    apply mem_center_iff.mpr
    intro a
    have ha : f a ∈ (⊥ : Subgroup (center P)) := hf ▸ (show f a ∈ f.range from ⟨a, rfl⟩)
    have h1 := congrArg Subtype.val (mem_bot.mp ha)
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  let : Fact (Nat.Prime (Nat.card (center P))) :=
    ⟨by rw [center_order_p p P]; exact Fact.out⟩
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp
    (f.range.eq_bot_or_eq_top_of_prime_card.resolve_left hne)
  have hd : y / x ∈ center P := QuotientGroup.eq_iff_div_mem.mp hxy.symm
  obtain ⟨a, ha⟩ := hf ⟨y / x, hd⟩
  have he : ⁅a, x⁆ = y / x := congrArg Subtype.val ha
  exact isConj_iff.mpr ⟨a, by
    calc
      a * x * a⁻¹ = ⁅a, x⁆ * x := by group
      _ = y := by rw [he, div_eq_mul_inv, inv_mul_cancel_right]⟩

end IsExtraspecial
