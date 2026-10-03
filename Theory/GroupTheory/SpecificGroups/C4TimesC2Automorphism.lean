module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# An automorphism bound for C₄ × C₂

An automorphism is determined by the images of the two standard generators.
The long generator has order four; the short generator is an involution
outside its cyclic subgroup. There are eight possible ordered image pairs,
as checked by finite enumeration. Thus the automorphism group has order at
most eight.

This elementary count excludes self-centralizing normal bases of this type
in groups of order 128, in the Hall–Janko branch of Janko–Thompson,
Math. Z. 113 (1970), Theorem 1.3(a), printed p.386.
-/

namespace C4TimesC2Automorphism
public abbrev Model := Multiplicative (ZMod 4) × Multiplicative (ZMod 2)
private def Good (v : Model × Model) : Prop :=
  v.1 ^ 2 ≠ 1 ∧ v.2 ^ 2 = 1 ∧ v.2 ≠ 1 ∧ v.2 ≠ v.1 ^ 2
private instance (v : Model × Model) : Decidable (Good v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
private def x : Model := (Multiplicative.ofAdd 1, 1)
private def y : Model := (1, Multiplicative.ofAdd 1)
private theorem good_xy : Good (x,y) := by decide
private theorem gen : ∀ z : Model, ∃ i : Fin 4, ∃ j : Fin 2, z = x ^ i.val * y ^ j.val := by decide
private theorem count : Nat.card {v : Model × Model // Good v} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

private def eval (f : MulAut Model) : {v : Model × Model // Good v} :=
  ⟨(f x, f y), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      apply good_xy.1
      apply f.injective
      simpa only [map_pow, map_one] using h
    · rw [← map_pow, good_xy.2.1, map_one]
    · intro h
      apply good_xy.2.2.1
      apply f.injective
      simpa only [map_one] using h
    · simpa only [← map_pow, f.injective.ne_iff] using good_xy.2.2.2⟩
private theorem inj : Function.Injective eval := by
  intro f g h
  have hh := congrArg Subtype.val h
  have hx : f x = g x := congrArg Prod.fst hh
  have hy : f y = g y := congrArg Prod.snd hh
  apply MulEquiv.ext
  intro z
  obtain ⟨i,j,rfl⟩ := gen z
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, hx, hy]
/-- The automorphism group of `C₄ × C₂` has order at most eight. -/
public theorem card_mulAut_le_eight : Nat.card (MulAut Model) ≤ 8 :=
  (Nat.card_le_card_of_injective eval inj).trans_eq count
end C4TimesC2Automorphism
