module
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.PairAction.WordOrder
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.PairAction.CenterImage.Action

/-!
# The actual center-action image of Held's pure pair

The literal pair product B acts on the center of its normal word subgroup
of order 256. Four explicit central words yield sixteen distinct binary
products. The Action certificates show how four original pair generators
act on them. Their 36 mixed-radix words give distinct elements of the actual
action image. The independent upper bound of 36 makes these words exhaustive,
without identifying the whole center or assuming the word subgroup is O₂(B).

These coordinates will identify this actual image with S₃ × S₃. Source context:
Aschbacher--Smith 2.3.9(7), printed p.526, and 15.3.41–42, printed p.1138;
GLS3 Table 5.3p and the unchanged ATLAS Held pair (false,0).

Extracted from `CFSG/Quasithin/Chapter15/Section03/ComponentUniqueness/RankTwo/NonCharacteristicTwo/SporadicSieve/HeldExclusion/ProperExtensionProfile/Quotients/PureInnerCore/CenterImage.lean`, preserving the literal words,
permutation tables and conjugation convention. Original ATLAS attribution and
license remain in `Theory/SpecificGroups/Held/Model/Source`.

-/

set_option Elab.async false
@[expose] public section
open Subgroup
namespace Held.AutomorphismLocalPair.ResidualNine.PairActionCertificate
namespace CenterImageCertificate

def Compatible (a : MulAut (center pureWordCore)) (p : Equiv.Perm (Fin 16)) : Prop :=
  ∀ v, a (centralWord v) = centralWord (p v)

theorem Compatible.one : Compatible 1 1 := fun _ => rfl

theorem Compatible.mul {a b : MulAut (center pureWordCore)}
    {p q : Equiv.Perm (Fin 16)} (ha : Compatible a p) (hb : Compatible b q) :
    Compatible (a * b) (p * q) := by
  intro v
  change a (b (centralWord v)) = centralWord (p (q v))
  rw [hb, ha]

theorem Compatible.inv {a : MulAut (center pureWordCore)}
    {p : Equiv.Perm (Fin 16)} (ha : Compatible a p) : Compatible a⁻¹ p⁻¹ := by
  intro v
  apply a.injective
  change a (a.symm (centralWord v)) = a (centralWord (p.symm v))
  rw [a.apply_symm_apply, ha, p.apply_symm_apply]

theorem Compatible.pow {a : MulAut (center pureWordCore)}
    {p : Equiv.Perm (Fin 16)} (ha : Compatible a p) (n : ℕ) :
    Compatible (a ^ n) (p ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using Compatible.one
  | succ n ih => simpa only [pow_succ] using ih.mul ha

theorem Compatible.eq_one {a : MulAut (center pureWordCore)}
    {p : Equiv.Perm (Fin 16)} (ha : Compatible a p) (h : a = 1) : p = 1 := by
  apply Equiv.ext
  intro v
  apply centralWord_injective
  simpa only [h, MulAut.one_apply, Equiv.Perm.one_apply] using (ha v).symm

def actualGenerator (k : Fin 4) : pureCenterAction.range :=
  pureCenterAction.rangeRestrict (actor k)

def actualWord (v : Fin 36) : pureCenterAction.range := word v actualGenerator

theorem generator_compatible (k : Fin 4) :
    Compatible (actualGenerator k) (smallGenerator k) := generator_action k

theorem word_compatible (v : Fin 36) :
    Compatible (actualWord v) (smallWord v) := by
  exact (((generator_compatible 0).pow _ |>.mul ((generator_compatible 1).pow _)).mul
    ((generator_compatible 2).pow _)).mul ((generator_compatible 3).pow _)

theorem actualWord_injective : Function.Injective actualWord := by
  intro v w h
  apply smallWord_injective
  apply Equiv.ext
  intro x
  apply centralWord_injective
  rw [← word_compatible v x, ← word_compatible w x, h]

theorem actualWord_zero : actualWord 0 = 1 := by
  simp [actualWord, word]

end CenterImageCertificate
open CenterImageCertificate

/-- The literal conjugation image on the center has order 36. -/
theorem pureCenterAction_range_card : Nat.card pureCenterAction.range = 36 := by
  apply Nat.le_antisymm pureCenterAction_range_card_le
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective _ actualWord_injective

namespace CenterImageCertificate

theorem actualWord_surjective : Function.Surjective actualWord := by
  apply (Nat.bijective_iff_injective_and_card actualWord).mpr
    ⟨actualWord_injective, by rw [Nat.card_fin, pureCenterAction_range_card]⟩ |>.surjective

end CenterImageCertificate
end Held.AutomorphismLocalPair.ResidualNine.PairActionCertificate
