module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients.PureInnerCore.WordOrder
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients.PureInnerCore.CenterImage.Action

/-!
# The order and two-core of Held's pure center-action image

The literal pair product B acts on the center of its normal word subgroup
of order 256. Four explicit central words yield sixteen distinct binary
products, and the action of four original pair generators on these products
is certified in Action. Their 36 mixed-radix words give distinct elements
of the actual action image. The existing upper bound of 36 makes these
words exhaustive, without identifying the whole center or assuming the
word subgroup is O₂(B).

Every element of the image's two-core has fourth power one: the image has
order 36 and ninth powers are injective in a two-group. Normality puts
w(rwr⁻¹) in the same core for each of the two odd generators r. The small
permutation certificate proves that only the identity representative passes
all three fourth-power tests. Thus the two-core of the actual image is trivial.

These are the two concrete inputs to the intrinsic pure-core calculation
used for Aschbacher--Smith 15.3.41–42 (printed p.1138), with model data from
GLS3 Table 5.3p and the unchanged ATLAS Held pair (false,0).
-/

set_option Elab.async false
public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
namespace CenterImageCertificate

private def Compatible (a : MulAut (center pureWordCore)) (p : Equiv.Perm (Fin 16)) : Prop :=
  ∀ v, a (centralWord v) = centralWord (p v)

private theorem Compatible.one : Compatible 1 1 := fun _ => rfl

private theorem Compatible.mul {a b : MulAut (center pureWordCore)}
    {p q : Equiv.Perm (Fin 16)} (ha : Compatible a p) (hb : Compatible b q) :
    Compatible (a * b) (p * q) := by
  intro v
  change a (b (centralWord v)) = centralWord (p (q v))
  rw [hb, ha]

private theorem Compatible.inv {a : MulAut (center pureWordCore)}
    {p : Equiv.Perm (Fin 16)} (ha : Compatible a p) : Compatible a⁻¹ p⁻¹ := by
  intro v
  apply a.injective
  change a (a.symm (centralWord v)) = a (centralWord (p.symm v))
  rw [a.apply_symm_apply, ha, p.apply_symm_apply]

private theorem Compatible.pow {a : MulAut (center pureWordCore)}
    {p : Equiv.Perm (Fin 16)} (ha : Compatible a p) (n : ℕ) :
    Compatible (a ^ n) (p ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using Compatible.one
  | succ n ih => simpa only [pow_succ] using ih.mul ha

private theorem Compatible.eq_one {a : MulAut (center pureWordCore)}
    {p : Equiv.Perm (Fin 16)} (ha : Compatible a p) (h : a = 1) : p = 1 := by
  apply Equiv.ext
  intro v
  apply centralWord_injective
  simpa only [h, MulAut.one_apply, Equiv.Perm.one_apply] using (ha v).symm

private def actualGenerator (k : Fin 4) : pureCenterAction.range :=
  pureCenterAction.rangeRestrict (actor k)

private def actualWord (v : Fin 36) : pureCenterAction.range := word v actualGenerator

private theorem generator_compatible (k : Fin 4) :
    Compatible (actualGenerator k) (smallGenerator k) := generator_action k

private theorem word_compatible (v : Fin 36) :
    Compatible (actualWord v) (smallWord v) := by
  exact (((generator_compatible 0).pow _ |>.mul ((generator_compatible 1).pow _)).mul
    ((generator_compatible 2).pow _)).mul ((generator_compatible 3).pow _)

private theorem actualWord_injective : Function.Injective actualWord := by
  intro v w h
  apply smallWord_injective
  apply Equiv.ext
  intro x
  apply centralWord_injective
  rw [← word_compatible v x, ← word_compatible w x, h]

private theorem actualWord_zero : actualWord 0 = 1 := by
  simp [actualWord, word]

end CenterImageCertificate
open CenterImageCertificate

/-- The literal conjugation image on the center has order 36. -/
theorem pureCenterAction_range_card : Nat.card pureCenterAction.range = 36 := by
  apply Nat.le_antisymm pureCenterAction_range_card_le
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective _ actualWord_injective

namespace CenterImageCertificate

private theorem actualWord_surjective : Function.Surjective actualWord := by
  apply (Nat.bijective_iff_injective_and_card actualWord).mpr
    ⟨actualWord_injective, by rw [Nat.card_fin, pureCenterAction_range_card]⟩ |>.surjective

private theorem core_fourth {x : pureCenterAction.range}
    (hx : x ∈ pCore 2 pureCenterAction.range) : x ^ 4 = 1 := by
  let y : pCore 2 pureCenterAction.range := ⟨x, hx⟩
  have h36 : x ^ 36 = 1 := by
    simpa only [pureCenterAction_range_card] using (pow_card_eq_one' (x := x))
  have hy : (y ^ 4) ^ 9 = (1 : pCore 2 pureCenterAction.range) ^ 9 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, one_pow, ← pow_mul] using h36
  have h := (pCore_isPGroup (p := 2) (G := pureCenterAction.range)).powEquiv
    (by decide : Nat.Coprime 2 9) |>.injective hy
  exact congrArg Subtype.val h

private theorem test_mem {x : pureCenterAction.range}
    (hx : x ∈ pCore 2 pureCenterAction.range) (r : pureCenterAction.range) :
    x * r * x * r⁻¹ ∈ pCore 2 pureCenterAction.range := by
  rw [mul_assoc x r x, mul_assoc x (r * x) r⁻¹]
  exact (pCore 2 pureCenterAction.range).mul_mem hx
    ((inferInstance : (pCore 2 pureCenterAction.range).Normal).conj_mem x hx r)

end CenterImageCertificate

/-- The actual range of the canonical center action has trivial two-core. -/
theorem pureCenterAction_range_twoCore : pCore 2 pureCenterAction.range = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨v, rfl⟩ := actualWord_surjective x
  have h4 : smallWord v ^ 4 = 1 :=
    ((word_compatible v).pow 4).eq_one (congrArg Subtype.val (core_fourth hx))
  have ht (k : Fin 4) :
      (smallWord v * smallGenerator k * smallWord v * (smallGenerator k)⁻¹) ^ 4 = 1 := by
    apply (((((word_compatible v).mul (generator_compatible k)).mul
      (word_compatible v)).mul (generator_compatible k).inv).pow 4).eq_one
    exact congrArg Subtype.val (core_fourth (test_mem hx (actualGenerator k)))
  have hv := fourth_power_test v h4 (ht 0) (ht 1)
  rw [hv, actualWord_zero]
  exact one_mem _

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
