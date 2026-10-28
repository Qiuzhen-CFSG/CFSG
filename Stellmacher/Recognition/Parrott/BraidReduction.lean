module

public import Stellmacher.Recognition.Parrott.BraidDihedral
public import Stellmacher.Recognition.Parrott.LocalGenerators

/-!
# The final reduction for Parrott's braid relation

For the actual compatible local generators, the displayed identity (*) and
its centralizing identity exclude order ten. The second-centralizer theorem
places r in O₂(C_G(ir)); adjoining the involution sdvzs to this normal two-group
is still a two-group. Its element sdvzsr therefore has two-power order.
Identity (*) makes its fourth power conjugate to (sr)⁴, which has order five
when rs has order ten. These orders are incompatible.

The final theorem combines this exclusion with the fourth-power conjugation
identity and the alternatives (rs)⁸=1 or (rs)¹⁰=1. Those word identities and
order alternatives remain explicit inputs here. The owning braid-relation task
must prove them and instantiate this reduction for the same compatible pair;
this module does not assert the unconditional braid relation.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§6, printed p.684, Verification of VI(i), especially equation (*).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottNormalizerGeneratorData
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
variable {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerGeneratorData f)

private theorem sqinv {H : Type*} [Group H] {a : H} (h : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

private theorem mul_core_two_power {H : Type*} [Group H] [Finite H]
    (a b : H) (ha : a ^ 2 = 1) (hb : b ∈ pCore 2 H) :
    ∃ m : ℕ, (a * b) ^ (2 ^ m) = 1 := by
  have hA : IsPGroup 2 (zpowers a) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_of_pow_eq_one ha
  let U := zpowers a ⊔ pCore 2 H
  have hU : IsPGroup 2 U := hA.to_sup_of_normal_right pCore_isPGroup
  let u : U := ⟨a * b, mul_mem_sup (mem_zpowers a) hb⟩
  obtain ⟨m, hm⟩ := hU u
  exact ⟨m, congrArg Subtype.val hm⟩

variable [Finite G]

/-- The two explicit source word identities exclude order ten, using the
actual second-centralizer core rather than an assumed two-element assertion. -/
public theorem braid_ten_impossible_of_word_identities
    (c : ParrottSecondCentralizerData n)
    (horder : orderOf (f.r * k.s) = 10)
    (hcentral : Commute (k.s * f.d * n.v * z * k.s) ((f.r * k.s) ^ 5 * f.r))
    (hstar : (k.s * f.d * n.v * z * k.s * f.r) ^ 4 =
      f.a * f.d * n.v * z * (k.s * f.r) ^ 4 * z * n.v * f.d * f.a) : False := by
  let q := (f.r * k.s) ^ 5 * f.r
  let H := centralizer ({q} : Set G)
  let a : H := ⟨k.s * f.d * n.v * z * k.s,
    mem_centralizer_singleton_iff.mpr hcentral.eq⟩
  let b : H := ⟨f.r, mem_centralizer_singleton_iff.mpr
    (k.braid_ten_reflection horder).2.2.eq⟩
  have hb : b ∈ pCore 2 H := by
    obtain ⟨b', hb', heq⟩ := k.braid_ten_core_mem c horder
    exact (Subtype.ext heq : b' = b) ▸ hb'
  have hD : (f.d * n.v * z) ^ 2 = 1 := by
    simpa only [Tits.parrottRelator, map_pow, FreeGroup.lift_apply_of, words,
      Tits.parrottRecognitionWords] using k.relators_except_braid .i_s8 (by decide)
  have ha : a ^ 2 = 1 := by
    apply Subtype.ext
    change (k.s * f.d * n.v * z * k.s) ^ 2 = 1
    have he := congrArg (MulAut.conj k.s) hD
    simpa only [map_pow, map_one, MulAut.conj_apply, sqinv k.s_sq, mul_assoc] using he
  obtain ⟨m, hm⟩ := mul_core_two_power a b ha hb
  have hmG : (k.s * f.d * n.v * z * k.s * f.r) ^ (2 ^ m) = 1 :=
    congrArg Subtype.val hm
  have hsmall := orderOf_dvd_of_pow_eq_one hmG
  have hpow := orderOf_pow_dvd (x := k.s * f.d * n.v * z * k.s * f.r) 4
  have hsrinv : k.s * f.r = (f.r * k.s)⁻¹ := by
    rw [mul_inv_rev, sqinv f.eq20_r, sqinv k.s_sq]
  have hsr4 : orderOf ((k.s * f.r) ^ 4) = 5 := by
    rw [orderOf_pow, hsrinv, orderOf_inv, horder]
    norm_num
  have hconj : (MulAut.conj (f.a * f.d * n.v * z)) ((k.s * f.r) ^ 4) =
      (k.s * f.d * n.v * z * k.s * f.r) ^ 4 := by
    rw [hstar]
    simp only [MulAut.conj_apply, mul_inv_rev, sqinv f.z_sq, sqinv f.v_sq,
      sqinv f.d_sq, sqinv f.a_sq, mul_assoc]
  have ho : orderOf ((k.s * f.d * n.v * z * k.s * f.r) ^ 4) = 5 := by
    rw [← hconj]
    exact ((MulAut.conj (f.a * f.d * n.v * z)).orderOf_eq _).trans hsr4
  rw [ho] at hpow
  have hd := (show Nat.Prime 5 by decide).dvd_of_dvd_pow (hpow.trans hsmall)
  norm_num at hd


/-- Assemble the braid relation once the source word identities and the
centralizer-based order alternatives have been established for this same pair. -/
public theorem braid_eighth_power_of_local_steps
    (h : ParrottCentralizerHypotheses z) (c : ParrottSecondCentralizerData n)
    (hfourth : (f.r * k.s) ^ 4 * f.y * (k.s * f.r) ^ 4 = f.r * f.y * f.r)
    (hcentral : (f.r * k.s) ^ 10 = 1 →
      Commute (k.s * f.d * n.v * z * k.s) ((f.r * k.s) ^ 5 * f.r))
    (hstar : (f.r * k.s) ^ 10 = 1 → (k.s * f.d * n.v * z * k.s * f.r) ^ 4 =
      f.a * f.d * n.v * z * (k.s * f.r) ^ 4 * z * n.v * f.d * f.a)
    (halt : (f.r * k.s) ^ 8 = 1 ∨ (f.r * k.s) ^ 10 = 1) :
    (f.r * k.s) ^ 8 = 1 := by
  rcases halt with h8 | h10
  · exact h8
  · exfalso
    have hlo := k.braid_order_ge_six_of_fourth_conjugation h hfourth
    have hd := orderOf_dvd_of_pow_eq_one h10
    have hhi := Nat.le_of_dvd (by decide : 0 < 10) hd
    have hn6 : orderOf (f.r * k.s) ≠ 6 := by intro he; norm_num [he] at hd
    have hn8 : orderOf (f.r * k.s) ≠ 8 := by intro he; norm_num [he] at hd
    have horder : orderOf (f.r * k.s) = 10 := by
      obtain ⟨m, hm⟩ := k.braid_order_even
      omega
    exact k.braid_ten_impossible_of_word_identities c horder (hcentral h10) (hstar h10)

end Stellmacher.Recognition.ParrottNormalizerGeneratorData
