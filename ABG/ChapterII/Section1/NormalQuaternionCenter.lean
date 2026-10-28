module

public import ABG.ChapterII.Section1.WreathedDefs
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.LinearCombination

/-!
# Central intersection of a normal quaternion subgroup

A normal generalized quaternion subgroup Q of any group S meets the center
of S in precisely its own center, of order two. No finiteness or two-group
assumption on S is required. This supplies the central-intersection step in
ABG Chapter II, Section 3, Proposition 2 (article p.22): its subgroup Q is
normal in the Sylow group S, which suffices for the argument.

The reusable model-center cardinality theorem is also public. In the concrete
quaternion model, commutation with the two standard generators
leaves just the identity and the halfway power of the cyclic generator.
Transporting this computation gives a characteristic subgroup of Q of order
two. Its image is normal in S, so conjugation fixes its unique nonidentity
element and the image is central in S. The reverse inclusion follows by
restricting ambient centrality to Q.
-/

/-- A generalized quaternion model of parameter at least two has center of order two. -/
public theorem QuaternionGroup.card_center_of_two_le (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (Subgroup.center (QuaternionGroup m)) = 2 := by
  let : NeZero m := ⟨by omega⟩
  let t : QuaternionGroup m := QuaternionGroup.a m
  have htm : (m : ZMod (2 * m)) + m = 0 := by
    simpa [two_mul, Nat.cast_add] using ZMod.natCast_self (2 * m)
  have ht : t ∈ Subgroup.center (QuaternionGroup m) := by
    apply Subgroup.mem_center_iff.mpr
    rintro (i | i)
    · simp only [t, QuaternionGroup.a_mul_a, add_comm]
    · simp only [t, QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
      congr 1
      linear_combination htm
  apply (Nat.card_eq_two_iff' (1 : Subgroup.center (QuaternionGroup m))).mpr
  refine ⟨⟨t, ht⟩, ?_, ?_⟩
  · intro h
    have hz := QuaternionGroup.a.inj (congrArg Subtype.val h)
    have hv := congrArg ZMod.val hz
    simp only [ZMod.val_natCast, ZMod.val_zero,
      Nat.mod_eq_of_lt (by omega : m < 2 * m)] at hv
    omega
  · rintro ⟨q, hq⟩ hqne
    apply Subtype.ext
    cases q with
    | a i =>
      have hi0 : i ≠ 0 := by
        intro hi
        apply hqne
        apply Subtype.ext
        simp [hi]
      let : NeZero i := ⟨hi0⟩
      have hcomm := Subgroup.mem_center_iff.mp hq (QuaternionGroup.xa 0)
      have hi : i = -i := by simpa using hcomm
      have hiv := congrArg ZMod.val hi
      rw [ZMod.val_neg_of_ne_zero] at hiv
      have hil := ZMod.val_lt i
      have hivm : i.val = m := by omega
      change QuaternionGroup.a i = QuaternionGroup.a (m : ZMod (2 * m))
      congr 1
      apply ZMod.val_injective
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : m < 2 * m)] using hivm
    | xa i =>
      have hcomm := Subgroup.mem_center_iff.mp hq (QuaternionGroup.a 1)
      have hi : i - 1 = i + 1 := QuaternionGroup.xa.inj hcomm
      have htwo : (2 : ZMod (2 * m)) = 0 := by linear_combination -hi
      have hv := congrArg ZMod.val htwo
      have hval : ZMod.val (2 : ZMod (2 * m)) = 2 :=
        ZMod.val_natCast_of_lt (by omega : 2 < 2 * m)
      rw [hval, ZMod.val_zero] at hv
      omega

namespace ABG

/-- Normal generalized quaternion subgroups have central intersection of order two. -/
public theorem normal_quaternion_inf_center_card {S : Type*} [Group S]
    (Q : Subgroup S) [Q.Normal] (hQ : IsGeneralizedQuaternionGroup Q) :
    Nat.card (Q ⊓ Subgroup.center S : Subgroup S) = 2 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hQ
  have hZQ : Nat.card (Subgroup.center Q) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact QuaternionGroup.card_center_of_two_le (2 ^ n)
      (by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn)
  let Z : Subgroup S := (Subgroup.center Q).map Q.subtype
  have hZcard : Nat.card Z = 2 :=
    (Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)).trans hZQ
  have hZN : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZle : Z ≤ Subgroup.center S := by
    obtain ⟨z, hzne, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZcard
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro g
    by_cases hxone : x = 1
    · simp [hxone]
    let xZ : Z := ⟨x, hx⟩
    let yZ : Z := ⟨g * x * g⁻¹, hZN.conj_mem x hx g⟩
    have hyne : yZ ≠ 1 := by
      intro hy
      have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
      apply hxone
      have h := congrArg (fun a : S => g⁻¹ * a * g) hy'
      simpa [mul_assoc] using h
    have heq : yZ = xZ := (hzuniq yZ hyne).trans (hzuniq xZ (by
      intro hx'
      exact hxone (congrArg Subtype.val hx'))).symm
    have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
    have h := congrArg (fun a : S => a * g) heq'
    simpa [mul_assoc] using h
  have hEq : Q ⊓ Subgroup.center S = Z := by
    apply le_antisymm
    · intro x hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro q
      exact Subtype.ext (Subgroup.mem_center_iff.mp hx.2 q)
    · exact le_inf (Subgroup.map_subtype_le _) hZle
  rw [hEq]
  exact hZcard

end ABG
