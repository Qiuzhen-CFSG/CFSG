module
public import Theory.GroupTheory.SemidihedralCenter
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# An order-four separating character of a semidihedral group

For the explicit semidihedral presentation of order `2^n`, with `n ≥ 4`,
`exists_order_four_character` constructs a character to the multiplicative
group of `ZMod 2`. It kills every element whose square is one, and every
order-four element in its kernel is conjugate to `a^(2^(n-3))`. The same
theorem verifies that `a*b` has order four. This is the internal character
input to the order-four transfer argument; no ambient fusion or
classification assumptions occur in this module.

The character is the parity of the cyclic exponent in the normal forms
`a^index` and `a^index*b` supplied by `Semidihedral.normal_form`.
Noncommutation separates the forms, and equality of cyclic powers determines
parity because the cyclic order is even. The odd conjugation exponent then
makes parity additive under multiplication. Writing `scale = 2^(n-4)`, the
outer square is `a^(4*scale*index)`. Consequently all involutions have even
exponent, while outer kernel elements have square one and cannot have order
four. The remaining cyclic order-four powers are the quarter-order rotation
and its inverse; conjugation by `b` interchanges them.

Source: Alperin–Brauer–Gorenstein, presentation on printed p.2 and Chapter II,
§1, Lemma 1(i), (iii), (vi), printed p.9, in
`refs/files/alperin-brauer-gorenstein.pdf`. The elementary square and cyclic
classification calculations follow the existing ABG presentation proofs,
but the complete import chain here stays below the campaign layer. The
cardinality and finiteness hypotheses are retained in the requested public
interface; the explicit presentation already suffices for this calculation.
-/

namespace Semidihedral
variable {G : Type*} [Group G]

private theorem exists_parity_character (a b : G) (modulus exponent : ℕ)
    (heven : 2 ∣ modulus) (ha : orderOf a = modulus)
    (hbb : b * b = 1) (hconj : b * a * b⁻¹ = a ^ exponent)
    (hodd : (exponent : ZMod 2) = 1) (hnc : ¬ Commute a b)
    (hnf : ∀ x : G, ∃ index : ℕ, x = a ^ index ∨ x = a ^ index * b) :
    ∃ character : G →* Multiplicative (ZMod 2),
      ∀ index : ℕ, character (a ^ index) = Multiplicative.ofAdd (index : ZMod 2) ∧
        character (a ^ index * b) = Multiplicative.ofAdd (index : ZMod 2) := by
  classical
  have hsep (left right : ℕ) : a ^ left ≠ a ^ right * b := by
    intro heq
    apply hnc
    have hc : Commute a (a ^ right * b) := heq ▸ Commute.self_pow a left
    apply mul_left_cancel (a := a ^ right)
    calc
      a ^ right * (a * b) = a * (a ^ right * b) := by
        rw [← mul_assoc, (Commute.self_pow a right).symm.eq, mul_assoc]
      _ = (a ^ right * b) * a := hc.eq
      _ = a ^ right * (b * a) := mul_assoc _ _ _
  have hcast (left right : ℕ) (heq : a ^ left = a ^ right) :
      (left : ZMod 2) = (right : ZMod 2) := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    apply Nat.ModEq.of_dvd heven
    simpa only [ha] using pow_eq_pow_iff_modEq.mp heq
  let value : G → ZMod 2 := fun x => (hnf x).choose
  have hvalue (x : G) (index : ℕ) (hx : x = a ^ index ∨ x = a ^ index * b) :
      value x = (index : ZMod 2) := by
    rcases (hnf x).choose_spec with hchosen | hchosen <;> rcases hx with hx | hx
    · exact hcast _ _ (hchosen.symm.trans hx)
    · exact (hsep _ _ (hchosen.symm.trans hx)).elim
    · exact (hsep _ _ (hx.symm.trans hchosen)).elim
    · exact hcast _ _ (mul_right_cancel (hchosen.symm.trans hx))
  have hp (index : ℕ) : value (a ^ index) = (index : ZMod 2) :=
    hvalue _ _ (Or.inl rfl)
  have ho (index : ℕ) : value (a ^ index * b) = (index : ZMod 2) :=
    hvalue _ _ (Or.inr rfl)
  have hmul (left right : G) : value (left * right) = value left + value right := by
    obtain ⟨first, rfl | rfl⟩ := hnf left
    · obtain ⟨second, rfl | rfl⟩ := hnf right
      · rw [← pow_add, hp, hp, hp, Nat.cast_add]
      · rw [← mul_assoc, ← pow_add, ho, hp, ho, Nat.cast_add]
    · obtain ⟨second, rfl | rfl⟩ := hnf right
      · rw [mul_assoc, move_pow a b exponent hconj second, ← mul_assoc, ← pow_add,
          ho, ho, hp, Nat.cast_add, Nat.cast_mul, hodd, one_mul]
      · have heq : (a ^ first * b) * (a ^ second * b) =
            a ^ (first + exponent * second) := by
          rw [mul_assoc, ← mul_assoc b, move_pow a b exponent hconj second,
            mul_assoc _ b b, hbb, mul_one, ← pow_add]
        rw [heq, hp, ho, ho, Nat.cast_add, Nat.cast_mul, hodd, one_mul]
  let character : G →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (value x)
      map_one' := by
        change value 1 = 0
        simpa only [pow_zero, Nat.cast_zero] using hp 0
      map_mul' := fun left right => congrArg Multiplicative.ofAdd (hmul left right) }
  exact ⟨character, fun index => ⟨congrArg Multiplicative.ofAdd (hp index),
    congrArg Multiplicative.ofAdd (ho index)⟩⟩

private theorem cyclic_four_isConj (a b : G) (scale index : ℕ) (hscale : 0 < scale)
    (ha : orderOf a = 8 * scale) (hconj : b * a * b⁻¹ = a ^ (4 * scale - 1))
    (hindex : index < 8 * scale) (hfour : orderOf (a ^ index) = 4) :
    IsConj (a ^ index) (a ^ (2 * scale)) := by
  have hdiv : 4 * (2 * scale) ∣ 4 * index := by
    rw [show 4 * (2 * scale) = 8 * scale by omega, ← ha,
      orderOf_dvd_iff_pow_eq_one, mul_comm 4 index, pow_mul, ← hfour]
    exact pow_orderOf_eq_one _
  obtain ⟨multiple, rfl⟩ := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)).mp hdiv
  have hmultiple : multiple < 4 := by nlinarith
  interval_cases multiple
  · simp at hfour
  · simpa only [mul_one] using (IsConj.refl (a ^ (2 * scale)))
  · have hsq : (a ^ (2 * scale * 2)) ^ 2 = 1 := by
      rw [← pow_mul, show 2 * scale * 2 * 2 = 8 * scale by omega,
        ← ha, pow_orderOf_eq_one]
    have hdiv := orderOf_dvd_of_pow_eq_one hsq
    rw [hfour] at hdiv
    norm_num at hdiv
  · have hinv : a ^ (2 * scale * 3) = (a ^ (2 * scale))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_add, show 2 * scale * 3 + 2 * scale = 8 * scale by omega,
        ← ha, pow_orderOf_eq_one]
    rw [hinv]
    apply IsConj.symm
    apply isConj_iff.mpr
    refine ⟨b, ?_⟩
    apply eq_inv_of_mul_eq_one_left
    have hp := congrArg (fun element : G => element ^ (2 * scale)) hconj
    rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply, ← pow_mul] at hp
    rw [hp, ← pow_add]
    have hexp : (4 * scale - 1) * (2 * scale) + 2 * scale =
        (8 * scale) * scale := by
      have : 4 * scale - 1 + 1 = 4 * scale := by omega
      nlinarith
    rw [hexp, pow_mul, ← ha, pow_orderOf_eq_one, one_pow]

private theorem character_of_normal_form (a b : G) (scale : ℕ) (hscale : 0 < scale)
    (ha : orderOf a = 8 * scale) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (4 * scale - 1)) (hnc : ¬ Commute a b)
    (hnf : ∀ element : G, ∃ index : ℕ,
      index < 8 * scale ∧ (element = a ^ index ∨ element = a ^ index * b)) :
    orderOf (a * b) = 4 ∧ ∃ character : G →* Multiplicative (ZMod 2),
      (∀ other : G, other ^ 2 = 1 → character other = 1) ∧
      (∀ other : G, orderOf other = 4 → character other = 1 →
        IsConj other (a ^ (2 * scale))) := by
  have hbb : b * b = 1 := by simpa only [hb, pow_two] using pow_orderOf_eq_one b
  have hsquare (index : ℕ) : (a ^ index * b) ^ 2 = a ^ (4 * scale * index) := by
    calc
      (a ^ index * b) ^ 2 = a ^ index * (b * a ^ index) * b := by
        simp only [pow_two, mul_assoc]
      _ = a ^ index * (a ^ ((4 * scale - 1) * index) * b) * b := by
        rw [move_pow a b _ hconj index]
      _ = a ^ (index + (4 * scale - 1) * index) := by
        rw [mul_assoc, mul_assoc, hbb, mul_one, ← pow_add]
      _ = a ^ (4 * scale * index) := by
        congr 1
        have : 4 * scale - 1 + 1 = 4 * scale := by omega
        nlinarith
  have habsq : (a * b) ^ 2 = a ^ (4 * scale) := by
    simpa only [pow_one, mul_one] using hsquare 1
  have habfour : orderOf (a * b) = 4 := by
    have hne : (a * b) ^ 2 ≠ 1 := by
      rw [habsq]
      exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
    have hfour : (a * b) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, habsq, ← pow_mul,
        show 4 * scale * 2 = 8 * scale by omega, ← ha, pow_orderOf_eq_one]
    exact @orderOf_eq_prime_pow G _ (a * b) 1 2 ⟨Nat.prime_two⟩ hne hfour
  have hodd : ((4 * scale - 1 : ℕ) : ZMod 2) = 1 := by
    apply Odd.natCast_zmod_two
    exact ⟨2 * scale - 1, by omega⟩
  obtain ⟨character, hcharacter⟩ := exists_parity_character a b (8 * scale)
    (4 * scale - 1) (by omega) ha hbb hconj hodd hnc
    (fun element => (hnf element).imp fun index hindex => hindex.2)
  refine ⟨habfour, character, ?_, ?_⟩
  · intro other htwo
    obtain ⟨index, _, rfl | rfl⟩ := hnf other
    · rw [(hcharacter index).1]
      change (index : ZMod 2) = 0
      apply (ZMod.natCast_eq_zero_iff _ _).mpr
      have hdiv : 8 * scale ∣ 2 * index := by
        rw [← ha, orderOf_dvd_iff_pow_eq_one, mul_comm 2 index, pow_mul]
        exact htwo
      have hhalf : 4 * scale ∣ index := by
        apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp
        convert hdiv using 1
        omega
      exact dvd_trans (by omega : 2 ∣ 4 * scale) hhalf
    · rw [(hcharacter index).2]
      change (index : ZMod 2) = 0
      apply (ZMod.natCast_eq_zero_iff _ _).mpr
      have hdiv : 8 * scale ∣ 4 * scale * index := by
        rw [← ha, orderOf_dvd_iff_pow_eq_one, ← hsquare]
        exact htwo
      apply (Nat.mul_dvd_mul_iff_left (by omega : 0 < 4 * scale)).mp
      convert hdiv using 1
      omega
  · intro other hfour hzero
    obtain ⟨index, hindex, rfl | rfl⟩ := hnf other
    · exact cyclic_four_isConj a b scale index hscale ha hconj hindex hfour
    · rw [(hcharacter index).2] at hzero
      change (index : ZMod 2) = 0 at hzero
      obtain ⟨multiple, hmultiple⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hzero
      have htwo : (a ^ index * b) ^ 2 = 1 := by
        rw [hsquare, hmultiple,
          show 4 * scale * (2 * multiple) = (8 * scale) * multiple by ring,
          pow_mul, ← ha, pow_orderOf_eq_one, one_pow]
      have hdiv := orderOf_dvd_of_pow_eq_one htwo
      rw [hfour] at hdiv
      norm_num at hdiv

/-- The semidihedral parity character kills involutions and separates the
outer order-four class from the cyclic order-four class. -/
public theorem exists_order_four_character {H : Type*} [Group H] [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (_hcard : Nat.card H = 2 ^ n) (a b : H)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set H) = ⊤) :
    orderOf (a * b) = 4 ∧ ∃ character : H →* Multiplicative (ZMod 2),
      (∀ other : H, other ^ 2 = 1 → character other = 1) ∧
      (∀ other : H, orderOf other = 4 → character other = 1 →
        IsConj other (a ^ (2 ^ (n - 3)))) := by
  let scale := 2 ^ (n - 4)
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hfull : 2 ^ (n - 1) = 8 * scale := by
    dsimp [scale]
    rw [show n - 1 = n - 4 + 3 by omega, pow_add]
    ring
  have hhalf : 2 ^ (n - 2) = 4 * scale := by
    dsimp [scale]
    rw [show n - 2 = n - 4 + 2 by omega, pow_add]
    ring
  have hquarter : 2 ^ (n - 3) = 2 * scale := by
    dsimp [scale]
    rw [show n - 3 = n - 4 + 1 by omega, pow_add]
    ring
  rw [hquarter]
  apply character_of_normal_form a b scale hscale (ha.trans hfull) hb
    (by simpa only [hhalf] using hconj) (generators_not_commute hn ha hconj)
  intro other
  rw [← hfull]
  exact normal_form a b _ _ (by positivity) ha
    (by rw [← hb]; exact pow_orderOf_eq_one b) hconj hgen other

end Semidihedral
