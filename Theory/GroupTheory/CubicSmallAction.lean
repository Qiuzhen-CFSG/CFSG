module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow-normalized cubics in small actions

In a group of order dividing 48, the normalizer of a cubic subgroup has
index dividing sixteen. If a Sylow two-subgroup normalizes that cubic,
the same index is odd, so the cubic is normal. For an action with
three-group kernel, pulling back this normal image places the original
cubic in the full three-core. No faithfulness or splitting is assumed.

Source application: Aschbacher–Smith, 14.7.27, printed pp.1054–1055,
refs/quasithin.pdf; the action is on a supercritical Frattini plane.
-/

public noncomputable section
namespace Theory.GroupTheory
open Subgroup
variable {D E : Type*} [Group D] [Finite D] [Group E]

/-- A cubic normalized by a Sylow two-subgroup is normal in a group of order dividing 48. -/
theorem cubic_normal_of_sylow_normalizes_card_dvd_fortyEight
    (hcard : Nat.card D ∣ 48) (S : Sylow 2 D) (A : Subgroup D)
    (hA : Nat.card A = 3) (hn : (S : Subgroup D) ≤ normalizer (A : Set D)) :
    A.Normal := by
  let N := normalizer (A : Set D)
  have hthree : 3 ∣ Nat.card N := hA ▸ card_dvd_of_le A.le_normalizer
  have hmul : 3 * N.index ∣ 3 * 16 :=
    (Nat.mul_dvd_mul_right hthree N.index).trans (N.card_mul_index ▸ hcard)
  have hi : N.index ∣ 16 := Nat.dvd_of_mul_dvd_mul_left (by decide) hmul
  have hcop : Nat.Coprime 16 (S : Subgroup D).index :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr S.not_dvd_index).pow_left 4
  exact normalizer_eq_top_iff.mp (index_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hcop hi (index_dvd_of_le hn)))

/-- A small action with three-group kernel puts a Sylow-normalized cubic in the full three-core. -/
theorem cubic_le_threeCore_of_small_action
    (f : D →* E) (hk : IsPGroup 3 f.ker) (hcard : Nat.card f.range ∣ 48)
    (S : Sylow 2 D) (A : Subgroup D) (hA : Nat.card A = 3)
    (hn : (S : Subgroup D) ≤ normalizer (A : Set D)) : A ≤ pCore 3 D := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let r := f.rangeRestrict
  let B := A.map r
  have hpA : IsPGroup 3 A := IsPGroup.of_card (n := 1) hA
  have hdiv : Nat.card B ∣ 3 := hA ▸ card_map_dvd A r
  have hBnormal : B.Normal := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hc | hc
    · have hb : B = ⊥ := eq_bot_of_card_eq _ hc
      rw [hb]
      infer_instance
    · exact cubic_normal_of_sylow_normalizes_card_dvd_fortyEight hcard
        (S.mapSurjective f.rangeRestrict_surjective) B hc
        ((map_mono hn).trans (le_normalizer_map r))
  let := hBnormal
  have hkr : IsPGroup 3 r.ker := hk.to_le (by
    intro x hx
    exact congrArg Subtype.val hx)
  exact (le_comap_map _ _).trans
    (le_sSup ⟨inferInstance,(hpA.map r).comap_of_ker_isPGroup r hkr⟩)

end Theory.GroupTheory
