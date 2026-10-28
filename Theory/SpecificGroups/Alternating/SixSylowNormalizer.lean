module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupAction.SimpleCosets
public import Mathlib.Tactic.NormNum

/-!
# A Sylow 2-subgroup of A₆ cannot normalize an A₅ subgroup

Every A₅ subgroup of A₆ is self-normalizing: it has index six, and the
faithful coset action of a simple group rules out a proper overgroup of
smaller index. The claimed Sylow invariance would then force eight to
divide sixty.

This is the finite-group obstruction at the end of Aschbacher--Smith,
Lemma 3.3.22, printed p.598. The statement uses an actual A₅ isomorphism
and covers both classes of A₅ subgroups in A₆.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.Alternating.SixSylowNormalizer
local notation "A6" => alternatingGroup (Fin 6)
local notation "A5" => alternatingGroup (Fin 5)

/-- Both classes of A₅ subgroups in A₆ are self-normalizing. -/
theorem five_subgroup_normalizer (H : Subgroup A6) (e : H ≃* A5) : normalizer (H : Set A6) = H := by
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  have hcard : Nat.card H = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hgroup : Nat.card A6 = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hi : H.index = 6 := by
    have hm := H.card_mul_index
    rw [hcard, hgroup] at hm
    omega
  let N := normalizer (H : Set A6)
  have hn : N ≠ ⊤ := by
    intro hn
    have hnormal : H.Normal := normalizer_eq_top_iff.mp hn
    rcases hnormal.eq_bot_or_eq_top with hb | ht
    · rw [hb,card_bot] at hcard
      norm_num at hcard
    · rw [ht,card_top,hgroup] at hcard
      norm_num at hcard
  have hd : 360 ∣ N.index.factorial := by
    simpa only [hgroup] using N.card_dvd_factorial_index_of_simple hn
  have hlow : 6 ≤ N.index := by
    by_contra h
    have hb : N.index ≤ 5 := by omega
    interval_cases hm : N.index <;> norm_num [hm,Nat.factorial] at hd
  have hm := H.relIndex_mul_index H.le_normalizer
  rw [hi] at hm
  have hpos : 0 < H.relIndex N := Nat.pos_of_ne_zero (by
    intro he
    change H.relIndex N * N.index = 6 at hm
    rw [he,zero_mul] at hm
    contradiction)
  have he : H.relIndex N = 1 := by
    change H.relIndex N * N.index = 6 at hm
    nlinarith
  exact le_antisymm (Subgroup.relIndex_eq_one.mp he) H.le_normalizer

/-- The last contradiction in the A₇ branch of source 3.3.22. -/
theorem no_sylow_normalizes_five (P : Sylow 2 A6) (H : Subgroup A6)
    (e : H ≃* A5) : ¬ (P : Subgroup A6) ≤ normalizer (H : Set A6) := by
  intro hn
  rw [five_subgroup_normalizer H e] at hn
  have hd := Subgroup.card_dvd_of_le hn
  have hp : Nat.card (P : Subgroup A6) = 8 := by
    rw [P.card_eq_multiplicity, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    decide +kernel
  have hh : Nat.card H = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hp, hh] at hd
  norm_num at hd

end Theory.SpecificGroups.Alternating.SixSylowNormalizer
