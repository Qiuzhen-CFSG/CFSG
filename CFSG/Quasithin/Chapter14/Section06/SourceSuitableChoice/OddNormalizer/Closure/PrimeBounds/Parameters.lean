module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.BorelParameters

/-!
# Applying the proved prime bound to the source Borel parameters

The maximal-prime choice now supplies the solvable-overgroup bound used by
the earlier field arithmetic. A literal solvable H ≤ J ≤ Mc with a torus
of order 2^m-1 has m=2 at p=3 and m=4 at p=5, under the source congruence.
An odd degree greater than one is impossible even without that congruence.

The latter is the numerical obstruction for the Suzuki Borel extension.
Constructing that extension, the actual component models and the final
wreath quotients remain with qt-e-suitable-odd-normalizer. These theorems
assert no existence or marking of a Borel subgroup.

Source: Aschbacher--Smith, proof of 14.6.14, printed pp.1032--1033.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The source field parameter with the prime-bound premise discharged. -/
theorem source_field_parameter_of_solvable_overgroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc H : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    {p : ℕ} (hp : p = 3 ∨ p = 5) (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (J : Subgroup G) (hHJ : H ≤ J) (hJMc : J ≤ Mc) (hs : Group.IsSolvable J)
    {m : ℕ} (hm : 2 ≤ m) (hdiv : 2 ^ m - 1 ∣ Nat.card J)
    (hcong : Nat.ModEq p (2 ^ m) 1) :
    (p = 3 ∧ m = 2) ∨ (p = 5 ∧ m = 4) :=
  field_parameter_of_solvable_overgroup hp
    (source_solvable_overgroup_prime_bound hG T hunique H hH hp hmax)
    J hHJ hJMc hs hm hdiv hcong

/-- A literal solvable overgroup cannot contain the torus order needed by a Suzuki Borel. -/
theorem source_no_odd_binary_torus_in_solvable_overgroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc H : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    {p : ℕ} (hp : p = 3 ∨ p = 5) (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (J : Subgroup G) (hHJ : H ≤ J) (hJMc : J ≤ Mc) (hs : Group.IsSolvable J)
    {m : ℕ} (hm : 2 ≤ m) (ho : Odd m) : ¬ 2 ^ m - 1 ∣ Nat.card J := by
  intro hdiv
  have hb := source_solvable_overgroup_prime_bound hG T hunique H hH hp hmax
  have hparam : m = 2 ∨ m = 4 := Nat.two_pow_sub_one_small_prime_support hm (by
    intro q hq hqd
    rcases hb J hHJ hJMc hs q hq (hqd.trans hdiv) with rfl | ht | ⟨_,hf⟩
    · have hpow : 2 ∣ (2 : ℕ) ^ m := dvd_pow_self _ (by omega)
      have hpos : 1 ≤ (2 : ℕ) ^ m := Nat.one_le_pow _ _ (by decide)
      have hsum : 2 ∣ (2 ^ m - 1) + 1 := (Nat.sub_add_cancel hpos).symm ▸ hpow
      exact (by decide : ¬ 2 ∣ 1) ((Nat.dvd_add_iff_right hqd).mpr hsum) |>.elim
    · exact Or.inl ht
    · exact Or.inr hf)
  rcases hparam with rfl | rfl <;> norm_num at ho
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
