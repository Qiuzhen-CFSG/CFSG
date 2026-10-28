module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.BorelPlacement.Seed
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.NumberTheory.BinaryTorusParity

/-!
# The parity restriction on a symplectic Borel block

An A₃-block has a quotient of order three. An injective map into a finite
power of a symplectic Borel therefore forces three to divide the Borel order
q⁴(q−1)². Since q = 2ⁿ, this is equivalent to even n. This arithmetic
exclusion does not require subnormality, and closes every odd-degree branch
of the Borel placement reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed p.248 (PDF p.259), and the A₃-block definition C.1.12, p.124.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.BorelPlacement

/-- An alternating-three block has an actual quotient of order three. -/
theorem three_dvd_card_of_alternating_three {X : Type*} [Group X]
    (hX : ChapterC.IsAlternatingBlock X 3) : 3 ∣ Nat.card X := by
  let _ := hX.2.1.finite
  obtain ⟨e⟩ := hX.2.2.quotient_iso
  have he : Nat.card (X ⧸ pCore 2 X) = 3 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [← he]
  exact card_quotient_dvd_card (pCore 2 X)

/-- Divisibility alone excludes all odd field exponents, even without subnormality. -/
theorem even_degree_of_matrix_block {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) {X : Type*} [Group X]
    (hX : ChapterC.IsAlternatingBlock X 3) {k : ℕ}
    (f : X →* (Fin k → borel (F := F))) (hf : Function.Injective f) : Even n := by
  let _ := hX.2.1.finite
  have hd := (three_dvd_card_of_alternating_three hX).trans (card_dvd_of_injective f hf)
  rw [Nat.card_fun, Nat.card_fin] at hd
  have hB := Nat.prime_three.dvd_of_dvd_pow hd
  rw [card_borel, hF] at hB
  rcases Nat.prime_three.dvd_mul.mp hB with hq | ht
  · have hh : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow
      (Nat.prime_three.dvd_of_dvd_pow hq)
    norm_num at hh
  · exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp
      (Nat.prime_three.dvd_of_dvd_pow ht)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.BorelPlacement
