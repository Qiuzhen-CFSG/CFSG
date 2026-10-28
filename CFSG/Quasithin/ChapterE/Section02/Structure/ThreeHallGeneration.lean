module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.KnownSimple

/-!
# Generation at degree two from an actual Hall three-group

For an SQTK minimal parabolic, the complete original E.2.2 construction
supplies a Hall subgroup containing a cyclic group of order 2^f-1, with
n(H) at most f. If any odd Hall subgroup of the unique maximal overgroup
is a three-group, equality of Hall orders makes the constructed cyclic
group a three-group as well. Reduction modulo eight forces f at most two.
This uses the adequate inequality through the solvable core, not an
unproved equality of generation parameters.

Source: Aschbacher–Smith, Proposition 10.2.3, printed p.745, using E.2.2,
pp.215–216. Faithfulness and Borel placement in the Chapter10 application
remain distinct geometric source conclusions.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE
open ChapterB Section06.FixedPointBounds Section06.FixedPointBounds.ParabolicCartan

private theorem mersenne_three_power_bound {n k : ℕ} (h : 2 ^ n - 1 = 3 ^ k) : n ≤ 2 := by
  by_contra hn
  have hn3 : 3 ≤ n := by omega
  have hdiv : 8 ∣ 2 ^ n := by
    have hh := pow_dvd_pow (2 : ℕ) hn3
    simpa using hh
  have hpowers : ∀ k : ℕ, 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with ih | ih <;> simp [ih]
  have hpos : 0 < (2 : ℕ) ^ n := pow_pos (by decide) n
  have he : 2 ^ n = 3 ^ k + 1 := by omega
  have hm := Nat.mod_eq_zero_of_dvd hdiv
  rw [he, Nat.add_mod] at hm
  rcases hpowers k with hpow | hpow <;> omega

theorem generationParameter_le_two_of_three_hall
    {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (B : Subgroup X) (hBM : B ≤ minimalParabolicMax S hP)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (minimalParabolicMax S hP)))
    (hB : IsPGroup 3 B) : generationParameter X ≤ 2 := by
  by_contra hn
  have hn1 : 1 < generationParameter X := by omega
  obtain ⟨n, _, hb, d, _⟩ :=
    MarkedModels.Inverted.source_intrinsic_escape_knownSimple hX S hP hn1
  have hY : IsPGroup 3 d.witness.abelianGroup := by
    obtain ⟨k,hk⟩ := hB.exists_card_eq
    apply IsPGroup.of_card (n := k)
    have he := d.hall.card_eq hHall
    rw [Nat.card_congr (subgroupOfEquivOfLe d.hall_le).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv] at he
    exact he.trans hk
  obtain ⟨k,hk⟩ := (hY.to_le d.witness.cyclic_le).exists_card_eq
  have hn2 := mersenne_three_power_bound (d.witness.card.symm.trans hk)
  omega

end CFSG.Quasithin.ChapterE
