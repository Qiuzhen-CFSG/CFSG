module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.Reduction
public import GorensteinWalter.PSL2CoprimeSylowCyclic
public import Theory.SpecificGroups.SL2.OddOrderDivisibility

/-!
# The odd-characteristic PSL₂ branch of the seven inspection

For q = p or p², with p odd and q ≥ 4, PSL₂(q) has no subgroup isomorphic
to A₇ or its perfect central three-cover. For p ≠ 3 and q ≥ 7 the cyclic
Sylow three-subgroups give three-rank at most one. The remaining fields
are q = 5 and q = 9, whose projective group orders are 60 and 360; neither
is divisible by seven. The proof transports these calculations along the
actual projective matrix equivalence supplied by the model predicate.

This proves the inspection for every two-subgroup of the automorphism group
without requiring a classification of its automorphisms. The stronger
subgroup exclusion makes the common-fixed component configuration impossible.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252 (PDF p.263), and Theorem C, printed p.33; the cyclic Sylow
calculation is the split/nonsplit torus argument of Huppert II.8.2–5.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie
variable {G : Type*} [Group G] [Finite G]

/-- No subgroup of an odd-characteristic Theorem C PSL₂ model is a seven group. -/
theorem not_isSeven_linear_two {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2) (hq : 4 ≤ p ^ e)
    (hG : ClassicalGroup.IsPSL G 2 (p ^ e)) (L : Subgroup G) : ¬ IsSeven L := by
  obtain ⟨F, hfield, hfinite, hF, ⟨f⟩⟩ := hG
  let : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (Nat.card F) := hF ▸ ho.pow
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) hodd
  have hcG : Nat.card G * 2 = p ^ e * ((p ^ e) ^ 2 - 1) := by
    rw [Nat.card_congr f.toEquiv, ← hF]
    exact hc
  by_cases hsmall : p ^ e < 7
  · have hfive : p ^ e = 5 := by
      have hp2 := hp.two_le
      have hpn2 : p ≠ 2 := fun h => by subst p; exact (by decide : ¬ Odd 2) ho
      have hp3 : 3 ≤ p := by omega
      rcases he with rfl | rfl
      · simp only [pow_one] at hq hsmall ⊢
        obtain ⟨k, hk⟩ := ho
        omega
      · nlinarith
    have hcard : Nat.card G = 60 := by rw [hfive] at hcG; omega
    exact not_isSeven_of_seven_not_dvd (by rw [hcard]; decide) L
  by_cases hp3 : p = 3
  · have he2 : e = 2 := he.resolve_left (by intro h; rw [h, pow_one, hp3] at hq; omega)
    have hcard : Nat.card G = 360 := by rw [hp3, he2] at hcG; norm_num at hcG; omega
    exact not_isSeven_of_seven_not_dvd (by rw [hcard]; decide) L
  · let R : Sylow 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := default
    have hcyc : IsCyclic R := GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card
      F hF (by omega) 3 (by decide) (by
        rw [hF]
        exact ((Nat.coprime_primes (by decide) hp).mpr (Ne.symm hp3)).pow_right e) R
    have hr : primeRank 3 G ≤ 1 := by
      rw [primeRank_congr 3 f]
      exact R.primeRank_le_one_of_isCyclic hcyc
    exact not_isSeven_of_three_rank_le_one hr L

/-- The complete odd-characteristic PSL₂ branch, with the actual model witness. -/
theorem sevenActionInspection_linear_two {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2) (hq : 4 ≤ p ^ e)
    (hG : ClassicalGroup.IsPSL G 2 (p ^ e)) : SevenActionInspection G := by
  intro P hP L hLF hLc hL
  exact (not_isSeven_linear_two hp ho he hq hG L hL).elim


end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie
