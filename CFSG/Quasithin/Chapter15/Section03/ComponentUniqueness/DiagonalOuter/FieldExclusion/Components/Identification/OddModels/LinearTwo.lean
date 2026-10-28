module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.FiniteModels.Basic
public import GorensteinWalter.PSL2CoprimeSylowCyclic
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Excluding the odd PSL₂ family from the field-component identification

The PSL₃(2) component forces seven to divide the ambient order. For PSL₂(pᵉ),
with e ≤ 2, this excludes characteristic three and every field of order below
seven. In the remaining cases, the split/nonsplit torus calculation makes the
Sylow three-subgroups cyclic, contradicting the supplied three-rank two.

This argument includes PSL₂(49): its field involution does have a PSL₃(2)
fixed component, so the rank hypothesis cannot be discarded.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, proof of 15.3.38,
printed p.1137; Theorem C, printed p.33. The torus calculation is Huppert
II.8.2--5, proved in `GorensteinWalter.PSL2CoprimeSylowCyclic`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

variable {S : Type*} [Group S] (s : SimpleInput S)
include s

/-- No PSL₂(pᵉ) entry of Theorem C satisfies the field-component input. -/
theorem SimpleInput.not_linear_two [Finite S]
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e ≤ 2) :
    ¬ ClassicalGroup.IsPSL S 2 (p ^ e) := by
  rintro ⟨F, hF, hfin, hcard, ⟨a⟩⟩
  let : Fact p.Prime := ⟨hp⟩
  have hseven : 7 ∣ Nat.card PSL(2,F) := by
    rw [← Nat.card_congr a.toEquiv]
    exact s.seven_dvd_card
  have horder := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F)
    (hcard ▸ ho.pow)
  have hsevenOrder : 7 ∣ p ^ e * ((p ^ e) ^ 2 - 1) := by
    rw [← hcard, ← horder]
    exact dvd_mul_of_dvd_left hseven 2
  have hepos : e ≠ 0 := by
    intro hz
    have hlarge := Finite.one_lt_card (α := F)
    rw [hcard, hz, pow_zero] at hlarge
    omega
  by_cases hp3 : p = 3
  · subst p
    have hecases : e = 1 ∨ e = 2 := by omega
    rcases hecases with rfl | rfl <;> norm_num at hsevenOrder
  · have hlarge : 7 ≤ Nat.card F := by
      by_contra! hs
      have hc : Nat.card F = 3 ∨ Nat.card F = 5 := by
        have hodd : Nat.card F % 2 = 1 := Nat.odd_iff.mp (hcard ▸ ho.pow)
        have hgt := Finite.one_lt_card (α := F)
        omega
      rcases hc with hc | hc <;>
        rw [hcard] at hc <;> rw [hc] at hsevenOrder <;> norm_num at hsevenOrder
    let P : Sylow 3 PSL(2,F) := default
    have hP : IsCyclic P := GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F
      hcard hlarge 3 (by decide)
      (by rw [hcard]; exact ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)).pow_right e) P
    have hr := P.primeRank_le_one_of_isCyclic hP
    rw [← primeRank_equiv 3 a, s.rank] at hr
    omega

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
