module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.DefiningThree
public import Theory.SpecificGroups.Classical.ThreeCoverLocalRanks
public import Theory.SpecificGroups.ProjectiveDimensionThree.NondefiningThreeRank
public import Theory.SpecificGroups.PSU3.PrimeOddCenterCover
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound
/-!
# Ordinary nondefining ranks of the actual signed-three covers

Ordinary scalar-cover recognition identifies a centered linear cover with
SL₃. In the unitary case the prime-field recognition does the same; at a
prime-square fixed field the full kernel bound has gcd(3,r²+1)=1 and forces
the cover to be centerless. In the centerless cases the actual projective
rank bounds include the noncommuting lift case at the prime three.

Thus every nondefining prime has ordinary rank at most two in the actual
covering group S. This discharges the remaining prime choice in the
signed-three branch of Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.SignedThree
open Theory.SpecificGroups.Classical.ThreeCoverLocalRanks

private theorem cast_ne_zero {F : Type*} [Field F] [Finite F]
    {p r e : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r)
    (hc : Nat.card F = r ^ e) : (p : F) ≠ 0 := by
  let : Fact r.Prime := ⟨hr⟩
  let := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  intro hh
  have hd : r ∣ p := (CharP.cast_eq_zero_iff F r p).mp hh
  exact hne ((Nat.prime_dvd_prime_iff_eq hr hp).mp hd).symm

private theorem projective_linear_rank {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hc : (p : F) ≠ 0) : primeRank p PSL(3,F) ≤ 2 := by
  by_cases hp : p = 3
  · subst p
    exact Matrix.ProjectiveDimensionThree.psl_primeRank_three_le_two hc
  · exact projective_linear_odd_prime_rank_le_two hp hc

private theorem projective_unitary_rank {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} [Fact p.Prime]
    (hc : (p : F) ≠ 0) : primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2 := by
  by_cases hp : p = 3
  · subst p
    exact Matrix.ProjectiveDimensionThree.psu_primeRank_three_le_two hc J
  · exact projective_unitary_odd_prime_rank_le_two J hp hc

private theorem rank_le_two_of_centerless {L Q : Type*} [Group L] [Group Q]
    [Finite L] [Finite Q] {p : ℕ} (hz : center L = ⊥)
    (e : L ⧸ center L ≃* Q) (hq : primeRank p Q ≤ 2) : primeRank p L ≤ 2 := by
  let a : L ≃* Q := ((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).symm.trans e
  rw [primeRank_equiv p a]
  exact hq

theorem linear_cover_nondefining_rank_le_two
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    {p r e : ℕ} (hp : p.Prime) (hr : r.Prime) (ho : Odd r) (_he : 0 < e)
    (hne : p ≠ r) (hm : ClassicalGroup.IsPSL (L ⧸ center L) 3 (r ^ e)) :
    primeRank p L ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hcard, ⟨a⟩⟩ := hm
  have hcast := cast_ne_zero hp hr hne hcard
  by_cases hz : center L = ⊥
  · exact rank_le_two_of_centerless hz a (projective_linear_rank hcast)
  · have hodd : Odd (Nat.card F) := hcard ▸ ho.pow
    have h2 : Nat.card F ≠ 2 := by intro hh; rw [hh] at hodd; norm_num at hodd
    have h4 : Nat.card F ≠ 4 := by intro hh; rw [hh] at hodd; norm_num at hodd
    obtain ⟨_, _, _, b, _⟩ := Matrix.PSL3.OrdinaryCenterRecognition.nontrivial_center_recognition
      h2 h4 a hz
    rw [primeRank_equiv p b.symm]
    exact special_odd_prime_rank_le_two hcast

private theorem gcd_three_square_add_one (r : ℕ) : Nat.gcd 3 (r ^ 2 + 1) = 1 := by
  apply Nat.Coprime.gcd_eq_one
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  have he := Nat.mod_eq_zero_of_dvd hd
  have hm : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;> simp [Nat.add_mod, Nat.pow_mod, hm] at he

theorem unitary_cover_nondefining_rank_le_two
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    {p r e : ℕ} (hp : p.Prime) (hr : r.Prime) (ho : Odd r) (he : e = 1 ∨ e = 2)
    (hne : p ≠ r) (hzodd : Odd (Nat.card (center L)))
    (hm : ClassicalGroup.IsPSU (L ⧸ center L) 3 (r ^ e)) : primeRank p L ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, J, hcard, hconj, ⟨a⟩⟩ := hm
  have hcast : (p : F) ≠ 0 := cast_ne_zero hp hr hne (by simpa only [← pow_mul] using hcard)
  have hr2 : r ≠ 2 := by rintro rfl; norm_num at ho
  have hqr := projective_unitary_rank J hcast
  by_cases hz : center L = ⊥
  · exact rank_le_two_of_centerless hz a hqr
  rcases he with rfl | rfl
  · obtain ⟨_, _, _, b, _⟩ := HermitianForm.PrimeOddCenterCover.nontrivial_center_recognition
      J hr hr2 (by simpa using hcard) (by simpa using hconj) a hzodd hz
    rw [primeRank_equiv p b.symm]
    exact unitary_odd_prime_rank_le_two J hcast
  · let c := centralQuotientCover a
    have hd := HermitianForm.UniversalCover.OddKernelBound.card_kernel_dvd_gcd
      J hr hr2 (by decide : 1 ≤ 2) (by decide : 2 ≤ 2) hcard hconj c
    rw [gcd_three_square_add_one r] at hd
    have hc : Nat.card (center L) = 1 := by
      simpa only [c, centralQuotientCover_ker] using Nat.eq_one_of_dvd_one hd
    exact (hz (card_eq_one.mp hc)).elim

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.SignedThree

namespace CFSG.Quasithin.ChapterA.Section02
open Nonsemisimple.RankTwoSieve
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.not_odd_psl_three_centralQuotient
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
    (hm : ClassicalGroup.IsPSL (S ⧸ center S) 3 (r ^ e)) : False := by
  by_cases hp : p = r
  · subst r
    exact h.not_defining_psl_three_centralQuotient ih e he hm
  · let := h.2.2.2.1.isPerfect
    have hb := Nonsemisimple.SignedThree.linear_cover_nondefining_rank_le_two
      h.2.2.2.2.1 hr ho he hp hm
    exact (not_le_of_gt (lemma_A_2_14 h ih.theoremA)) hb

theorem CounterexampleToTheoremA.not_odd_psu_three_centralQuotient
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hn : ¬ IsSemisimple G)
    (r e : ℕ) (hr : r.Prime) (ho : Odd r) (he : 0 < e)
    (hm : ClassicalGroup.IsPSU (S ⧸ center S) 3 (r ^ e)) : False := by
  by_cases hp : p = r
  · subst r
    exact h.not_defining_psu_three_centralQuotient ih e he hm
  by_cases he2 : 2 < e
  · obtain ⟨f,hf⟩ := h.exists_surjective ih.theoremA
    exact no_psu_three_large_quotient ih h.1 h.2.1
      ((QuotientGroup.mk' (center S)).comp f) ((QuotientGroup.mk'_surjective _).comp hf)
      r e hr ho he2 hm
  · let := h.section_quasisimple_of_not_semisimple ih.theoremA hn
    have hb := Nonsemisimple.SignedThree.unitary_cover_nondefining_rank_le_two
      h.2.2.2.2.1 hr ho (by omega) hp (h.section_center_odd_card ih.theoremA) hm
    exact (not_le_of_gt (lemma_A_2_14 h ih.theoremA)) hb

end CFSG.Quasithin.ChapterA.Section02
