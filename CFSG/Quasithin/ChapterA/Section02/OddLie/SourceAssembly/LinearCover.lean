module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.PrimeCovers
public import Theory.Quasithin.CentralExtensionSL2Pair
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import Theory.SpecificGroups.LinearHigher.OddCharacteristicCover
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The complete odd split-linear cover branch of A.2.17

The original odd center and root ranks reduce the degree to at most four.
The completed PSL₂ and PSL₃ cover branches leave PSL₄; two commuting SL₂
factors force a prime field. The actual Steinberg scalar lift bounds the
remaining odd center by four, making it trivial and contradicting the
original Case II failure witness. Characteristic three is included.
Source: Aschbacher–Smith A.2.14 and A.2.17, printed pp.37–39.
-/

open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly

/-- Two actual complementary two-spaces in PSL₄ force a prime field through
an odd central kernel, with no quotient quasithinness premise. -/
public theorem linear_four_fieldExponent_eq_one_of_odd_center
    {G : Type*} [Group G] [Finite G]
    (hqt : IsQuasithin G) (ho : Odd (Nat.card (center G)))
    {r e : ℕ} [Fact r.Prime] (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSL (G ⧸ center G) 4 (r^e)) : e = 1 := by
  obtain ⟨F, hF, hfin, hc, ⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  apply CentralExtension.fieldExponent_eq_one_of_commuting_sl2 hr2 he hc
    (iso.trans (ClassicalStructure.linearModelEquiv F 1).symm) ho hqt
    (ClassicalStructure.linearFundamental F 1) (ClassicalStructure.linearComplement F 1)
    (ClassicalStructure.linearFundamental_injective F 1)
    (Matrix.SpecialLinearGroup.LinearFundamental.projectRight_injective (m := Fin 2))
    (ClassicalStructure.linear_factors_commute F 1)

universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

/-- Original odd split-linear Case II has precisely degree four over a prime
field after all elementary-rank and completed degree-two/three cover cases. -/
public theorem linear_caseII_parameters
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {r e n : ℕ} [Fact r.Prime]
    (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSL (G ⧸ center G) n (r^e)) : n = 4 ∧ e = 1 := by
  have ho : Odd (Nat.card (center G)) := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    rw [hk]
    exact h.2.2.2.2.2.1.pow
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hn4 := DefiningKernel.linear_degree_le_four_of_odd_center hr2 he h.1 ho model
  have hn2 : n ≠ 2 := by
    intro hn2
    subst n
    obtain ⟨F,hF,hfin,hc,⟨iso⟩⟩ := model
    let : Group.IsPerfect PSL(2,F) :=
      Group.IsPerfect.ofSurjective (f := iso.toMonoidHom) iso.surjective
    have hq : 3 < Nat.card F := by
      by_contra hq
      have hl : 1 < Nat.card F := Finite.one_lt_card
      have hfodd : Odd (Nat.card F) := hc ▸ hr.pow
      have h3 : Nat.card F = 3 := by obtain ⟨k,hk⟩ := hfodd; omega
      exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three h3 inferInstance
    exact linear_two_caseII h ih hP (hc ▸ hq) hr.pow ⟨F,hF,hfin,hc,⟨iso⟩⟩
  have hn3 : n ≠ 3 := by
    intro hn3
    subst n
    exact linear_three_caseII h ih hP hr he model
  have hn4eq : n = 4 := by omega
  subst n
  exact ⟨rfl,linear_four_fieldExponent_eq_one_of_odd_center h.1 ho hr he model⟩

/-- Every odd split-linear central quotient is excluded in the original
source Case II. The last degree-four prime-field case uses the actual
Steinberg scalar lift, including characteristic three. -/
public theorem linear_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {r e n : ℕ} [Fact r.Prime]
    (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSL (G ⧸ center G) n (r^e)) : False := by
  obtain ⟨rfl,rfl⟩ := linear_caseII_parameters h ih hP hn hr he model
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have ho : Odd (Nat.card (center G)) := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    rw [hk]
    exact h.2.2.2.2.2.1.pow
  let c := PerfectCentralCovering.centralQuotientCover iso
  obtain ⟨s,hs,hfac,_⟩ :=
    Theory.SpecificGroups.LinearHigher.OddCharacteristicCover.exists_covering_of_card_prime
      Fact.out hr2 (by simpa using hcard) c.toMonoidHom c.surjective c.ker_le_center
      (by simpa only [c,PerfectCentralCovering.centralQuotientCover_ker] using ho)
  have hd := kernel_card_dvd_of_surjective_factor
    (QuotientGroup.mk' (center SL(4,F))) c.toMonoidHom s hs hfac
  have hz4 : Nat.card (center G) ∣ 4 := by
    have hk : Nat.card (MonoidHom.ker (QuotientGroup.mk' (center SL(4,F)))) =
        Nat.gcd 4 (Nat.card F - 1) := by
      rw [QuotientGroup.ker_mk',Atlas.ExceptionalSupport.card_sl_center]
      rfl
    rw [hk] at hd
    have hd' : Nat.card (center G) ∣ Nat.gcd 4 (Nat.card F - 1) := by
      simpa only [c,PerfectCentralCovering.centralQuotientCover_ker] using hd
    exact hd'.trans (Nat.gcd_dvd_left _ _)
  have hz1 : Nat.card (center G) = 1 := Nat.eq_one_of_dvd_coprimes
    (ho.coprime_two_right.pow_right 2) dvd_rfl hz4
  exact h.center_ne_bot ih.theoremA ((center G).eq_bot_of_card_eq hz1)

end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
