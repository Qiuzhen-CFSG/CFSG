module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.CoverCases
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.SymplecticG2
public import CFSG.Quasithin.ChapterA.Section02.OddLie.DefiningKernel
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
public import Theory.SpecificGroups.G2.MultiplierOrdinary
public import Theory.Quasithin.CentralExtensionRankBound

/-!
# Odd prime-field cover branches in A.2.17

The actual symplectic universal double cover excludes the prime-field PSp₄
endpoint, including three. The central quotient rank bound applied to the
two G₂ root groups forces a prime field in the original Case II group.
The completed ordinary G₂ covering calculation then removes every prime
greater than three, retaining exactly the ternary endpoint.

All conclusions concern the original Theorem A counterexample. No
quasithinness of an arbitrary odd central quotient is assumed.
Source: Aschbacher–Smith A.2.17, printed p.39; I.1.4, printed p.408.
-/

open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

omit [IsQuasisimple G] in
private theorem odd_center (h : CounterexampleToTheoremA K G S p)
    (hP : IsPGroup p (center G)) : Odd (Nat.card (center G)) := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  exact h.2.2.2.2.2.1.pow

/-- The actual universal double cover excludes the prime-field symplectic
endpoint from original Case II, including characteristic three. -/
public theorem symplectic_prime_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {r : ℕ} [Fact r.Prime] (hr : Odd r)
    (model : ClassicalGroup.IsPSp (G ⧸ center G) 2 r) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨iso⟩⟩ := model
  let : Fact (2 < Nat.card F) := ⟨by
    have := (Fact.out : r.Prime).two_le
    have hne : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
    omega⟩
  let c := centralQuotientCover iso
  let d : Covering G (ClassicalGroup.PSp 2 F) := c.toCovering
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hu := Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.quotientCover_isUniversal hr2 hc
  have hfac : c.toMonoidHom.comp (hu.lift d).toMonoidHom =
      (Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.quotientCover F).toMonoidHom :=
    congrArg Covering.toMonoidHom (hu.lift_fac d)
  have hdvd : Nat.card (center G) ∣ 2 := by
    have hd := kernel_card_dvd_of_surjective_factor
      (Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.quotientCover F).toMonoidHom
      c.toMonoidHom (hu.lift d).toMonoidHom (hu.lift d).surjective hfac
    have hk : Nat.card
        (Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.quotientCover F).toMonoidHom.ker = 2 := by
      rw [show (Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.quotientCover F).toMonoidHom.ker = center (Matrix.symplecticGroup (Fin 2) F) from QuotientGroup.ker_mk' _]
      exact Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.card_center
        (Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.two_ne_zero Fact.out hr2 hc)
    simpa only [hk, c, centralQuotientCover_ker] using hd
  have hcard1 : Nat.card (center G) = 1 := Nat.eq_one_of_dvd_coprimes
    (odd_center h hP).coprime_two_right dvd_rfl hdvd
  exact h.center_ne_bot ih.theoremA ((center G).eq_bot_of_card_eq hcard1)

omit [IsQuasisimple G] in
/-- The actual G₂ root pair forces a prime field even in original Case II,
through the odd central kernel and without quasithinness of the quotient. -/
public theorem g2_fieldExponent_eq_one_of_odd_center
    (hqt : IsQuasithin G) (ho : Odd (Nat.card (center G)))
    {r e : ℕ} [Fact r.Prime] (hr : Odd r) (he : 1 ≤ e)
    (model : ClassificationModels.IsG2At (G ⧸ center G) (r^e)) : e = 1 := by
  obtain ⟨F, hF, hfin, hc, ⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  obtain ⟨z, hz, hz2, hl⟩ := Atlas.G2.exists_involution_two_mul_fieldExponent_le_primeRank
    hr2 hc (MonoidHom.id (Atlas.G2.Model F)) Function.injective_id
  have hu := CentralExtension.primeRank_involutionCentralizer_le_three_of_odd_center hr2 iso ho hqt
    (orderOf_eq_prime hz2 hz)
  omega

/-- The completed ordinary G₂ multiplier calculation excludes every odd
prime greater than three from original Case II. -/
public theorem g2_large_prime_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (model : ClassificationModels.IsG2At (G ⧸ center G) r) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨iso⟩⟩ := model
  let : Fact (2 < Nat.card F) := ⟨by omega⟩
  let c := centralQuotientCover iso
  let d : Covering G (Atlas.G2.Model F) := c.toCovering
  let hu := Atlas.G2.FiniteCover.cover_isUniversal F
  have hfac : c.toMonoidHom.comp (hu.lift d).toMonoidHom =
      (Atlas.G2.FiniteCover.cover F).toMonoidHom :=
    congrArg Covering.toMonoidHom (hu.lift_fac d)
  have hd := kernel_card_dvd_of_surjective_factor
    (Atlas.G2.FiniteCover.cover F).toMonoidHom c.toMonoidHom
    (hu.lift d).toMonoidHom (hu.lift d).surjective hfac
  have hk := Atlas.G2.MultiplierOrdinary.prime_universalProjection_ker_eq_bot hc hr
  change Nat.card c.toMonoidHom.ker ∣ Nat.card (universalProjection (Atlas.G2.Model F)).ker at hd
  have hcard1 : Nat.card (center G) = 1 := by
    simpa only [c, centralQuotientCover_ker, hk, card_bot, Nat.dvd_one] using hd
  exact h.center_ne_bot ih.theoremA ((center G).eq_bot_of_card_eq hcard1)

/-- The full original odd G₂ Case II branch is reduced to its precise ternary
endpoint; every larger characteristic and every extension field is excluded. -/
public theorem g2_caseII_parameters
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {r e : ℕ} [Fact r.Prime]
    (hr : Odd r) (he : 1 ≤ e)
    (model : ClassificationModels.IsG2At (G ⧸ center G) (r^e)) : r = 3 ∧ e = 1 := by
  have he1 := g2_fieldExponent_eq_one_of_odd_center h.1 (odd_center h hP) hr he model
  subst e
  have hm : ClassificationModels.IsG2At (G ⧸ center G) r := by
    simpa only [pow_one] using model
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hp := (Fact.out : r.Prime).two_le
  have hr3 : r = 3 := by
    by_contra hn
    exact g2_large_prime_caseII h ih (by omega) hm
  exact ⟨hr3,rfl⟩
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
