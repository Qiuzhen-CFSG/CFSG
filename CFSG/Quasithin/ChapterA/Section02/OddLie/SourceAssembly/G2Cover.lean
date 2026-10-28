module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.PrimeCovers
public import Theory.SpecificGroups.G2.MultiplierThree.RootPlaneRank
public import Theory.SpecificGroups.G2.MultiplierThree.UpperBound
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Small

/-!
# The complete odd G₂ cover branch of source A.2.17

The rank-four obstruction through the actual odd center reduces G₂ to a
prime field, and the ordinary multiplier removes primes above three. At
three, the universal kernel bound forces the original center to have order
three and the offending prime to be three. Its A/B lifted root plane raises
ordinary rank to three. The actual G₂(3) quotient is quasithin, so A.2.7
supplies the local rank inequality and the ordinary-rank implication is
vacuous. Both clauses of Theorem A therefore hold for the original offending
section, which the prime center identifies with the actual central quotient.

This source argument does not assert that the triple cover is nonquasithin.
Source: Aschbacher–Smith A.2.14 and A.2.17, printed pp.37–39; I.2.1.
-/

open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

/-- The ternary G₂ Case II endpoint is impossible because its lifted A/B
root plane gives ordinary rank three, while the actual quotient is quasithin.
The proof retains the source failure witness and does not exclude the
quasithin triple cover by a nonexistent local-rank-three subgroup. -/
public theorem g2_three_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G))
    (model : ClassificationModels.IsG2At (G ⧸ center G) 3) : False := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let eF : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three (by
    simpa only [Nat.card_eq_fintype_card] using hq)
  let iso := e.trans (Atlas.G2.fieldEquiv eF.symm)
  let : Fact (2 < Nat.card (ZMod 3)) := ⟨by norm_num⟩
  let c := centralQuotientCover iso
  let d : Covering G (Atlas.G2.Model (ZMod 3)) := c.toCovering
  let hu := Atlas.G2.FiniteCover.cover_isUniversal (ZMod 3)
  have hfac : c.toMonoidHom.comp (hu.lift d).toMonoidHom =
      (Atlas.G2.FiniteCover.cover (ZMod 3)).toMonoidHom :=
    congrArg Covering.toMonoidHom (hu.lift_fac d)
  have hd := kernel_card_dvd_of_surjective_factor
    (Atlas.G2.FiniteCover.cover (ZMod 3)).toMonoidHom c.toMonoidHom
    (hu.lift d).toMonoidHom (hu.lift d).surjective hfac
  change Nat.card c.toMonoidHom.ker ∣ Nat.card
    (universalProjection (Atlas.G2.Model (ZMod 3))).ker at hd
  have hd' : Nat.card (center G) ∣ Nat.card (Atlas.G2.FiniteCover.Kernel (ZMod 3)) := by
    simpa only [c, centralQuotientCover_ker] using hd
  have hle : Nat.card (center G) ≤ 3 :=
    (Nat.le_of_dvd Nat.card_pos hd').trans
      Atlas.G2.FiniteCover.MultiplierThree.kernel_card_le_three
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  have ho : Odd (Nat.card (center G)) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact h.2.2.2.2.2.1.pow
  have hz : Nat.card (center G) = 3 := by
    have hne : Nat.card (center G) ≠ 1 :=
      fun hh => h.center_ne_bot ih.theoremA ((center G).eq_bot_of_card_eq hh)
    have hn0 := Nat.card_pos (α := center G)
    have hh := ho.not_two_dvd_nat
    omega
  have hp3 : p = 3 := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hd3 : 3 ∣ p^n := by rw [← hn, hz]
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp
      (Nat.prime_three.dvd_of_dvd_pow hd3)).symm
  subst p
  have hrank := Atlas.G2.three_le_primeRank_of_ternary_central_quotient iso hP
    (h.center_ne_bot ih.theoremA)
  obtain ⟨N, hN, hne, hNC, ⟨es⟩⟩ := h.quotient_by_nontrivial_center_subgroup ih.theoremA
  let := hN
  let : Fact (Nat.card (center G)).Prime := ⟨by rw [hz]; exact Nat.prime_three⟩
  have hNZ : N = center G := by
    rcases (N.subgroupOf (center G)).eq_bot_or_eq_top_of_prime_card with hb | ht
    · have hm := congrArg (Subgroup.map (center G).subtype) hb
      rw [Subgroup.map_subgroupOf_eq_of_le hNC, Subgroup.map_bot] at hm
      exact (hne hm).elim
    · exact le_antisymm hNC (Subgroup.subgroupOf_eq_top.mp ht)
  have hquot : IsQuasithin (G ⧸ center G) :=
    CFSG.Quasithin.MainConverse.ExceptionalLocal.g2_three_quasithin
      ⟨F, hF, hfin, hq, ⟨e⟩⟩
  have huq := isQuasithin_iff_twoLocalPrimeRank.mp hquot 3 (by decide) (by decide)
  have hug := isQuasithin_iff_twoLocalPrimeRank.mp h.1 3 (by decide) (by decide)
  have hc : TheoremAConclusion G (G ⧸ center G) 3 :=
    ⟨.inl ⟨lemma_A_2_7_4 (center G) (by decide) huq, hug⟩,
      fun hl => (by omega)⟩
  exact h.2.2.2.2.2.2 (hc.of_mulEquiv
    (es.symm.trans (QuotientGroup.quotientMulEquivOfEq hNZ)))

/-- The full odd-characteristic G₂ branch of original source Case II. -/
public theorem g2_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {r e : ℕ} [Fact r.Prime]
    (hr : Odd r) (he : 1 ≤ e)
    (model : ClassificationModels.IsG2At (G ⧸ center G) (r^e)) : False := by
  obtain ⟨rfl, rfl⟩ := g2_caseII_parameters h ih hP hr he model
  exact g2_three_caseII h ih hP (by simpa only [pow_one] using model)
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
