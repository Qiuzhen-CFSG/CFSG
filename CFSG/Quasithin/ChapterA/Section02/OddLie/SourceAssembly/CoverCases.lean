module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.QuasisimpleCase
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalRanks.NondefiningThree
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.PSL2
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.CoveringKernelCard

/-!
# Actual odd linear central covers in A.2.17 Case II

For degree three, the genuine universal scalar projection bounds the
original center by three. Its nontriviality forces exactly order three and
nondefining characteristic; the projective three-rank bound contradicts
the original A.2.14 failure witness. This works at every odd field degree.
For degree two, the universal SL₂ projection has two-element kernel, so
an odd center is trivial. The order-nine exception is transported through
the actual PSL₂(9) ≃ A₆ equivalence and the alternating cover exclusion.

No quasithinness of an arbitrary quotient is assumed.
Source: Aschbacher–Smith, A.2.14 and A.2.17, printed pp.37–39.
-/

open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

omit [IsQuasisimple G] in
private theorem prime_eq_three_of_center_card (hp : p.Prime)
    (hP : IsPGroup p (center G)) (hc : Nat.card (center G) = 3) : p = 3 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hd : 3 ∣ p ^ n := by rw [← hn, hc]
  have hdp := Nat.prime_three.dvd_of_dvd_pow hd
  exact ((Nat.dvd_prime hp).mp hdp).resolve_left (by decide) |>.symm

/-- Every odd-characteristic degree-three linear cover is excluded from
source Case II by its actual scalar center and the original A.2.14 witness. -/
public theorem linear_three_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {r e : ℕ} [Fact r.Prime]
    (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSL (G ⧸ center G) 3 (r ^ e)) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨iso⟩⟩ := model
  have hFo : Odd (Nat.card F) := hcard ▸ hr.pow
  have h2 : Nat.card F ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hFo)
  have h4 : Nat.card F ≠ 4 := fun hh => (by decide : ¬ Odd 4) (hh ▸ hFo)
  obtain ⟨hZ, hmod, _, _⟩ :=
    Matrix.PSL3.OrdinaryCenterRecognition.nontrivial_center_recognition h2 h4 iso
      (h.center_ne_bot ih.theoremA)
  have hp3 := prime_eq_three_of_center_card h.2.2.2.2.1 hP hZ
  subst p
  have hr2 : r ≠ 2 := fun hh => by subst r; exact (by decide : ¬ Odd 2) hr
  have hr3 : r ≠ 3 := by
    intro hh
    subst r
    have hd : 3 ∣ Nat.card F := hcard ▸ dvd_pow_self 3 (by omega)
    have hm := Nat.mod_eq_zero_of_dvd hd
    omega
  have hl := ClassicalRanks.NondefiningThree.threeRank_le_two_of_psl3_equiv
    iso hcard he hr2 hr3
  exact (not_le_of_gt (lemma_A_2_14_center h ih.theoremA hZ)) hl

/-- The ordinary odd PSL₂ universal cover has no nontrivial odd center.
The order-nine endpoint instead uses the actual PSL₂(9) ≃ A₆ comparison. -/
public theorem linear_two_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {q : ℕ} (hq : 3 < q) (ho : Odd q)
    (model : ClassicalGroup.IsPSL (G ⧸ center G) 2 q) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨iso⟩⟩ := model
  by_cases h9 : Nat.card F = 9
  · exact h.not_alternating_centralQuotient ih.theoremA hP (by decide : 5 ≤ 6)
      (iso.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 h9))
  let : Fact (3 < Nat.card F) := ⟨hcard ▸ hq⟩
  have hodd : Odd (Nat.card F) := hcard ▸ ho
  let c := centralQuotientCover iso
  let d : Covering G PSL(2,F) := c.toCovering
  have hu := GorensteinWalter.PSL2Cover.isUniversal_of_odd F hodd h9
  have hfac : c.toMonoidHom.comp (hu.lift d).toMonoidHom =
      (GorensteinWalter.PSL2Cover.cover F).toMonoidHom :=
    congrArg Covering.toMonoidHom (hu.lift_fac d)
  have hdvd : Nat.card (center G) ∣ 2 := by
    have hd := kernel_card_dvd_of_surjective_factor
      (GorensteinWalter.PSL2Cover.cover F).toMonoidHom c.toMonoidHom
      (hu.lift d).toMonoidHom (hu.lift d).surjective hfac
    have htwo : Nat.card (GorensteinWalter.PSL2Cover.cover F).toMonoidHom.ker = 2 :=
      GorensteinWalter.sl2ProjectiveProjection_ker_card F hodd
    simpa only [htwo, c, centralQuotientCover_ker] using hd
  have hoZ : Odd (Nat.card (center G)) := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact h.2.2.2.2.2.1.pow
  have hcard1 : Nat.card (center G) = 1 := Nat.eq_one_of_dvd_coprimes
    hoZ.coprime_two_right dvd_rfl hdvd
  exact h.center_ne_bot ih.theoremA ((center G).eq_bot_of_card_eq hcard1)
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
