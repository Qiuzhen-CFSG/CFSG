module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveContracts
public import Theory.GroupTheory.PrimeRankCoprimeIndex
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder

/-!
# Degree recognition for the four small nonblock quotient models

The literal secondary projection has a binary PSL₂ quotient, so its order
is divisible by 2ⁿ(2²ⁿ−1) and every odd-prime rank is at most one. The orders
of J₁ and PSL₃(5) therefore force n=2 directly. For PSL₃(4) and PSU₃(5), the
orders leave n=3 as the only extra possibility. That would give a secondary
projection of index prime to three. Its cubic rank would then equal the full
quotient's cubic rank, contradicting the concrete rank-two witnesses.

All four degree clauses in the small-model part of 4.3.16 are thus recovered
from the actual models. Generation then excludes the two odd rows, and the
existing source outer-action argument applies to the two exceptional models.
The classification of the remaining Theorem C models into the source rows is
still required; the final theorem here retains the four actual models as an
explicit premise, and does not assert that inspection.
Source: Aschbacher--Smith, 4.3.12--16, printed pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The binary rank-one order on the literal projected secondary quotient. -/
theorem SecondaryActionData.secondaryProjection_quotient_card (s : SecondaryActionData c n) :
    Nat.card ((SourceImages.secondaryProjection c s.component s.secondary_le).range ⧸
      pCore 2 (SourceImages.secondaryProjection c s.component s.secondary_le).range) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := SourceImages.secondaryProjection_model c s.component
    s.secondary_le s.secondary_model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  rw [Nat.card_congr (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup, hF]

/-- The actual secondary quotient is a section of the full component quotient. -/
theorem SecondaryActionData.secondary_order_dvd_full_quotient (s : SecondaryActionData c n) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card (s.component ⧸ pCore 2 s.component) := by
  let B := (SourceImages.secondaryProjection c s.component s.secondary_le).range
  rw [←SecondaryActionData.secondaryProjection_quotient_card s]
  exact (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card

/-- Every odd-prime rank of the literal secondary projection is at most one. -/
theorem SecondaryActionData.secondaryProjection_odd_primeRank_le_one
    (s : SecondaryActionData c n) {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (SourceImages.secondaryProjection c s.component s.secondary_le).range ≤ 1 := by
  let B := (SourceImages.secondaryProjection c s.component s.secondary_le).range
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := SourceImages.secondaryProjection_model c s.component
    s.secondary_le s.secondary_model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  rw [←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 B) pCore_isPGroup,
    primeRank_congr p (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm)]
  exact Matrix.SL2.binary_odd_primeRank_le_one ho

/-- Cubic rank two and a cube-free cubic part rule out a secondary section
whose order is divisible by nine. The index argument uses the actual projection. -/
theorem SecondaryActionData.nine_not_dvd_secondary_order
    (s : SecondaryActionData c n)
    (h27 : ¬ 27 ∣ Nat.card (s.component ⧸ pCore 2 s.component))
    (hr : 2 ≤ primeRank 3 (s.component ⧸ pCore 2 s.component)) :
    ¬ 9 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  let B := (SourceImages.secondaryProjection c s.component s.secondary_le).range
  intro hd
  have hB : 9 ∣ Nat.card B := by
    rw [←SecondaryActionData.secondaryProjection_quotient_card s] at hd
    exact hd.trans (card_quotient_dvd_card (pCore 2 B))
  have hi : ¬ 3 ∣ B.index := by
    intro hi
    have hh := Nat.mul_dvd_mul hB hi
    rw [B.card_mul_index] at hh
    exact h27 hh
  have hb := SecondaryActionData.secondaryProjection_odd_primeRank_le_one s (p := 3) (by decide)
  change primeRank 3 B ≤ 1 at hb
  rw [B.primeRank_eq_of_not_dvd_index hi] at hb
  omega

/-- The Janko row of the actual quotient forces the original rank-one degree to be two. -/
theorem SecondaryActionData.degree_two_of_janko_model (s : SecondaryActionData c n)
    (hn : 1 < n) (e : (s.component ⧸ pCore 2 s.component) ≃* Janko1.Model) : n = 2 := by
  have hd := SecondaryActionData.secondary_order_dvd_full_quotient s
  rw [Nat.card_congr e.toEquiv, Janko1.card_model] at hd
  have hd2 : 2 ^ n ∣ 175560 := (dvd_mul_right _ _).trans hd
  have hb : n < 4 := by
    by_contra! hn4
    have hh := (Nat.pow_dvd_pow 2 hn4).trans hd2
    norm_num at hh
  interval_cases n <;> norm_num at *

/-- The PSL₃(5) row forces the original rank-one degree to be two. -/
theorem SecondaryActionData.degree_two_of_ternary_five_model (s : SecondaryActionData c n)
    (hn : 1 < n) (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 5) :
    n = 2 := by
  have hd := SecondaryActionData.secondary_order_dvd_full_quotient s
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective, hF] at hd
  norm_num at hd
  have hd2 : 2 ^ n ∣ 372000 := (dvd_mul_right _ _).trans hd
  have hb : n < 6 := by
    by_contra! hn6
    have hh := (Nat.pow_dvd_pow 2 hn6).trans hd2
    norm_num at hh
  interval_cases n <;> norm_num at *

/-- Both odd rows are excluded in every source degree above one. The degree-two
premise is derived from the literal projected section, not assumed. -/
theorem SecondaryActionData.not_odd_model_of_generation (s : SecondaryActionData c n)
    (hn : 1 < n) (hg : SecondaryActionData.ActionGeneration s)
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 5 ∨
      Nonempty ((s.component ⧸ pCore 2 s.component) ≃* Janko1.Model)) : False := by
  have hn2 : n = 2 := by
    rcases hm with hm | he
    · exact SecondaryActionData.degree_two_of_ternary_five_model s hn hm
    · exact SecondaryActionData.degree_two_of_janko_model s hn (Classical.choice he)
  exact SecondaryActionData.not_nonexceptional_of_generation s hn hg
    (Or.inr (Or.inr ⟨hn2, hm⟩))

/-- The linear exceptional quotient forces degree two without a model-inspection
parameter premise. Degree three contradicts its cubic rank and cubic part. -/
theorem SecondaryActionData.degree_two_of_linear_four_model (s : SecondaryActionData c n)
    (hn : 1 < n) (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4) :
    n = 2 := by
  have hcard : Nat.card (s.component ⧸ pCore 2 s.component) = 20160 := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective, hF]
    norm_num
  have hr : 2 ≤ primeRank 3 (s.component ⧸ pCore 2 s.component) := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    rw [primeRank_congr 3 e]
    exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective_of_three_dvd
      (by norm_num [hF])
  have h9 := SecondaryActionData.nine_not_dvd_secondary_order s (by rw [hcard]; decide) hr
  have hd := SecondaryActionData.secondary_order_dvd_full_quotient s
  rw [hcard] at hd
  have hd2 : 2 ^ n ∣ 20160 := (dvd_mul_right _ _).trans hd
  have hb : n < 7 := by
    by_contra! hn7
    have hh := (Nat.pow_dvd_pow 2 hn7).trans hd2
    norm_num at hh
  interval_cases n <;> norm_num at *

/-- The unitary exceptional quotient also forces the same original degree two. -/
theorem SecondaryActionData.degree_two_of_unitary_five_model (s : SecondaryActionData c n)
    (hn : 1 < n) (hm : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    n = 2 := by
  have hcard : Nat.card (s.component ⧸ pCore 2 s.component) = 126000 := by
    obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
    have hf : Nat.card {x : F // J.conj x = x} = 5 := by
      simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
        J.conj 5 1 (by decide) (by simpa only [pow_one] using hF)
          (by simpa only [pow_one] using hc)
    rw [Nat.card_congr e.toEquiv, Representation.SU3.BinaryDegree.card_projective J hF hf]
    norm_num
  have hr : 2 ≤ primeRank 3 (s.component ⧸ pCore 2 s.component) := by
    obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
    rw [primeRank_congr 3 e]
    exact Theory.SpecificGroups.SignedThreeCubicRank.unitary_projective_of_three_dvd J
      (by decide : Nat.Prime 5) hF hc (by decide)
  have h9 := SecondaryActionData.nine_not_dvd_secondary_order s (by rw [hcard]; decide) hr
  have hd := SecondaryActionData.secondary_order_dvd_full_quotient s
  rw [hcard] at hd
  have hd2 : 2 ^ n ∣ 126000 := (dvd_mul_right _ _).trans hd
  have hb : n < 5 := by
    by_contra! hn5
    have hh := (Nat.pow_dvd_pow 2 hn5).trans hd2
    norm_num at hh
  interval_cases n <;> norm_num at *

/-- The four small actual quotient models supply all their source degree clauses.
The two odd rows are then excluded by generation; the surviving models give
the original torus's outer-action clause on the literal full quotient. -/
theorem SecondaryActionData.exceptional_of_small_models
    {V : Subgroup G} (s : SecondaryActionData c n) (hn : 1 < n)
    (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hm : (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 5 ∨
      Nonempty ((s.component ⧸ pCore 2 s.component) ≃* Janko1.Model)) ∨
      (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∨
        ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)) :
    ExceptionalModel (s.component ⧸ pCore 2 s.component) n ∧
      SecondaryActionData.torusImage s ⊓
        MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ := by
  apply SecondaryActionData.exceptional_of_source_inputs s D h hn hg
  rcases hm with ho | he
  · exact (SecondaryActionData.not_odd_model_of_generation s hn hg ho).elim
  · refine Or.inr ⟨?_, he⟩
    rcases he with hl | hu
    · exact SecondaryActionData.degree_two_of_linear_four_model s hn hl
    · exact SecondaryActionData.degree_two_of_unitary_five_model s hn hu

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
