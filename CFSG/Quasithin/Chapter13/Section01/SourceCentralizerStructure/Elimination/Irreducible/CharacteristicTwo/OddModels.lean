module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.LinearThreeExclusion.EvenModels
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.StarTransport
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.SpecificGroups.OddThreeRank
public import Theory.SpecificGroups.SymplecticFour.DefiningRank
public import Theory.AtlasPort.LinearGroups.G2.LongRootPlaneLift
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear

public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.Preparation

/-!
# Excluding the odd linear-three quotient in the characteristic-two branch

The full C.2.7 star catalogue is incompatible with a central quotient PSL₃(p)
for an odd prime p > 3. Elementary two-ranks separate the nonbinary linear,
symplectic and G₂ rows; the remaining concrete orders separate the finite
rows. The actual central comparison between K/O₂(K) and K* transports this
exclusion without identifying either group with K.

The final theorem applies this comparison to the original escaping component.
No linear-three row, parabolic marking or model-sieve conclusion is assumed.
Source: Aschbacher–Smith, 13.1.12(3), p.875, and C.2.7, pp.145–147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.LinearThreeExclusion
open ChapterB.SourceInduction.ProjectiveLine ChapterC.C27Source

private def centerQuotientEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem odd_projective_rank {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hm : ClassicalGroup.IsPSL Q 3 p) :
    primeRank 2 Q ≤ 2 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [primeRank_equiv 2 e]
  exact Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le Fact.out ho hF

/-- Every group in the genuine B.5.1 star catalogue excludes an odd-prime
projective linear-three central quotient. No block or parabolic marking is used. -/
theorem star_model_not_odd_linear_three_center
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (ho : Odd p) (h : StarModels.Model A) :
    ¬ ClassicalGroup.IsPSL (A ⧸ center A) 3 p := by
  intro hm
  have hr := odd_projective_rank ho hm
  cases h with
  | linearTwo F e =>
    exact not_even_rankOne_model hp ho (Or.inr hm)
      ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,⟨centerQuotientEquiv e⟩⟩
  | linearThree F e =>
    exact not_even_projective_model hp ho hm
      ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,⟨centerQuotientEquiv e⟩⟩
  | symplectic F _ e =>
    have hl := Theory.SpecificGroups.SymplecticFour.DefiningRank.three_mul_fieldExponent_le_primeRank
      F.Carrier F.card_eq
    rw [← primeRank_equiv 2 (centerQuotientEquiv e)] at hl
    have := F.degree_pos
    omega
  | g2 F large e =>
    have hF : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr large
    let j : (A ⧸ center A) ≃* Atlas.G2.Model F.Carrier :=
      (centerQuotientEquiv e).trans
        ((QuotientGroup.quotientMulEquivOfEq
          (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hF)).trans
            QuotientGroup.quotientBot)
    rw [primeRank_equiv 2 j] at hr
    have hb := (primeRank_le_iff_elementary_card_le (Atlas.G2.Model F.Carrier)).mp hr
      Atlas.G2.longRootLocal Atlas.G2.LongRootPlaneLift.elementary
    rw [Atlas.G2.card_longRootLocal] at hb
    norm_num at hb
    nlinarith
  | g2DerivedTwo e =>
    have hcard : Nat.card A = 6048 := by
      rw [Nat.card_congr e.toEquiv,
        Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
      exact Atlas.G2.BinaryException.card_H
    exact not_linearThree_of_small_order hp
      ((Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (center A))).trans
        (by omega : Nat.card A ≤ 20160)) (Or.inr hm)
  | alternating n hn e =>
    have hlo : 5 ≤ n := by rcases hn with rfl | rfl | rfl | rfl <;> omega
    have hhi : n ≤ 8 := by rcases hn with rfl | rfl | rfl | rfl <;> omega
    have hcard : Nat.card A ≤ 20160 := by
      let : NeZero n := ⟨by omega⟩
      let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      interval_cases n <;> norm_num
    exact not_linearThree_of_small_order hp
      ((Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (center A))).trans
        hcard) (Or.inr hm)
  | linearFiveTwo e =>
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    rw [← Nat.card_congr (centerQuotientEquiv e).toEquiv] at hc
    norm_num [Fin.prod_univ_succ] at hc
    exact not_linearThree_of_large_exceptional_order hp (Or.inr hc) (Or.inr hm)
  | tripleSix _ e =>
    have hcard : Nat.card (A ⧸ center A) ≤ 20160 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      norm_num
    exact not_linearThree_of_small_order hp hcard (Or.inr hm)

/-- C.2.7 excludes the odd linear-three quotient through its literal central
comparison map, preserving the distinction between the quotient and star image. -/
theorem source_not_odd_linear_three
    {G : Type*} [Group G] [Finite G] {H R M K : Subgroup G}
    (h : SourceInterface.Input KnownSimple.IsKnownSimple H R M K)
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (ho : Odd p) :
    ¬ LinearThreeModel p (XiQuotient K) := by
  intro hm
  have hb := (kernel_offender_from_source h).1.upper
  have he := coreStarCenterEquiv h.normalizes h.quasisimple
    (starImage_ne_bot_of_bound h.normalizes h.quasisimple hb)
  exact star_model_not_odd_linear_three_center hp ho (star_model_from_source h)
    ((linearThree_center_model hm).of_mulEquiv he.symm)

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The literal C.2.7 source input excludes the odd quotient on K/O₂(K). -/
theorem Context.not_characteristic_two_odd_linear_three (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hf : generalizedFitting K = pCore 2 K) :
    ¬ LinearThreeModel p (XiQuotient K) := by
  have hp : 5 ≤ p := by
    have hh := h.prime_gt_three
    obtain ⟨k,hk⟩ := h.odd
    omega
  exact source_not_odd_linear_three (h.characteristic_two_input c s hnt e hi hf) hp h.odd

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
