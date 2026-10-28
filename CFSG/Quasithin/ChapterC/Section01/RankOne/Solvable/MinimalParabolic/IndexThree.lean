module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Stellmacher.UniqueMaximalContainingMap
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The order-twelve residual of a solvable minimal parabolic of index three

The native solvable pushing-up factors have elementary four-cores and cubic
quotients. At Sylow index three, any one factor has index a power of two,
so its subnormality forces it to contain the entire two-residual. Thus the
original residual is itself an alternating-three block, with the literal
four-core and cubic quotient retained.

Source: Aschbacher--Smith C.1.29, applied in F.6.13, printed pp.133,307;
Stellmacher (2.4), as formalized in the native solvable minimal-parabolic API.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem perfect_le_subnormal_index_two_power
    (L N : Subgroup G) (hL : IsPPerfect 2 L) (hN : N.IsSubnormal) :
    (∃ n, N.index ∣ 2 ^ n) → L ≤ N := by
  induction hN with
  | top => intro _; exact le_top
  | step N K hNK _ hnormal ih =>
    rintro ⟨n, hn⟩
    have hLK : L ≤ K := ih ⟨n, (index_dvd_of_le hNK).trans hn⟩
    let := hnormal
    have hp : IsPGroup 2 (K ⧸ N.subgroupOf K) :=
      IsPGroup.of_card_dvd_pow ((relIndex_dvd_index_of_le hNK).trans hn)
    have hf := hL.hom_eq_one_of_isPGroup hp
      ((QuotientGroup.mk' (N.subgroupOf K)).comp (inclusion hLK))
    intro x hx
    exact (QuotientGroup.eq_one_iff (inclusion hLK ⟨x, hx⟩)).mp
      (congrArg (fun f => f ⟨x, hx⟩) hf)

theorem index_three_residual
    (h : SectionTwo.Hypotheses G) (S : Sylow 2 G)
    (hi : (S : Subgroup G).index = 3)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal) :
    IsElementaryAbelian 2 (pCore 2 (pResidual 2 G)) ∧
      Nat.card (pCore 2 (pResidual 2 G)) = 4 ∧
      Nat.card (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) = 3 ∧
      ChapterC.IsBlock (pResidual 2 G) ∧ ChapterC.IsAlternatingBlock (pResidual 2 G) 3 := by
  classical
  have hco := isCoatom_of_index_three (S : Subgroup G) hi
  have hu : IsUniqueMaximalContaining (S : Subgroup G) ⊤ := by
    apply (uniqueMaximalContaining_top_iff _).mpr
    refine ⟨S, hco, le_rfl, ?_⟩
    intro M hM hSM
    exact ((hco.le_iff).mp hSM).resolve_left hM.ne_top
  let : (SectionTwo.vSubgroup S).Normal := normalClosure_normal
  let : (SectionTwo.cSubgroup S).Normal :=
    inferInstanceAs (centralizer (SectionTwo.vSubgroup S : Set G)).Normal
  let q := QuotientGroup.mk' (SectionTwo.cSubgroup S)
  have hq := QuotientGroup.mk'_surjective (SectionTwo.cSubgroup S)
  have hker : q.ker = SectionTwo.cSubgroup S := QuotientGroup.ker_mk' _
  let := SectionTwo.quotientConjugationAction S q hq hker
  obtain ⟨d⟩ := ChapterC.RankOne.Solvable.MinimalParabolic.exists_nativeData S q hq h hker hP hu
  change ChapterC.RankOne.Solvable.MinimalParabolic.ActualData S q hq hker at d
  have hex : ∃ i : Fin d.n, ¬ d.residualFactor i ≤ (S : Subgroup G) := by
    by_contra! hh
    have hr : pResidual 2 G ≤ (S : Subgroup G) := by
      rw [← d.iSup_residualFactor]
      exact iSup_le hh
    have htop := pResidual_sup_sylow_eq_top S
    rw [sup_eq_right.mpr hr] at htop
    have hone := index_eq_one.mpr htop
    omega
  obtain ⟨i, _⟩ := hex
  have hc : Nat.card (d.residualFactor i) = 12 := by
    have hh := (pCore 2 (d.residualFactor i)).index_mul_card
    change Nat.card (d.residualFactor i ⧸ pCore 2 (d.residualFactor i)) * _ = _ at hh
    rw [d.factor_core_card h i, d.factor_quotient_card h i] at hh
    exact hh.symm
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  have hcard : Nat.card G = 3 * 2 ^ n := by
    rw [← (S : Subgroup G).index_mul_card, hi, hn]
  have hindex : (d.residualFactor i).index ∣ 2 ^ n := by
    have hh := (d.residualFactor i).index_mul_card
    rw [hc, hcard] at hh
    exact ⟨4, by omega⟩
  have he : d.residualFactor i = pResidual 2 G := le_antisymm (d.residualFactor_le i)
    (perfect_le_subnormal_index_two_power _ _ (isPPerfect_pResidual 2)
      (d.residualFactor_subnormal i) ⟨n, hindex⟩)
  obtain ⟨hb, ha⟩ := ChapterC.RankOne.Solvable.MinimalParabolic.block_of_subnormal_elementary_four_core
    (d.residualFactor i) (d.residualFactor_subnormal i) (d.residualFactor_twoPerfect i)
    (d.factor_core_elementary h i) (d.factor_core_card h i) (d.factor_quotient_card h i)
  rw [← he]
  exact ⟨d.factor_core_elementary h i, d.factor_core_card h i, d.factor_quotient_card h i, hb, ha⟩
end CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic
