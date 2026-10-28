module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic.Factors
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic.AlternatingThree

/-!
# An outside alternating-three block in a solvable minimal parabolic

Under the original Section Two hypotheses, characteristic-subgroup
obstruction and unique-maximal condition, the intrinsic residual factors
have elementary four-cores and cubic quotients. The proved natural-module
recognition makes them alternating-three blocks. Since the residual and
the original Sylow generate the group, one factor lies outside every proper
overgroup of that Sylow. Its J(S) marking and canonical-module support are
unchanged.

This is the local solvable input to the outside-block argument in
Aschbacher–Smith C.1.29, printed pp.132–134, using Stellmacher (2.4),
`refs/latex/stellmacher-n-group.tex`. The ambient extension and final Chapter
15 source application consume the same block; no new model or outside-block
premise occurs here.
-/

public section
namespace CFSG.Quasithin.ChapterC.RankOne.Solvable
open Subgroup Stellmacher MinimalParabolic
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original minimal parabolic contains an outside A₃ block with its
native support and its original elementary Thompson marking. -/
theorem exists_outside_alternatingThree_block
    (h : SectionTwo.Hypotheses G) (S : Sylow 2 G)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hu : IsUniqueMaximalContaining (S : Subgroup G) ⊤)
    (M : Subgroup G) (hSM : (S : Subgroup G) ≤ M) (hM : M < ⊤) :
    ∃ K : Subgroup G, ¬ K ≤ M ∧ IsBlock K ∧ IsAlternatingBlock K 3 ∧
      K = ⁅K, elementaryAbelianMaxJ (S : Subgroup G)⁆ ∧
      (blockU K).map K.subtype ≤ SectionTwo.vSubgroup S := by
  classical
  let : (SectionTwo.vSubgroup S).Normal := normalClosure_normal
  let : (SectionTwo.cSubgroup S).Normal :=
    inferInstanceAs (centralizer (SectionTwo.vSubgroup S : Set G)).Normal
  let q := QuotientGroup.mk' (SectionTwo.cSubgroup S)
  have hq := QuotientGroup.mk'_surjective (SectionTwo.cSubgroup S)
  have hker : q.ker = SectionTwo.cSubgroup S := QuotientGroup.ker_mk' _
  let := SectionTwo.quotientConjugationAction S q hq hker
  obtain ⟨d⟩ := exists_nativeData S q hq h hker hP hu
  change ActualData S q hq hker at d
  have hi : ∃ i : Fin d.n, ¬ d.residualFactor i ≤ M := by
    by_contra hh
    push Not at hh
    have hRM : pResidual 2 G ≤ M := by
      rw [← d.iSup_residualFactor]
      exact iSup_le hh
    have hgen : pResidual 2 G ⊔ (S : Subgroup G) = ⊤ := by
      rw [← twoResidualAmbient_top_eq_pResidual]
      exact twoResidualAmbient_top_sup_sylow S
    exact hM.ne (top_unique (hgen ▸ sup_le hRM hSM))
  obtain ⟨i, hi⟩ := hi
  obtain ⟨hb, ha⟩ := block_of_subnormal_elementary_four_core (d.residualFactor i)
    (d.residualFactor_subnormal i) (d.residualFactor_twoPerfect i)
    (d.factor_core_elementary h i) (d.factor_core_card h i) (d.factor_quotient_card h i)
  refine ⟨d.residualFactor i, hi, hb, ha, d.factor_commutator_thompson i, ?_⟩
  have hU : blockU (d.residualFactor i) ≤ pCore 2 (d.residualFactor i) :=
    commutator_le_left _ _
  have hm := map_mono (f := (d.residualFactor i).subtype) hU
  rw [d.factor_core_eq h i, map_subgroupOf_eq_of_le (d.support_le_factor h i)] at hm
  exact hm.trans (d.support_le_v i)

end CFSG.Quasithin.ChapterC.RankOne.Solvable
