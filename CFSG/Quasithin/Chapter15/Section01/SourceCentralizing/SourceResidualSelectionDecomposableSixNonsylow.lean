module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.RankOneRadical

/-!
# The original radical is not Sylow in a surviving constrained component join

The literal radical Q₁ lies in the original centralizer Sylow S. If Q₁ were
Sylow in LQ₁, maximality applied to S_L Q₁ would put the full component
Sylow S_L in Q₁. The existing C.2.4 full-Sylow theorem would then make L an
L₂-even or alternating-five block. Thus the selected non-rank-one source
cannot supply an original-Sylow hypothesis for an A₆ reconstruction.

The argument applies to every original pre-exclusion source. It does not
use a Nine hypothesis, global residual centralization, or a six-point
quotient model.

Source: Aschbacher--Smith C.2.4(1), p.144, and 15.1.20, pp.1094--1095.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- Excluding the genuine rank-one blocks excludes Sylow membership of the
same original radical Q₁ in the same component join LQ₁. -/
theorem PreExclusionSource.not_original_radical_sylow_of_no_rankOne
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfit : generalizedFitting d.L = pCore 2 d.L)
    (hnot : ¬ ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5)) :
    ¬ Chapter1.IsSylowIn 2 d.Q1 (d.L ⊔ d.Q1) := by
  intro hSyl
  have hQS := d.catalogue_radical_le_sylow s.centralizer_sylow hu
  have he := (Chapter1.isSylowIn_iff.mp hSyl).2.2 (d.SL ⊔ d.Q1)
    (T.isPGroup'.to_le ((sup_le d.SL_le_S hQS).trans d.S_le_T))
    le_sup_right (sup_le (d.SL_le_L.trans le_sup_left) le_sup_right)
  exact hnot (s.constrained_rankOne_block_of_sylow_le_radical (h := h) hG hfit
    ((show d.SL ≤ d.SL ⊔ d.Q1 from le_sup_left).trans_eq he))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
