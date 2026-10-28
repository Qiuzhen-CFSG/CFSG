module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNinePartner
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialAmbient

/-!
# Original fixed-normalizer control in the Nine row

The actual Nine action gives the pair of maximal two-locals. Thompson-center
escape then places the fixed-subgroup normalizer in the partner, without
using the residual conclusion of 15.1.14. Consequently all three normalizer
inclusions of 15.1.14 follow independently in this row.

For the full chosen module, the partner is C_G(Z), and its intersection
with M is the action kernel times T. This intersection is strictly smaller
than the fixed-subgroup normalizer. The remaining residual conclusion is
equivalent to equality of that normalizer with the partner; it is not
assumed or concluded here.

Source: Aschbacher--Smith 15.1.13--14, printed pp.1090--1091.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The three original normalizer inclusions follow in the Nine row without
the residual-centralization conclusion of 15.1.14. -/
theorem PreparedChosenModule.nine_fixed_normalizer_controls
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : PreparedChosenModule T M V)
    (h9 : letI := hp.elementary
      SourceCases.Nine (imageRepresentation M V hp.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict)) :
    M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
        normalizer (thompsonFixed T V : Set G) ∧
      normalizer (thompsonFixed T V : Set G) ≤ Mc ∧
      normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc := by
  let := hp.elementary
  have hpair := hp.nine_maximal_overgroups hG T hempty hM hJ hu h9
  have hNM := hp.thompsonFixed_normalizer_le_of_maximal_overgroups_pair
    hG T hempty hM hmany hJ hpair
  have hn : M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
      normalizer (thompsonFixed T V : Set G) :=
    (le_inf (inf_le_left.trans hp.normalized)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  have hr := chosen_twoRank_gt_one_of_quadraticRatio_two T hM.1.2 hp.le_selected
    hp.normalized hp.quadratic_ratio
  have hJJ : ChapterB.thompsonJ (T : Subgroup G) 0 ≤
      ChapterB.thompsonJ (T : Subgroup G) 1 :=
    ChapterB.lemma_B_2_3_1 _ (by omega : 0 ≤ 1) hr
  have he := ChapterB.lemma_B_2_3_3 (T : Subgroup G)
    (ChapterB.thompsonJ (T : Subgroup G) 1) (by omega : 0 < ChapterB.twoRank (T : Subgroup G))
    hJJ (ChapterB.thompsonJ_le _ _)
  rw [ChapterB.thompsonJ_zero,ChapterB.thompsonJ_zero] at he
  have hJM : normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M := by
    apply le_trans ?_ (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
    rw [he]
    exact normalizer_le_normalizer_elementaryAbelianMaxJ _
  exact ⟨hn,hNM,le_inf hJM ((le_inf hJM le_rfl).trans (hn.trans hNM))⟩

/-- The full Nine row places the literal fixed normalizer above the partner
intersection, with strictness supplied by the original Thompson-center escape.
Its equality with the partner is precisely the remaining residual assertion. -/
theorem PreparedChosenModule.nine_fixed_normalizer_interval
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hp : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (h9 : letI := hp.elementary
      SourceCases.Nine (imageRepresentation M V hp.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict)) :
    M ⊓ Mc < normalizer (thompsonFixed T V : Set G) ∧
      normalizer (thompsonFixed T V : Set G) ≤ Mc ∧
      ((pResidual 2 (centralizer (centralInvolutions T : Set G))).map
          (centralizer (centralInvolutions T : Set G)).subtype ≤
            centralizer (thompsonFixed T V : Set G) ↔
        normalizer (thompsonFixed T V : Set G) = Mc) := by
  obtain ⟨hMc,hI,hIT⟩ := hp.nine_partner_centralizer hG T hempty hM hJ hu hne hfull h9
  have hcontrol := hp.nine_fixed_normalizer_controls hG T hempty hM hmany hJ hu h9
  have hTN : (T : Subgroup G) ≤ normalizer (thompsonFixed T V : Set G) :=
    (le_inf hM.1.2 (ChapterB.le_normalizer_thompsonJ _ _)).trans hcontrol.1
  have hIN : M ⊓ Mc ≤ normalizer (thompsonFixed T V : Set G) := by
    rw [hI,hIT]
    exact sup_le
      (inf_le_right.trans ((centralizer_le inf_le_left).trans
        (Subgroup.centralizer_le_normalizer _))) hTN
  have hnot : ¬ normalizer (thompsonFixed T V : Set G) ≤ M := by
    intro hn
    exact (hp.source_thompson_escape_and_movement hG T hempty hM hmany hJ).1
      ((Subgroup.centralizer_le_normalizer _).trans
        ((hp.thompsonCenter_normalizer_le_fixed_normalizer hG T hM hJ).trans hn))
  refine ⟨lt_of_le_of_ne hIN (fun he => hnot (he.symm.le.trans inf_le_left)),hcontrol.2.1,?_⟩
  rw [hp.thompsonFixed_residual_iff_normalizes hG T hM hJ,←hMc]
  constructor
  · intro hn
    exact le_antisymm hcontrol.2.1 hn
  · intro he
    exact he.symm.le

end CFSG.Quasithin.Chapter15.Section01
