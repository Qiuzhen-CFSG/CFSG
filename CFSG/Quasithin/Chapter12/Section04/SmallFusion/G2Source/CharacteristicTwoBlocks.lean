module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.HyperplanePreparation
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.CommutationSource
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.Generation
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.NormalBlockRank
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.SylowMaximal

/-!
# The literal residual block in the binary G₂ characteristic-two case

E.6.7 is applied inside the original escaping hyperplane centralizer, using
its actual Sylow subgroup C_T(V). A faithful cubic action makes the block
family a singleton. The original corank-one inequality excludes rank-one
blocks over larger fields, leaving the alternating-three and alternating-five
rows. The Thompson movement identity is retained for the local C.5.7 argument.

Source: Aschbacher--Smith, 12.4.8, printed p.815, and E.6.7, E.6.14,
printed pp.246--251.
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterB.QuasisimpleSource Atlas.G2.Natural
open ChapterE ChapterE.Section06 ChapterE.Section06.InvariantSubspaces
open ChapterE.Section06.InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V U : Subgroup G}

/-- The original G₂ hyperplane has one moved alternating block when its
centralizer has characteristic two and its cubic actor is faithful. -/
theorem cover_characteristicTwo_blockSelection_moved
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G))
    (hc : HasCharacteristicTwo (centralizer (U : Set G)))
    (ha : HasFaithfulThreeAction U) :
    ∃ J : Subgroup G, SingleBlock T (normalizer (V : Set G)) V U J ∧
      (ChapterC.IsAlternatingBlock J 3 ∨ ChapterC.IsAlternatingBlock J 5) ∧
      J = ⁅J, Stellmacher.elementaryAbelianMaxJ (sylowCentralizer (T : Subgroup G) V)⁆ := by
  have hE := cover_source_hypothesisE61 h D structural e hne
  have hU := (escaping_cover_subspaces h D structural e hne hUV hcor hescape).2.2.2.1
  have hSyl := hE.sylow_obstruction hU
  have hQH := (Chapter1.isSylowIn_iff.mp hSyl).2.1
  obtain ⟨d⟩ := e67Input_knownSimple hE U hU (centralizer (U : Set G)) hQH le_rfl hc
  have hcount := d.toBlockFamily.count_eq_one_of_faithful_three hE hU hc fixedNineInput ha
  let i : Fin d.count := ⟨0, by omega⟩
  have hi := faithfulIndexInput_of_commutation_and_quotient_rank
    conjugateChiZeroCommutationInput normalChiZeroQuotientRankInput hE U hU hc ha d hcount i
  have hr := chiZero_eq_primeToResidual_of_index (d.le i) (d.type i) (d.subnormal i) hi
  have hn : ((d.block i).subgroupOf (centralizer (U : Set G))).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    rw [hr]
    exact (centralizer (U : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (centralizer (U : Set G))
        (primeToResidual 3 (centralizer (U : Set G))))
  refine ⟨d.block i, ⟨d.le i, d.toBlockFamily.generated_of_count_eq_one hcount i,
    d.type i, hr, blockSylowMaximalInput _ _ _ hc hSyl (d.le i) hn (d.type i)⟩,
    ?_, d.thompson i⟩
  rcases d.type i with ⟨n, hn⟩ | hAlt
  · obtain ⟨X, _, _, _, _, _, _, _, _, hbound⟩ := d.rankOne i n hn
    have hge := hn.1
    rw [hcor] at hbound
    omega
  · exact hAlt

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
