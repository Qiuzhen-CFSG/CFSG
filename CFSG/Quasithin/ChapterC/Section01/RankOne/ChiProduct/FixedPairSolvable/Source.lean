module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann.Source

/-!
# Fixed-pair C.1.28 for every solvable canonical action

Choose a full-Sylow minimal parabolic escaping the control of the original
universal pair. The restricted canonical action remains solvable. The normal
Baumann argument handles both the single and paired cases in that minimal
parabolic; C.1.27 lifts its same moving A₃ block to the original group.

No abelian-image assumption, local pair, factor marker, local-class premise,
subnormality premise or two-group action-kernel assumption remains.
Source: Aschbacher--Smith C.1.28 and 14.1.11, printed pp.133,978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable
open ChapterB GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

theorem exists_moving_alternatingThree_of_fixed_pair_escape
    (T : Sylow 2 G) (hfit : generalizedFitting G = pCore 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u})
    (hproper : control T D ≠ ⊤) (hrank : primeRank 3 G ≤ 2)
    (hsolv : Group.IsSolvable (G ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))) :
    ∃ A : Subgroup G, IsBlock A ∧ IsAlternatingBlock A 3 ∧
      A = ⁅A,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU A).map A.subtype = ⁅normalClosure
        (omegaOneCenterAmbient (T : Subgroup G) : Set G),A⁆ ∧
      ⁅normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G),A⁆ ≠ ⊥ := by
  obtain ⟨H,hTH,hP,hout⟩ := exists_minimalParabolic_outside T D hproper
  have hc := (ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit
  have hcH := centralizer_pCore_le_of_pCore_le H hc
    ((pCore_isPGroup.le_sylow_of_normal T).trans hTH)
  let U := normalClosure (omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H)
  have hmap := omegaClosure_map_le T H hTH
  have hsH := solvable_local_action _ H U hmap hsolv
  obtain ⟨K,hb,ha,hm,hu,_⟩ := NormalBaumann.minimal_parabolic_moving_alternatingThree_of_fixed_pair_escape
    (T.subtype hTH) hP ((ChapterA.generalizedFitting_eq_pCore_iff 2).mpr hcH)
    (subtypePair T D H hTH) (subtypePair_universal T D hD H hTH)
    (subtypePair_control_ne_top T D H hTH hout)
    ((Theory.GroupTheory.primeRank_le_of_injective 3 H.subtype H.subtype_injective).trans hrank) hsH
  refine ⟨K.map H.subtype,?_⟩
  apply Ambient.local_alternatingThree_maps_to_ambient T hc H hTH K hb ha hm
  · exact (map_mono (f := H.subtype) (hu.le.trans (commutator_le_left U _))).trans hmap
  · exact hsolv
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable
