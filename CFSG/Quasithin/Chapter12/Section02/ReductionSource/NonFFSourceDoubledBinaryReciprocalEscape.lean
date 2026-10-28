module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.LinearThree
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryOddAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPairGeneration

/-!
# Reciprocal escape for the original doubled binary orbit

The natural three-space marking identifies the literal component two-core
quotient with SL₃(2). The original odd actor therefore satisfies the binary
linear-three reciprocal escape theorem. The residual cover and the pushing-up
relation place the entire natural-plus-dual orbit in the core of the same
selected witness; the core also lies in the original section centralizer.

The seed and the doubled orbit remain distinct. These results supply the
escape input for C.4.8 and do not assert the later module-forcing contradiction.
Source: Aschbacher--Smith 4.2.5--13 and 4.4.3--6, printed pp.609--620.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Representation Representation.BinaryOffender
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original binary doubled marking supplies reciprocal escape on the seed.
The actor centralizes the whole orbit, and the seed remains distinct from it. -/
theorem sourceOrbit_binary_reciprocal_escape_of_not_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    EscapeCase L V A := by
  obtain ⟨t,ht,hnt,q,hq,hker,E,hE,hV,hVt⟩ :=
    D.sourceOrbit_binary_quotient_coordinates h hd F hF hmodel
  let b : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  let e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* Matrix.PSL3Two.PSL :=
    centerQuotientCongr b
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf
      (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))
  have hM := D.doubledNormalizer_unique h
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  exact linearThree_escape_case_of_not_unique h.toHypothesis1221 D hu e A hc.1 hc.2 ho
    ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V (T : Subgroup G)))) hnot

/-- The whole doubled orbit lies in the core of the very same reciprocal
escape witness; it is not identified with the original three-dimensional seed. -/
theorem sourceOrbit_binary_reciprocal_escape_witness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H W : Subgroup G, Witness L V A J H W ∧
      D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L ∧
      ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
        (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H := by
  obtain ⟨J,H,W,hw,hescape⟩ :=
    D.sourceOrbit_binary_reciprocal_escape_of_not_unique h hd F hF hmodel A hAC ho hnot
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf
      (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  obtain ⟨hc,_,hW,hne⟩ := D.doubledOrbit_oddActorResidual_cover h A hA ho
  have hI := ((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer
  obtain ⟨hs,_⟩ := coveringOvergroup_eta L.le_normalizer le_rfl hI hc.subset hne
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hNL : (L.subgroupOf (normalizer (L : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  have hperfect : IsPPerfect 2 L := by
    intro N hN hp
    let := hN
    have he : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hp.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  refine ⟨J,H,W,hw,?_,?_,hescape⟩
  · rw [D.sourceOrbit_eq]
    exact hW.trans hw.2.1.1
  · exact core_le_sectionCentralizer_of_eta L.le_normalizer hNL hperfect hs.1 hw.1.1.1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
