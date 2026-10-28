module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeFixedFactorPair
public import Theory.GroupTheory.CommutatorPreimage

/-!
# No fixed-factor error in the actual opposed quadratic action

Let F be the whole original component-fixed factor and E = Fᵍ its
opposed factor. Their disjointness and S-normality show that [A,E] lies
in E, is disjoint from F, and is centralized by E, for every A ≤ S.
Consequently centralization modulo F already lifts to
actual centralization. The final source theorem applies this to both the
original commutator core Q and the literal point kernel N = O₂(C_G(z)).

This controls the fixed-factor part of the kernel on the original groups.
It does not bound displacement modulo the larger moving layer, assert that
E escapes O₂(LS), or exclude any of the surviving finite carriers.

Source: Aschbacher--Smith15.3.7--8,15.3.12 and15.3.23, pp.1122--1129;
MS93 (4.5), pp.895--900.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

omit [Finite G] in
private theorem fixed_preimage_eq_of_disjoint_displacement
    (A D E F : Subgroup G) (hAD : ⁅A,D⁆ ≤ E) (hdis : Disjoint E F)
    (hAF : A ≤ normalizer (F : Set G)) :
    commutatorPreimage A D F = A ⊓ centralizer (D : Set G) := by
  apply le_antisymm
  · apply le_inf (commutatorPreimage_le _ _ _)
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    exact (le_inf ((commutator_mono (commutatorPreimage_le _ _ _) le_rfl).trans hAD)
      (commutator_commutatorPreimage_le A D F hAF)).trans hdis.eq_bot.le
  · apply le_commutatorPreimage inf_le_left
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le

/-- The opposed-factor double commutator vanishes for every subgroup
of S. For every subgroup of the actor, including each involution, centralization
modulo F has no hidden displacement. -/
theorem coreFixed_opposed_action
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S)
    (A : Subgroup G) (hAS : A ≤ d.S) :
    let F := coreFixed L
    let E := F.conjBy g
    E ≤ d.S ∧ ⁅A,E⁆ ≤ E ∧ ⁅⁅A,E⁆,E⁆ = ⊥ ∧ Disjoint ⁅A,E⁆ F ∧
      ∀ D : Subgroup G, D ≤ E →
        commutatorPreimage A D F = A ⊓ centralizer (D : Set G) := by
  let F := coreFixed L
  let E := F.conjBy g
  obtain ⟨hdis,_,hW,_,hWS,_,_⟩ :=
    coreFixed_conjugate_pair d L e h hg b t common earlier g hgT hgS
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hi)
  have hSa : d.S.map (MulAut.conj g).toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (hTS hgT)
  have hSF : d.S ≤ normalizer (F : Set G) :=
    hg.component_normalized.trans (Extension.SourceCases.FixedFour.coreFixed_normalized L)
  have hSE : d.S ≤ normalizer (E : Set G) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hSF
    rwa [hSa,map_equiv_normalizer_eq] at hh
  have hAE : ⁅A,E⁆ ≤ E :=
    le_normalizer_iff_commutator_le_right.mp (hAS.trans hSE)
  let : IsElementaryAbelian 2 (F ⊔ E : Subgroup G) := hW
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.of_injective
      (inclusion (show E ≤ F ⊔ E from le_sup_right)) (inclusion_injective _)
  have hEE : E ≤ centralizer (E : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact ⟨le_sup_right.trans hWS,hAE,
    commutator_eq_bot_iff_le_centralizer.mpr (hAE.trans hEE),
    hdis.symm.mono_left hAE,
    fun D hDE => fixed_preimage_eq_of_disjoint_displacement A D E F
      ((commutator_mono le_rfl hDE).trans hAE) hdis.symm (hAS.trans hSF)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.CoreActions LinearThree.Extension.SourceCases
open LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- At the original full-Sylow point, the same opposed whole factor has
quadratic action and exact fixed-point lifting on both Q and O₂(C_G(z)). -/
theorem binary_three_source_opposed_fixed_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let Q := LinearThree.commutatorCore c.L
    let N := (centralizer ({z} : Set G)).pCoreIn 2
    let F := coreFixed c.L
    let E := F.conjBy g
    E ≤ d.S ∧ ⁅Q,E⁆ ≤ Q ⊓ E ∧ ⁅N,E⁆ ≤ N ⊓ E ∧
      ⁅⁅Q,E⁆,E⁆ = ⊥ ∧ ⁅⁅N,E⁆,E⁆ = ⊥ ∧
      Disjoint ⁅Q,E⁆ F ∧ Disjoint ⁅N,E⁆ F ∧
      ∀ D : Subgroup G, D ≤ E →
        commutatorPreimage Q D F = Q ⊓ centralizer (D : Set G) ∧
        commutatorPreimage N D F = N ⊓ centralizer (D : Set G) := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  let Q := LinearThree.commutatorCore c.L
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let F := coreFixed c.L
  let E := F.conjBy g
  have hQS : Q ≤ d.S := commutatorCore_le_S d c.L h.core_le h.radical
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  obtain ⟨hES,hQE,hQQE,hQF,hQfix⟩ :=
    coreFixed_opposed_action d c.L eSL h hg b t common earlier g hgT hgS Q hQS
  obtain ⟨_,hNE,hNNE,hNF,hNfix⟩ :=
    coreFixed_opposed_action d c.L eSL h hg b t common earlier g hgT hgS N hNS
  have hSQ : d.S ≤ normalizer (Q : Set G) :=
    hg.component_normalized.trans (normalizer_le_normalizer_commutatorCore c.L)
  have hSN : d.S ≤ normalizer (N : Set G) :=
    le_sup_right.trans (hLS.trans (C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (pCore 2 C))))
  exact ⟨hES,
    le_inf (le_normalizer_iff_commutator_le_left.mp (hES.trans hSQ)) hQE,
    le_inf (le_normalizer_iff_commutator_le_left.mp (hES.trans hSN)) hNE,
    hQQE,hNNE,hQF,hNF,fun D hDE => ⟨hQfix D hDE,hNfix D hDE⟩⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
