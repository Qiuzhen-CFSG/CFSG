module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeCubicCentralizer

/-!
# The conjugate core survives in the original binary quotient

Let Q = [O₂(L), L] and take a in T outside S. The original index-two geometry
puts Qᵃ inside S and makes YS normalize it. Its image in the literal quotient
LS/O₂(LS) cannot vanish: vanishing is precisely the conjugate-core bound
which makes the nontrivial two-subgroup Q Qᵃ normalized by L and T, contrary
to the original unique maximal overgroup theorem.

The matrix-image consumer uses the original BinaryMS core projection, with
its proved kernel O₂(LS). It retains the actual subgroup and quotient map;
no splitting of L and no fixation of the intrinsic four is used.

Source: Aschbacher–Smith 15.3.23, printed pp.1128–1129, combined with the
original residual geometry and uniqueness statement 15.3.7.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every outside Sylow conjugate of the original commutator core survives
modulo the original overgroup two-core. -/
theorem binary_three_source_conjugate_core_nonvanishing
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (a : G) (ha : a ∈ (d.T : Subgroup G)) (haS : a ∉ d.S) :
    (LinearThree.commutatorCore c.L).conjBy a ≤ d.S ∧
      d.Y ⊔ d.S ≤ normalizer ((LinearThree.commutatorCore c.L).conjBy a : Set G) ∧
      ¬ (LinearThree.commutatorCore c.L).conjBy a ≤ (c.L ⊔ d.S).pCoreIn 2 := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  let := hW
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hi)
  have hSa : d.S.map (MulAut.conj a).toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (hTS ha)
  have hTY : (d.T : Subgroup G) ≤ normalizer (d.Y : Set G) :=
    d.sylow_le.trans (OutsideStructure.LocalBranches.m_normalizes_y d)
  have hYa : d.Y.map (MulAut.conj a).toMonoidHom = d.Y :=
    mem_normalizer_iff_map_conj_eq.mp (hTY ha)
  have hYQ : d.Y ⊔ d.S ≤ normalizer (LinearThree.commutatorCore c.L : Set G) := by
    apply (sup_le ?_ hg.component_normalized).trans (normalizer_le_normalizer_commutatorCore c.L)
    rw [← hg.first_choice]
    exact h.normalizes_component
  have hQa : (LinearThree.commutatorCore c.L).conjBy a ≤ d.S := by
    have hh := map_mono (f := (MulAut.conj a).toMonoidHom)
      (commutatorCore_le_S d c.L h.core_le h.radical)
    rwa [hSa] at hh
  have hYQa : d.Y ⊔ d.S ≤ normalizer ((LinearThree.commutatorCore c.L).conjBy a : Set G) := by
    have hh := map_mono (f := (MulAut.conj a).toMonoidHom) hYQ
    rw [Subgroup.map_sup, hYa, hSa, map_equiv_normalizer_eq] at hh
    exact hh
  refine ⟨hQa, hYQa, ?_⟩
  intro hbound
  have hC : centralizer (d.V : Set G) ≤ d.M :=
    (Subgroup.centralizer_le_normalizer _).trans
      (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).ge
  have hunique := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action
    hM hu hmany hne).2.2.2.2.1
  exact contradiction_of_conjugate_core_control d c hi h.radical h.core_le hC
    hg.component_normalized hg.generation a ha haS (hg.exchange a ha haS) (Or.inr hbound) hunique

/-- The surviving image is a literal two-subgroup of SL₃(2), normalized by
the original residual and Sylow images. -/
theorem binary_three_source_conjugate_core_image
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
    (a : G) (ha : a ∈ (d.T : Subgroup G)) (haS : a ∉ d.S) :
    let N := (((LinearThree.commutatorCore c.L).conjBy a).subgroupOf (c.L ⊔ d.S)).map
      b.coreProjection
    N ≠ ⊥ ∧ IsPGroup 2 N ∧
      ((d.Y ⊔ d.S).subgroupOf (c.L ⊔ d.S)).map b.coreProjection ≤
        normalizer (N : Set Matrix.PSL3Two.SL) ∧
      N ≤ (d.S.subgroupOf (c.L ⊔ d.S)).map b.coreProjection := by
  dsimp only
  let J := c.L ⊔ d.S
  let Q := (LinearThree.commutatorCore c.L).conjBy a
  let N := (Q.subgroupOf J).map b.coreProjection
  obtain ⟨hQS,hNQ,hQK⟩ := binary_three_source_conjugate_core_nonvanishing
    hG d hempty hM hu hmany hI htwo hf c e a ha haS
  have hQJ : Q ≤ J := hQS.trans le_sup_right
  have hpQ : IsPGroup 2 Q := d.T.isPGroup'.to_le (hQS.trans inf_le_left)
  have hN0 : N ≠ ⊥ := by
    intro hN
    apply hQK
    intro q hq
    have hq1 : b.coreProjection ⟨q,hQJ hq⟩ = 1 := by
      exact hN.le (mem_map_of_mem b.coreProjection (show (⟨q,hQJ hq⟩ : J) ∈ Q.subgroupOf J from hq))
    have hk : (⟨q,hQJ hq⟩ : J) ∈ pCore 2 J := by
      rw [← b.coreProjection_kernel]
      exact hq1
    exact mem_map_of_mem J.subtype hk
  refine ⟨hN0, hpQ.comap_subtype.map b.coreProjection, ?_, map_mono (subgroupOf_mono J hQS)⟩
  apply le_normalizer_iff.mpr
  rintro _ ⟨x,hx,rfl⟩ _ ⟨q,hq,rfl⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  exact mem_map_of_mem b.coreProjection ((hNQ hx q).mp hq)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
