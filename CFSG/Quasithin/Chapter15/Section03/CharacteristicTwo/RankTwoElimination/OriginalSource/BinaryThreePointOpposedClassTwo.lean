module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCentralEight

/-!
# The actual opposed core has class at most two in the point quotient

The exchange carries the intrinsic four to the original moving plane.
That plane lies in the natural center commutator, hence in the center of
N=O2(C) in the binary carriers. The third commutator of Q^g is exactly
H^g, so its literal point image has trivial third commutator. The original
full quotient Sylow normalizes this same image. No containing-component
placement of the opposed image is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The same actual opposed core image is Sylow-normalized and has class at most two. -/
theorem binary_three_source_binary_opposed_class_two
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
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL K n 2)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let q := QuotientGroup.mk' (pCore 2 C)
    let Qg := (LinearThree.commutatorCore c.L).conjBy g
    let E := (intrinsicFour c.L).conjBy g
    let D := (Qg.subgroupOf C).map q
    let Sbar := (P : Subgroup C).map q
    E ≤ (center N).map N.subtype ∧ Qg ≤ d.S ∧ D ≤ Sbar ∧
      Sbar ≤ normalizer D ∧ ⁅⁅D,D⁆,D⁆ = ⊥ := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let q := QuotientGroup.mk' (pCore 2 C)
  let Q := LinearThree.commutatorCore c.L
  let Qg := Q.conjBy g
  let E := (intrinsicFour c.L).conjBy g
  let D := (Qg.subgroupOf C).map q
  have hEQ : E = movingPlane d c.L :=
    intrinsicFour_conjugate_eq_movingPlane_of_MS93 d c.L eSL h hg b t common earlier g hgT hgS
  have hUZ := movingPlane_le_coreCenter d c hg.component_normalized h.core_le h.radical
  have hYL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hEV : E ≤ ⁅coreCenter c.L,c.L⁆ := by
    rw [hEQ]
    obtain ⟨_,_,_,_,_,hmove,_,_⟩ := hg.coordinates
    rw [←hmove]
    exact commutator_mono hUZ hYL
  have hspan := binary_three_source_binary_central_eight_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hn hm
  have hEC : E ≤ (center N).map N.subtype := hEV.trans (hspan.2.2.1.trans hspan.2.2.2.1)
  have hQS : Q ≤ d.S := commutatorCore_le_S d c.L h.core_le h.radical
  have hSQ : d.S ≤ normalizer Q :=
    hg.component_normalized.trans (normalizer_le_normalizer_commutatorCore c.L)
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTS : (d.T : Subgroup G) ≤ normalizer d.S :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hi)
  have hSg : d.S.map (MulAut.conj g).toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (hTS hgT)
  have hQgS : Qg ≤ d.S := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hQS
    rwa [hSg] at hh
  have hSQg : d.S ≤ normalizer Qg := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hSQ
    rwa [hSg,map_equiv_normalizer_eq] at hh
  have hSC : d.S ≤ C := le_sup_right.trans hLS
  have hQgC : Qg ≤ C := hQgS.trans hSC
  have hPC : (P : Subgroup C) = d.S.subgroupOf C := by
    rw [←hP]
    exact (comap_map_eq_self_of_injective C.subtype_injective (P : Subgroup C)).symm
  have hQP : Qg.subgroupOf C ≤ (P : Subgroup C) := by rw [hPC]; exact comap_mono hQgS
  have hPD : (P : Subgroup C) ≤ normalizer (Qg.subgroupOf C) := by
    intro x hx y
    change ((y : G) ∈ Qg) ↔ ((x : G) * (y : G) * (x : G)⁻¹ ∈ Qg)
    exact mem_normalizer_iff.mp (hSQg (hP ▸ mem_map_of_mem C.subtype hx)) y
  have hgam : (⁅⁅Qg.subgroupOf C,Qg.subgroupOf C⁆,Qg.subgroupOf C⁆).map C.subtype = E := by
    rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hQgC]
    change ⁅⁅Q.map (MulAut.conj g).toMonoidHom,Q.map (MulAut.conj g).toMonoidHom⁆,
      Q.map (MulAut.conj g).toMonoidHom⁆ = _
    rw [←map_commutator,←map_commutator]
    rfl
  have hgamma : ⁅⁅D,D⁆,D⁆ = ⊥ := by
    rw [←map_commutator,←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    intro x hx
    have hm : (x : G) ∈ E := hgam ▸ mem_map_of_mem C.subtype hx
    have hxN : (x : G) ∈ N := map_subtype_le _ (hEC hm)
    change x ∈ pCore 2 C
    exact (comap_map_eq_self_of_injective C.subtype_injective (pCore 2 C)).le hxN
  exact ⟨hEC,hQgS,map_mono hQP,
    (map_mono hPD).trans (le_normalizer_map q),hgamma⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
