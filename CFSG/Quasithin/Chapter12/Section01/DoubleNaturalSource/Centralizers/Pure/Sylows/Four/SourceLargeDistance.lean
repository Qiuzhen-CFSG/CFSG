module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.SourceCoreAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.Input
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightSmallDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightCoefficients
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.OriginalEarlier

/-!
# Excluding large critical distance at the original pure point

The original natural summand has displacement in the central point line.
The corrected MS93 small-displacement theorem makes this summand central in
the commutator core at large distance. The intrinsic component two-core
centralizes that full core center, contradicting the proved nontrivial action
of the original pure-point residual core on the natural summand.

Every large-distance path input is supplied by `OriginalEarlier.earlier`.
No fixation of the replacement's fixed factor by the original join core is
used. The exact nonabelian setup is retained; the distance-four branch is not
excluded by this module.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open ChapterC ChapterC.BinaryMS ChapterC.BinaryMS.MS93
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

private theorem centralizes_component_core_of_small_displacement
    {J : Type*} [Group J] [Finite J] {κ : GroupClass} {K R : Subgroup J}
    {input : Input κ K R} (t : InputSetup input)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    {A N : Subgroup J} (hA : A ≤ commutatorCore K) (hN : N ≤ commutatorCore K)
    (hcentral : N ≤ center J) (hcard : Nat.card N ≤ 2)
    (hcomm : ⁅A, commutatorCore K⁆ ≤ N) :
    A ≤ centralizer ((pCore 2 K).map K.subtype : Set J) := by
  have hfix := t.large_core_small_displacement common earlier hA hN hcentral hcard hcomm
  intro a ha l hl
  obtain ⟨l, hl, rfl⟩ := hl
  let q : commutatorCore K := ⟨a, hA ha⟩
  let u := input.intrinsicCoreEquiv.symm q
  have hu : ((u : K) : J) = a := by
    have hh := congrArg (fun z : commutatorCore K => (z : J))
      (input.intrinsicCoreEquiv.apply_symm_apply q)
    exact hh
  have huc : u ∈ center (blockU K) := by
    apply mem_center_iff.mpr
    intro v
    apply Subtype.ext
    apply K.subtype_injective
    change ((v : K) : J) * ((u : K) : J) = ((u : K) : J) * ((v : K) : J)
    rw [hu]
    exact hfix ha (input.intrinsicCoreEquiv v) (input.intrinsicCoreEquiv v).property
  have he := t.large_core_centralizes_center common earlier l hl ⟨u, huc⟩
  have he' := congrArg K.subtype he
  simp only [map_mul, map_inv] at he'
  change (l : J) * ((u : K) : J) * (l : J)⁻¹ = ((u : K) : J) at he'
  rw [hu] at he'
  exact mul_inv_eq_iff_eq_mul.mp he'

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- A genuine nonabelian MS setup on the original marked pure-point pair
cannot have critical distance greater than four. -/
theorem pure_binary_setup_distance_le_four
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (hms : SmallMSPair KnownSimple.IsKnownSimple (B.pointResidual w) (B.pointSylow w))
    (e : (B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : InputSetup (hms.binaryInput e))
    (hc : ¬ IsMulCommutative (commutatorCore
      ((B.pointResidual w).subgroupOf (B.pointResidual w ⊔ B.pointSylow w)))) :
    t.geometry.b t.reduction.radical ≤ 4 := by
  by_contra hb
  have hb' : 4 < t.geometry.b t.reduction.radical := Nat.lt_of_not_ge hb
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb'
  let X := B.pointResidual w
  let R := B.pointSylow w
  let J := X ⊔ R
  let K := X.subgroupOf J
  let A := B.naturalSummand
  let N := zpowers (w : G)
  let Q := commutatorCore K
  obtain ⟨hA, hdisp, hNcentral, hNcard⟩ :=
    S.pure_natural_msCore_small_displacement hNM hWT hTM w hw hp
  have hmap : Q.map J.subtype = msQ X R := binaryCore_map X R
  have hQJ : msQ X R ≤ J := hmap ▸ map_subtype_le _
  have hAJ : A ≤ J := hA.trans hQJ
  have hNJ : N ≤ J := hNcentral.trans inf_le_left
  have hNA : N ≤ A := zpowers_le.mpr ((B.mem_naturalSummand w).mpr hp)
  have hQ : (msQ X R).subgroupOf J = Q := by
    rw [← hmap]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hA₀ : A.subgroupOf J ≤ Q := by rw [← hQ]; exact comap_mono hA
  have hN₀ : N.subgroupOf J ≤ Q := (comap_mono hNA).trans hA₀
  have hcentral : N.subgroupOf J ≤ center J := by
    intro z hz
    apply mem_center_iff.mpr
    intro j
    exact Subtype.ext ((hNcentral hz).2 j j.property)
  have hcard : Nat.card (N.subgroupOf J) ≤ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNJ).toEquiv]
    exact hNcard.le
  have hQcore : msQ X R ≤ J.pCoreIn 2 := by
    rw [← hmap]
    exact map_mono (commutator_le_left _ _)
  have hcomm : ⁅A.subgroupOf J, Q⁆ ≤ N.subgroupOf J := by
    intro x hx
    have hh := mem_map_of_mem J.subtype hx
    rw [map_commutator, map_subgroupOf_eq_of_le hAJ, hmap] at hh
    exact ((commutator_mono le_rfl hQcore).trans hdisp) hh
  have hfix := centralizes_component_core_of_small_displacement t common earlier
    hA₀ hN₀ hcentral hcard hcomm
  apply S.pure_residual_core_moves_natural w hw hp
  intro a ha l hl
  obtain ⟨l, hl, rfl⟩ := hl
  let eK : K ≃* X := subgroupOfEquivOfLe le_sup_left
  let lK := eK.symm l
  have hlK : lK ∈ pCore 2 K := by
    rw [← pCore_map_iso 2 eK.symm]
    exact mem_map_of_mem _ hl
  have he := hfix (show (⟨a, hAJ ha⟩ : J) ∈ A.subgroupOf J from ha)
    (lK : J) (mem_map_of_mem K.subtype hlK)
  exact congrArg J.subtype he

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
