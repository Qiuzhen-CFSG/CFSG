module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.LocalCore
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.OriginalInitial
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.MarkedGeometry
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.LayerMarks
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.ActionSizes
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters.Literal

/-!
# Assemble the actual source markings into the terminal fusion argument

The original hypotheses, source 53 intersection and source 55 centers supply
all scalar and local-core fields. The two actions from the same source 54
coordinates preserve their determinant marking. The source 56 partner and
source 58 recognition use one common natural–dual identification. These
inputs therefore instantiate the existing source 59–61 contradiction.

Source: Aschbacher–Smith, 15.3.50–61, printed pp.1145–1151.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core
open Core.Automizers.Models Core.ResidualGeneration ResidualOrbits
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

noncomputable def original_earlierData
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    [(d.Z.subgroupOf (closureU d.Z d.ZS)).Normal]
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (g : G) [(d.V.subgroupOf (pairP d.Z d.ZS g)).Normal]
    (hI : pairI d.Z d.ZS g = d.Y ⊔ closureU d.Z d.ZS)
    (hIM : pairI d.Z d.ZS g ≤ d.M)
    (hVP : d.V ≤ pairP d.Z d.ZS g)
    (hcenterP : d.V = (center (pairP d.Z d.ZS g)).map (pairP d.Z d.ZS g).subtype)
    (hcenterU : center (closureU d.Z d.ZS) = d.Z.subgroupOf (closureU d.Z d.ZS))
    (hg : g ∈ d.Y) (hmove : ¬ rightConjugate d.Z g ≤ d.V ⊓ closureU d.Z d.ZS)
    (layers : LayerActions (pairI d.Z d.ZS g) d.Y (pairP d.Z d.ZS g) d.V
      (Cubic.MLocal.Structure.pairI_normalizes_pairP d.Z d.ZS g)
      (hIM.trans d.action.normalizes))
    (hdet : ∀ v : d.V, (layers.lowerCoordinates v).toAdd.det =
      FusionCore.orthogonalCoordinateValue (d.action.coordinates v))
    (quotientPair : Cubic.MLocal.Structure.NaturalQuotientPair d.action
      (pairI d.Z d.ZS g) (pairP d.Z d.ZS g) hIM
      (Cubic.MLocal.Structure.pairI_normalizes_pairP d.Z d.ZS g))
    (Y₁ : Subgroup G) (y t₀ : G) (hY₁ : Y₁ ≤ d.Y)
    (r : Recognition.FusionRecognition (d.T : Subgroup G) d.Z d.ZS d.V t₀)
    (partner : Partner.EarlierGeometry (d.T : Subgroup G) d.Z d.ZS d.V Y₁ y t₀)
    (hrec : partner.recognized = r.recognized) :
    Assembly.EarlierData d.T d.M d.action 1 g Y₁ y t₀ := by
  have hpartner := FusionCore.CosetSetup.OriginalSource.source_partner_eq hG d hempty hM hu hmany
  rcases d with ⟨T,M,Mc,hTM,action,Yplus,choice⟩
  change Mc = centralizerH (centralInvolutions T) at hpartner
  subst Mc
  let d : CharacteristicTwo.LocalData G :=
    ⟨T,M,centralizerH (centralInvolutions T),hTM,action,Yplus,choice⟩
  let h := original_hypothesis hG d hempty hM hu hmany hfixed
  have hconj := original_conjugates_centralize hG d hM hfixed
  have hUnon := original_U_nonabelian hG d hempty hM hu hmany hfixed hnon
  have hY : d.Y = residualY d.M (centralizerH d.Z) := rfl
  have hf := FusionCore.CosetSetup.OriginalSource.source_fusion_inputs hG d hM hfixed
  have hVC := module_centralizer_eq_point d (centralizerH d.Z) h hUnon
  have hc := localCoreData_of_layers d h g hI hIM hVP hcenterP hcenterU hVC layers
  have hcard := nonabelian_image_card d (centralizerH d.Z) h hUnon
  have hinter := nonabelian_intersections d (centralizerH d.Z) h hconj hnon hUnon
  refine {
    T_le_M := d.sylow_le
    core := by simpa only [← hY] using hc
    partner := partner
    Y₁_le := hY ▸ hY₁
    V_not_le_core := module_not_le_core d (centralizerH d.Z) h hconj hnon
    displacement_le := ?_
    displacement_card := commutator_quotient_card d (centralizerH d.Z) h hconj hnon hUnon
    U_card := r.U_card
    extraspecial := r.extraspecial
    pair_eq := by simpa only [← hY] using hI
    pair_le_M := hIM
    normalizes_Y := ?_
    center_P := hcenterP
    layers := layers
    quotientPair := quotientPair
    centralizer_Y := ?_
    characteristic_two := ?_
    chosen_mem := hY ▸ hg
    chosen_moving := hmove
    U_image_elementary := span_image_elementary d (centralizerH d.Z) h
    U_image_card := hcard
    U_image_other := ?_
    U_action_card := ?_
    fixed_action_card := ?_
    centralizer_control := hfixed
    Z_card := h.point_card
    plusType := r.plusType
    plusElementary := r.plusElementary
    natural_singular := by simpa only [hrec] using r.natural_singular
    square := by
      intro z hz hzm
      change Extraspecial.SquareForm partner.recognized z
      rw [hrec]
      exact r.square z hz hzm
    swap := by simpa only [hrec] using r.swap
    fixed_line := quotient_fixed_line_of_commutator
      (FusionCore.CosetSetup.OriginalSource.source_seed_commutator d)
    marked_geometry := ?_
    intersection_card := ?_
    singular := ?_
    hyperplane := ?_
    nonsingular := ?_
    separated := marked_involutions_not_conjugate d hf }
  · rw [commutator_comm]
    exact (module_commutator_bounds d (centralizerH d.Z) h).2.trans inf_le_left
  · rw [← hY]
    exact (normal_subgroupOf_iff_le_normalizer
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)).mp
      (residualY_normal d.M d.Mc)
  · rw [← hY]
    exact (FusionCore.CosetSetup.Source49.ordinary_from_original hG d hempty hM hu hmany hfixed).1.symm
  · exact hG.evenCharacteristic d.T d.M hM.1.1 d.sylow_le
  · intro he
    exact nonabelian_image_outside_stabilizer d (centralizerH d.Z) h hUnon he.le
  · exact (conjugation_subgroup_image_card_eq d.action (d.T : Subgroup G)
      (closureU d.Z d.ZS) d.sylow_le (h.UH_le_QH.trans h.QH_le_T) h.T_normalizes_V).trans hcard
  · exact (fixedLift_action_card_eq d.action d.Z d.ZS
      ((show closureU d.Z d.ZS ≤ pairI d.Z d.ZS g from le_sup_left).trans hIM)
      ((show closureU d.Z d.ZS ≤ pairI d.Z d.ZS g from le_sup_left).trans
        (hIM.trans d.action.normalizes))).trans hcard
  · intro z v hz hv hzm hvm
    rw [hrec]
    exact Classical.choice (exists_marked_local_geometry d h hf hconj hnon hUnon
      (FusionCore.CosetSetup.OriginalSource.source_seed_commutator d) r z v hz hv hzm hvm)
  · rw [inf_comm,hinter.2.1]
    exact commutator_card_eight d (centralizerH d.Z) h hUnon
  · intro z hz hzm
    exact lower_marked_singular d layers hdet hf z hz hzm
  · intro z hz hzm
    exact lower_marked_hyperplane d layers hdet h hconj hnon hUnon z hz hzm
  · intro v hv hvm
    exact lower_marked_nonsingular d layers hdet v hv hvm

/-- The literal original-input consumer of the terminal transfer theorem. -/
theorem false_of_original_recognized_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    [(d.Z.subgroupOf (closureU d.Z d.ZS)).Normal]
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (g : G) [(d.V.subgroupOf (pairP d.Z d.ZS g)).Normal]
    (hI : pairI d.Z d.ZS g = d.Y ⊔ closureU d.Z d.ZS)
    (hIM : pairI d.Z d.ZS g ≤ d.M)
    (hVP : d.V ≤ pairP d.Z d.ZS g)
    (hcenterP : d.V = (center (pairP d.Z d.ZS g)).map (pairP d.Z d.ZS g).subtype)
    (hcenterU : center (closureU d.Z d.ZS) = d.Z.subgroupOf (closureU d.Z d.ZS))
    (hg : g ∈ d.Y) (hmove : ¬ rightConjugate d.Z g ≤ d.V ⊓ closureU d.Z d.ZS)
    (layers : LayerActions (pairI d.Z d.ZS g) d.Y (pairP d.Z d.ZS g) d.V
      (Cubic.MLocal.Structure.pairI_normalizes_pairP d.Z d.ZS g)
      (hIM.trans d.action.normalizes))
    (hdet : ∀ v : d.V, (layers.lowerCoordinates v).toAdd.det =
      FusionCore.orthogonalCoordinateValue (d.action.coordinates v))
    (quotientPair : Cubic.MLocal.Structure.NaturalQuotientPair d.action
      (pairI d.Z d.ZS g) (pairP d.Z d.ZS g) hIM
      (Cubic.MLocal.Structure.pairI_normalizes_pairP d.Z d.ZS g))
    (Y₁ : Subgroup G) (y t₀ : G) (hY₁ : Y₁ ≤ d.Y)
    (r : Recognition.FusionRecognition (d.T : Subgroup G) d.Z d.ZS d.V t₀)
    (partner : Partner.EarlierGeometry (d.T : Subgroup G) d.Z d.ZS d.V Y₁ y t₀)
    (hrec : partner.recognized = r.recognized) :
    False := by
  let := hG.simple
  exact Assembly.false_of_earlier_data (original_earlierData hG d hempty hM hu hmany hfixed
    hnon g hI hIM hVP hcenterP hcenterU hg hmove layers hdet quotientPair Y₁ y t₀ hY₁
    r partner hrec)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
