module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.FFClassification
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryTheta

/-!
# Original-input binary characteristic-two reductions

The original orthogonal action and preceding source theorems supply every
local input of the binary four- and five-dimensional branches. In dimension
five an actual invariant parabolic gives a strictly smaller characteristic-two
outside subgroup, so subgroup-order induction closes that case directly.
In dimension four the proved FF and cohomology classifiers construct the
natural-dual module and its literal residual binary MS input. The remaining
C.1.34 implication is restricted to that actual input and its marked Sylow.

Source: Aschbacher–Smith 15.3.24, printed pp.1129–1130.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
variable {G : Type*} [Group G] [Finite G]

/-- The ambient input of 15.3.24 is already supplied by the original
orthogonal action, ordering maximum, and 15.3.7. -/
theorem source_binary_ambient_conclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard) :
    LinearFourFive.Source.AmbientConclusions d := by
  obtain ⟨hne,_,hmax⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have hMc : d.Mc ∈ maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) :=
    hu ▸ Set.mem_singleton d.Mc
  have hTMc : (d.T : Subgroup G) ≤ d.Mc :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)).trans hMc.2
  obtain ⟨N,hN,horder⟩ := InitialSource.UniformControl.source_exists_ordering_maximal_above
    hG d.T ⟨hMc.1,hTMc⟩
  rw [hmax N hN] at horder
  have hC : d.Mc = centralizer (d.Z : Set G) :=
    centralizer_eq_Mc_of_residual_dichotomy d.T d.M d.Mc d.sylow_le
      ⟨hMc.1,hTMc⟩ hne hMc.2 horder
      ((source_lemma_15_3_2_4 d.T d.action hM (le_inf d.sylow_le hTMc)
        inf_le_left).imp id And.right)
  have h7 := source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action
    hM hu hmany hne
  exact ⟨(Subgroup.centralizer_le_normalizer _).trans
      (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).ge,
    hC,h7.2.1,h7.1,source_residual_seed_span hG d.T hempty d.action hM hu hmany hne,
    h7.2.2.2.2.2.2,d.action.planeStabilizer_index_two d.T d.sylow_le 1,
    d.action.card_centralInvolutions d.T d.sylow_le,
    d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1⟩

/-- The literal earlier-component input of 15.3.24 is supplied by 15.3.16
and the ordinary cubic-residual argument, on the original component and span. -/
theorem source_binary_component_conclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(n,ZMod 2)) :
    LinearFourFive.Source.ComponentConclusions d c := by
  obtain ⟨hY,hθ⟩ := source_lemma_15_3_17_binary_four_five
    hG d hempty hM hu hmany hI c hn e
  obtain ⟨_,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  exact ⟨hY,hθ,source_lemma_15_3_16_span_isR2 hG d hempty hM hu hmany hI htwo hf c,
    hcore,hJ⟩

open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
  LinearFourFive LinearFourFive.FiveParabolics in
/-- A binary five-dimensional counterexample has a strictly smaller actual
characteristic-two outside overgroup. This stops the parabolic argument before
any classification of components in that smaller group. -/
theorem smaller_characteristicTwo_of_binary_five
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hf : HasCharacteristicTwo I)
    (hrank : primeRank 3 d.Yplus = 2)
    (c : ComponentWitness d I) (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(5,ZMod 2))
    (hYL : d.Yplus ≤ c.L) (hθ : c.L = theta I)
    (hθM : theta (d.MI I) = d.Yplus) (htwo : OutsideStructure.RankTwoCase d I) :
    ∃ K : Subgroup G, K < I ∧ K ∈ d.Hplus ∧ HasCharacteristicTwo K := by
  obtain ⟨_,hH,hsol,h3⟩ := SourceQuotients.source_preparation_of_earlier
    d c e hS hYL hθM hrank (Or.inl htwo)
  have hi := isInnerOnModel_of_product_quotient d c e hS hYL hθ hH hsol h3
  obtain ⟨b,i,hbase,hout,hn⟩ :=
    exists_outside_parabolic d c e hS hYL hθ hsol h3 hi
  let P := parabolic e b i
  let K := P ⊔ d.S
  have hPL : P ≤ c.L := lift_le e _
  have hSI : d.S ≤ I := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hKI : K ≤ I := sup_le (hPL.trans (component_le c)) hSI
  have hYK : d.Yplus ⊔ d.S ≤ K :=
    sup_le_sup_right (le_sup_left.trans hbase) _
  have hKM : ¬ K ≤ d.M := fun h => hout (le_sup_left.trans h)
  obtain ⟨hK,_,hfK⟩ := intermediate_outside d hI hS hf hKI hYK hKM
  have h31 : ¬ 31 ∣ Nat.card K := not_thirtyOne_dvd_join P d.S hn
    (Chapter1.isSylowIn_iff.mp hS).1 (parabolic_quotient_models e b i)
  have hKI' : K < I := lt_of_le_of_ne hKI (fun he =>
    component_not_five d c (he ▸ h31) e)
  exact ⟨K,hKI',hK,hfK⟩

/-- The degree-five branch of original 15.3.13 closes using its induction
hypothesis on proper outside overgroups. No earlier model list or exclusion
on those smaller groups is an independent premise. -/
theorem source_lemma_15_3_24_five_of_proper_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I)
    (hproper : ∀ K : Subgroup G, K < I → K ∈ d.Hplus → ¬ HasCharacteristicTwo K)
    (c : ComponentWitness d I) (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(5,ZMod 2)) : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  obtain ⟨hYL,hθ⟩ := source_lemma_15_3_17_binary_four_five
    hG d hempty hM hu hmany hI c (Or.inr rfl) e
  obtain ⟨K,hKI,hK,hfK⟩ := smaller_characteristicTwo_of_binary_five d hI h11.sylow hf
    (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) c e hYL hθ h11.theta_eq.symm htwo
  exact hproper K hKI hK hfK

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearFourFive
open LinearFourFive.NaturalDualParabolic
open LinearFourFive.NaturalDualParabolic.Realization
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original degree-four setup constructs the literal binary MS input at
an actual point of its natural-dual model. Only C.1.34 on this input remains
explicit; the FF and cohomology classifications and every earlier geometric
clause are supplied by their proved original-source producers. -/
theorem source_lemma_15_3_24_four_of_binary_ms
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(4,ZMod 2))
    (classification : ∀ (h : NaturalDual d c.L) (x : BinaryLinear.OuterCyclic.Space 4), x ≠ 0 →
      ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple
        (residualComponent h x) (sylowPart h x) →
      ∀ P : Sylow 2 (residualOvergroup h x),
        sylowPart h x ≤ (P : Subgroup (residualOvergroup h x)) →
        ∃ e' : (residualComponent h x ⧸ pCore 2 (residualComponent h x)) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
          Alternatives (ZMod 2) 1 (residualComponent h x) (sylowPart h x) P e') : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hrank := OutsideStructure.rankTwoCase_three_rank hG d hI htwo
  have ambient := source_binary_ambient_conclusions hG d hempty hM hu hmany
  have hc := source_binary_component_conclusions hG d hempty hM hu hmany
    hI htwo hf c (Or.inl rfl) e
  have hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) := htwo.2.2.2.2.1
  have hLR : c.L ⊔ d.R ≤ I :=
    sup_le (component_le c) ((pCoreIn_le 2 _).trans hI.1.2)
  have hcore : c.L.pCoreIn 2 ≤ d.R :=
    (pCoreIn_mono_of_normalizes le_sup_left
      (hLR.trans (normalizes_of_eq_theta hc.component_eq_theta))).trans hc.core_le
  have hW : d.componentSpan c.L ≤ c.L ⊔ d.R := by
    have hh := span_le_overgroup d c.L hR
    simpa only [overgroup,sup_eq_left.mpr (hc.yplus_le.trans le_sup_left)] using hh
  have hcontrol : SolvableInvariantControl d I :=
    SourceRankOne.OriginalSource.source_lemma_15_3_26_3 hG d hempty hM hu hmany hI hf
  let earlier : Preparation.Earlier d c :=
    ⟨h11.sylow,hc.yplus_le,hc.component_eq_theta,h11.theta_eq.symm,
      htwo.1,htwo.2.1,hcontrol,hcore⟩
  have hq := OutsideStructure.outside_sqtk hG d hI
  obtain ⟨h,_,hsplit⟩ := FourModules.naturalDual_plane_split d c
    SourceInputs.FFClassification.classification SourceInputs.universalNaturalCohomology
    hI hf hrank earlier hq e hW hc.span_reduced hc.core_le hc.thompson
    (hR.le.trans inf_le_right) ambient.centralizer_le ambient.involution_centralizer
    ambient.intersection ambient.residual_image ambient.span ambient.alternatives
  let _ := hc.span_reduced.elementary
  let _ : IsElementaryAbelian 2 (d.componentSpan c.L) :=
    IsElementaryAbelian.of_surjective (subgroupOfEquivOfLe hW).toMonoidHom
      (subgroupOfEquivOfLe hW).surjective
  obtain ⟨_,_,hi,p,_⟩ := Preparation.source_preparation hI hf hrank earlier h.model
  obtain ⟨x,hx,hSP,hact⟩ := ProjectedAction.exists_point c h p.marking hc.yplus_le
    earlier.theta_local hcore (hR.le.trans inf_le_right) ambient.span hsplit
    (fun hs => (h11.second_choice hs).2.1)
  obtain ⟨input,_,_,_,_⟩ := NumericClassification.exists_marked_binaryInput_of_inner
    h p.marking hx h11.sylow hc.component_eq_theta hi hSP hf hq hsplit hact
    h11.characteristic_exclusion
  obtain ⟨P,hmark⟩ := residualOvergroup_sylow h x (component_le c) h11.sylow
  have hSP' : sylowPart h x ≤ (P : Subgroup (residualOvergroup h x)) := by
    intro s hs
    have hm : (s : G) ∈ (P : Subgroup (residualOvergroup h x)).map
        (residualOvergroup h x).subtype := hmark.symm ▸ hs
    obtain ⟨t,ht,he⟩ := hm
    exact (Subtype.ext he : t = s) ▸ ht
  obtain ⟨e',ha⟩ := classification h x hx input P hSP'
  exact NumericClassification.not_source_alternatives h hx h11.sylow
    hc.component_eq_theta input ambient.sylow_index ambient.center_order
    ambient.fixed_plane_order P hmark e' ha

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
