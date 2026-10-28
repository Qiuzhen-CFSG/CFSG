module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.SourceInputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.ResidualProduct

/-!
# The conditional source implications 15.3.39--40

The component-orbit equality is supplied by the constructed factor geometry:
under a strict orbit, two simple conjugate components give equal actor
projections, while the moving definite plane has a nontrivial projection.
Its commuting and generating actors then contradict one another.

For containment, 15.3.38 and the local rank bound reduce to three-rank one.
The actual linear model ranks exclude the diagonal branch, leaving the
corrected three-part splitting. The component is normal inside I. The
1.1.5 model inspection proves its trivial two-core, and the source plane
actors are identified with its component and centralizing residuals.

The two orientations are handled separately. Only when Y₊ = Y are the
planes interchanged. The Borel action restricts the model and constructs
O²(Y₊ ∩ L) ≃ A₄. The actual residual action, its centralizer kernel, and
a genuine element of T minus S supply the residual-product argument,
constructing Y ≃ A₄ × A₄ and contradicting 15.3.9. No product configuration,
actor equivalence, field bound, or either target containment is assumed.

The parent supplies the earlier source inputs in `ContainmentSourceInputs`.
These are conditional implications, not proofs of those earlier results.
The literal 15.3.37 alternatives follow afterwards through their first
branch, without feeding that corollary back into the corrected reduction.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.39--40,
printed pp.1137--1138; correction of 15.3.37 recorded in
`docs/quasithin-proof-basis.md`.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem orbit_eq_span (L S : Subgroup G) :
    componentOrbit L S = localSpan L S :=
  le_antisymm (iSup_conjugates_le_of_le_normalizer L S _
    (le_conjugateSpanBy L S) (le_normalizer_conjugateSpanBy L S))
    (conjugateSpanBy_le (le_componentOrbit L S) (le_normalizer_componentOrbit L S))

/-- Source 15.3.39 from the genuine earlier conclusions. The imported
factor-geometry proof constructs the actual two-component projections. -/
public theorem source_lemma_15_3_39 (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} {z : G} (h : ContainmentSourceInputs d I L z) :
    L = componentOrbit L d.S :=
  componentOrbit_eq_of_threePartAlternatives d h.component_le h.outside_structure
    h.component h.component_structure h.strongly_quasithin h.component_rank_pos
    h.component_alternative h.residual_image h.rank_two_case h.alternatives
    h.intersection_splitting

private theorem rank_one_of_not_contained (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} {z : G} (h : ContainmentSourceInputs d I L z)
    (hne : ¬ d.Yplus ≤ L) : primeRank 3 L = 1 := by
  have hl := Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion h.component_le)
    (inclusion_injective h.component_le)
  have hi := h.strongly_quasithin 3 (by decide) (by decide)
  have hp := h.component_rank_pos
  have hn : primeRank 3 L ≠ 2 := fun he => hne (h.rank_two_containment he)
  omega

private theorem not_diagonal_of_rank_one {Yplus L L₀ : Subgroup G}
    (hr : primeRank 3 L = 1) : ¬ Candidates.RankTwoDiagonal Yplus L L₀ := by
  rintro ⟨_, _, y, _, _, _, hm⟩
  rcases hm with ⟨n, _, hn, hm, _⟩ | hm
  · have hh := Candidates.SignedReduction.RankOneModels.linear_three_even_rank hn hm
    omega
  · obtain ⟨F, _, _, hc, e, _, _, _, _, _⟩ := hm
    have hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 (2 ^ 2) :=
      ⟨F, inferInstance, inferInstance, hc, ⟨e⟩⟩
    have hh := Candidates.SignedReduction.RankOneModels.linear_three_even_rank
      (by decide : Even 2) hq
    have hu := primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 L) pCore_isPGroup
    omega

private theorem rank_one_core (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} {z : G} (h : ContainmentSourceInputs d I L z)
    (hr : primeRank 3 L = 1) : pCore 2 L = ⊥ := by
  let := h.component.2
  obtain ⟨α, _, ha⟩ := h.component_structure.model_action
  have hrK : primeRank 3 (L.subgroupOf I) = 1 :=
    (primeRank_equiv 3 (subgroupOfEquivOfLe h.component_le)).trans hr
  have hc := (Candidates.SignedReduction.RankOneModels.rankOneInitialModel_and_core
    α ha h.component_structure.odd_core hrK).2
  have he := pCore_map_iso 2 (subgroupOfEquivOfLe h.component_le)
  rw [hc, Subgroup.map_bot] at he
  exact he.symm

omit [Finite G] in
private theorem quotient_card_of_split {Yplus L L₀ : Subgroup G}
    (hs : Candidates.RankOneThreePartSplit Yplus L L₀) :
    Nat.card (Yplus ⧸ pCore 2 Yplus) = 9 := by
  obtain ⟨e⟩ := hs.quotient
  rw [Nat.card_congr e.toEquiv]
  norm_num [Nat.card_eq_fintype_card]

omit [Finite G] in
private theorem rank_one_setup (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} {z : G} (h : ContainmentSourceInputs d I L z)
    [(L.subgroupOf I).Normal]
    (hr : primeRank 3 L = 1)
    (hs : Candidates.RankOneThreePartSplit d.Yplus L (componentOrbit L d.S)) :
    Candidates.RankOneAction.Setup d.Yplus d.S d.M I L where
  outside := h.outside
  sylow := h.outside_structure.sylow
  sylow_le := inf_le_left.trans d.sylow_le
  component_le := h.component_le
  component := h.component
  component_outside := by
    simpa only [map_subgroupOf_eq_of_le h.component_le] using h.component_structure.outside
  orbit_eq := hs.orbit_eq.trans (orbit_eq_span L d.S)
  orbit_bound := by
    have he : (normalizer (L : Set G)).relIndex I = 1 :=
      relIndex_eq_one.mpr (le_normalizer_of_normal_subgroupOf h.component_le)
    omega
  theta_eq := h.outside_structure.theta_eq.symm
  normalizer_eq := h.outside_structure.normalizer_eq
  quotient_three := IsPGroup.of_card (n := 2) (quotient_card_of_split hs)
  rank_component := hr
  rank_yplus := h.residual_rank
  residual_ne := by
    intro he
    have ht := hs.component_three_part
    rw [he] at ht
    norm_num at ht
  characteristic_two_containment := h.invariant_subgroup

private theorem square_of_oriented_actor (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} {z : G} (h : ContainmentSourceInputs d I L z)
    (hs : Candidates.RankOneThreePartSplit d.Yplus L (componentOrbit L d.S))
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j)
    (hchoice : Hypothesis15310 d.M d.Y d.S (d.action.plane i) d.Yplus)
    (hAU : componentFactor d.Yplus L ≤ centralizer (d.action.plane i : Set G))
    (hAW : ⁅d.action.plane j, componentFactor d.Yplus L⁆ = d.action.plane j)
    (eA : componentFactor d.Yplus L ≃* alternatingGroup (Fin 4))
    (t : G) (ht : t ∈ (d.T : Subgroup G) ∧ t ∉ d.S)
    (hti : (d.action.plane i).map (MulAut.conj t).toMonoidHom = d.action.plane j)
    (htj : (d.action.plane j).map (MulAut.conj t).toMonoidHom = d.action.plane i) :
    Nonempty (d.Y ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) := by
  have hYM := Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal d.M d.Mc)
  obtain ⟨hRS, hVR, hself⟩ := RankOne.PlaneGeometry.core_geometry d.action d.T
    d.sylow_le (localModule_le d.T d.sylow_le) hYM h.characteristic_two h.residual_core 1
  obtain ⟨hD, hk, hq⟩ := RankOne.PlaneGeometry.residualAction_geometry d.action
    h.residual_image h.residual_quotient hij
  have hSY := (source_orbit_plane_facts d.action d.T d.sylow_le
    (localModule_le d.T d.sylow_le) 1 (Multiplicative.ofAdd (1 : ZMod 2)) d.choice).1
  have hSL : d.S ≤ normalizer (L : Set G) := by
    rw [hs.orbit_eq]
    exact le_normalizer_componentOrbit L d.S
  have hplusY : d.Yplus ≤ d.Y := by
    rcases d.choice with he | ⟨_, he⟩
    · exact he.le
    · rw [he]
      exact (map_subtype_le _).trans inf_le_left
  have hout := ResidualProduct.alternating_square_of_local_geometry
    (RankOne.PlaneGeometry.residualAction d.action) hD hk hq hchoice
    (quotient_card_of_split hs) (residualY_isPPerfect d.M d.Mc) hplusY
    (d.sylow_le.trans hMY) hRS hself
    ((d.action.plane_le i).trans hVR) ((d.action.plane_le j).trans hVR)
    (d.action.card_plane i) (d.action.card_plane j) (natural_planes_disjoint d.action hij)
    (normalizes_componentFactor hSY hSL) hAU hAW eA t ht hti htj
  exact hout.2.2.2.2.2.2

/-- Source 15.3.40 from the genuine earlier conclusions. The rank-one
factor/centralizer branch produces an actual alternating-square equivalence,
contradicting 15.3.9. Both definite-plane orientations are included. -/
public theorem source_lemma_15_3_40 (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} {z : G} (h : ContainmentSourceInputs d I L z) : d.Yplus ≤ L := by
  classical
  by_contra hne
  have horbit := source_lemma_15_3_39 d h
  have hr := rank_one_of_not_contained d h hne
  have hs : Candidates.RankOneThreePartSplit d.Yplus L (componentOrbit L d.S) := by
    rcases h.alternatives with he | he | he
    · exact (hne (he.trans horbit.ge)).elim
    · exact he
    · exact (not_diagonal_of_rank_one hr he).elim
  obtain ⟨P, hP⟩ := h.outside_structure.sylow
  let : (L.subgroupOf I).Normal := relative_normal_of_source_componentOrbit_eq
    h.component_le P hP h.component_alternative horbit
  have hsetup := rank_one_setup d h hr hs
  have hcore := rank_one_core d h hr
  obtain ⟨a, _, ho⟩ := source_identified_and_oriented_planeActors d h.outside h.component_le
    h.outside_structure h.component_structure h.component_alternative h.residual_image
    h.rank_two_case hs
  have hij : (1 : OrthogonalPlaneIndex) ≠ Multiplicative.ofAdd (1 : ZMod 2) := by decide
  obtain ⟨t, ht, hts, ht1, ht2⟩ := RankOne.PlaneGeometry.exists_plane_interchanger
    d.action d.T d.sylow_le hij
  apply h.not_alternating_square
  rcases ho with ⟨ha, hWL⟩ | ⟨hYY, ha, hWL⟩
  · have hgen : ⁅d.V, componentFactor d.Yplus L⁆ = d.V₂ := by rw [ha]; exact a.plane
    obtain ⟨_, ⟨eA⟩⟩ := RankOnePlane.component_model_and_actor_of_source d hsetup
      h.centralizer_overgroup h.outside_structure.odd_core hcore _ hgen hWL hs.model
    apply square_of_oriented_actor d h hs hij d.choice _ _ eA t ⟨ht, hts⟩ ht1 ht2
    · rw [ha]; exact a.right_le.trans (inf_le_right.trans inf_le_right)
    · rw [ha]; exact a.plane_self
  · have hgen : ⁅d.V, componentFactor d.Yplus L⁆ = d.V₁ := by
      rw [ha, hYY]
      exact (residualY_fullActionCoordinateFacts d.action h.residual_image).commutator _ _ hij.symm
    obtain ⟨_, ⟨eA⟩⟩ := RankOnePlane.component_model_and_actor_of_source d hsetup
      h.centralizer_overgroup h.outside_structure.odd_core hcore _ hgen hWL hs.model
    apply square_of_oriented_actor d h hs hij.symm (Or.inl hYY) _ _ eA t ⟨ht, hts⟩ ht2 ht1
    · rw [ha]; exact centralizingFactor_le _ _
    · rw [ha]; exact a.other_plane hYY

/-- The literal alternatives hold through their first branch after 15.3.40.
This corollary is not used in either containment proof. -/
public theorem literal_alternatives_after_containment (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} {z : G} (h : ContainmentSourceInputs d I L z) :
    Candidates.Alternatives15337 d.Yplus L (componentOrbit L d.S) :=
  Or.inl ((source_lemma_15_3_40 d h).trans (le_componentOrbit L d.S))

end CFSG.Quasithin.Chapter15.Section03.RankTwo
