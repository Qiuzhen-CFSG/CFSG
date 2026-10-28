module

public import Stellmacher.SectionEight.GeneratedEightFiveActionFromFour
public import Stellmacher.QuotientModuleFixedPoints
public import Stellmacher.SectionEight.GeneratedEightSixEquationOneSetup

/-!
# The first commutator in generated Stellmacher (8.6)

The order-four initial center has the central first-step center as its
order-two Sylow-fixed line. This fixed-line calculation does not require
the unused long-path premise in the (8.5) interface. The line has index
two in the initial center, so the initial-center commutator with the
first-step core lies in it. Local transitivity transports this bound to
every center generating the first-step neighbor join. At distance two,
the critical terminal center lies in the first-step core, making the
commutator nontrivial and hence equal to the line.

Source: Stellmacher, printed p.41, the paragraph preceding (8.6)(1),
`refs/files/stellmacher-n-group.pdf`. Hypothesis Two stays on the ambient
group; all proofs use the graph-preserving local context.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement
universe u

private theorem elementary_centralizer_le_omega
    {G : Type u} [Group G] {E T : Subgroup G}
    (hET : E ≤ T) (hcentral : E ≤ Subgroup.centralizer (T : Set G))
    (hpow : ∀ element ∈ E, element ^ 2 = 1) :
    E ≤ omegaOneCenter T := by
  intro element helement
  let point : T := ⟨element, hET helement⟩
  have hpoint : point ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro actor
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcentral helement) actor actor.property
  let centralPoint : Subgroup.center T := ⟨point, hpoint⟩
  have hpower : centralPoint ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hpow element helement
  have homega : centralPoint ∈ omega₁ (G := Subgroup.center T) (p := 2) := by
    rw [omega₁, omega]
    apply Subgroup.subset_closure
    simpa using hpower
  exact Subgroup.mem_map_of_mem T.subtype
    (Subgroup.mem_map_of_mem (Subgroup.center T).subtype homega)

private theorem omega_sylow_le_z
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (vertex : Γ.Vertex)
    (hS : IsSylowTwoIn S (stabilizer Γ vertex)) :
    omegaOneCenter S ≤ z Γ vertex := by
  obtain ⟨_, sylow, hsylow⟩ := hS
  change omegaOneCenter S ≤ Γ.zAt vertex
  rw [Γ.zAt_def]
  exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩

/-- The central first-step center is the order-two fixed line in the
four-element initial center, without a long-path assumption. -/
public theorem eight_six_first_step_fixed_line_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.firstStep) = 2 ∧
      ZAt ctx.Γ ctx.criticalPath.firstStep ≤ ZAt ctx.Γ ctx.criticalPath.a := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Za := z Γ cp.a
  let Zfirst := z Γ cp.firstStep
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hback : cp.a ∈ neighborhood Γ cp.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hback
  have hlocal := SevenSix.edge_local_data h Γ cp
  have hSylow : IsSylowTwoIn S P := hlocal.1.1.1.2.1
  have hSylowFirst : IsSylowTwoIn S (stabilizer Γ cp.firstStep) :=
    hlocal.2.1.1.2.1
  have hZaS : Za ≤ S :=
    ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        ((Subgroup.map_subtype_le _).trans (SevenSix.local_cores_le_edge_sylow h Γ cp).1))
  have hZfirstS : Zfirst ≤ S :=
    ((lemma_seven_three h Γ).center_core cp.firstStep cp.a hback).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        ((Subgroup.map_subtype_le _).trans (SevenSix.local_cores_le_edge_sylow h Γ cp).2))
  have hZfirstCentral : Zfirst ≤ Subgroup.centralizer (S : Set H) :=
    (hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
      (Subgroup.centralizer_le hSylowFirst.1)
  have hZfirstOmega : Zfirst ≤ omegaOneCenter S :=
    elementary_centralizer_le_omega hZfirstS hZfirstCentral
      (fun element helement => elemPow_eq_one_of_isElementaryAbelian element helement)
  have hOmegaZa : omegaOneCenter S ≤ Za := omega_sylow_le_z Γ cp.a hSylow
  have hOmegaFirst : omegaOneCenter S ≤ Zfirst :=
    omega_sylow_le_z Γ cp.firstStep hSylowFirst
  have hfixedEq : Za ⊓ Subgroup.centralizer (S : Set H) = Zfirst := by
    apply le_antisymm
    · apply le_trans _ hOmegaFirst
      exact elementary_centralizer_le_omega (inf_le_left.trans hZaS) inf_le_right
        (fun element helement => elemPow_eq_one_of_isElementaryAbelian element helement.1)
    · exact le_inf (hZfirstOmega.trans hOmegaZa) hZfirstCentral
  obtain ⟨w⟩ := exists_quotientModuleWitness P Za
    (hZaS.trans (cp.S_le_edge_stabilizers.trans inf_le_left))
    (stabilizer_le_normalizer_z Γ cp.a)
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom Za w.action
  obtain ⟨hSP, sylow, hsylow⟩ := hSylow
  have hnative : (sylow : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hsylow
  let imageSylow := sylow.mapSurjective w.surjective
  have himage : (imageSylow : Subgroup w.X) = (S.subgroupOf P).map w.projection := by
    change (sylow : Subgroup P).map w.projection = _
    rw [hnative]
  have hJne := (eight_five_offender_local ctx w).2
  have hJle : SectionOne.oneJ (V := Za) ((S.subgroupOf P).map w.projection) ≤
      (imageSylow : Subgroup w.X) := by
    rw [himage]
    exact sSup_le fun _ hactor => hactor.1
  have hnontrivial : (imageSylow : Subgroup w.X) ≠ ⊥ := by
    intro hbot
    exact hJne (bot_unique (hJle.trans_eq hbot))
  let fixed := FixedPoints.subgroup imageSylow Za
  change Nat.card Za = 4 at hcard
  have hparity := imageSylow.isPGroup'.card_modEq_card_fixedPoints Za
  change Nat.card Za % 2 = Nat.card fixed % 2 at hparity
  have hpositive : 0 < Nat.card fixed := Nat.card_pos
  have hproper : fixed ≠ ⊤ := by
    intro htop
    apply hnontrivial
    apply bot_unique
    intro actor hactor
    change actor = 1
    apply w.action_injective
    rw [map_one]
    apply MulEquiv.ext
    intro point
    have hpoint : point ∈ fixed := htop ▸ Subgroup.mem_top point
    exact hpoint (⟨actor, hactor⟩ : imageSylow)
  have hless : Nat.card fixed < 4 := by
    have hle := Subgroup.card_le_card_group fixed
    by_contra hnot
    apply hproper
    apply Subgroup.eq_top_of_card_eq
    omega
  have hfixedCard : Nat.card fixed = 2 := by
    omega
  have htransfer := w.fixedPoints_card S hSP
  change Nat.card (FixedPoints.subgroup ((S.subgroupOf P).map w.projection) Za) = _ at htransfer
  rw [← himage] at htransfer
  have hfirstCard : Nat.card Zfirst = 2 := by
    rw [← hfixedEq, ← htransfer]
    exact hfixedCard
  exact ⟨hfirstCard, hZfirstOmega.trans hOmegaZa⟩

public theorem eight_six_commutator_le_of_line_index_two
    {G : Type*} [Group G] (moduleGroup line actor : Subgroup G)
    (hindex : (line.subgroupOf moduleGroup).index = 2)
    (hmodule : actor ≤ Subgroup.normalizer (moduleGroup : Set G))
    (hline : actor ≤ Subgroup.normalizer (line : Set G)) :
    ⁅moduleGroup, actor⁆ ≤ line := by
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_le.mpr
  intro element helement vector hvector
  have hconj : element * vector * element⁻¹ ∈ moduleGroup :=
    (Subgroup.mem_normalizer_iff.mp (hmodule helement) vector).mp hvector
  have hmem := (line.subgroupOf moduleGroup).mul_mem_iff_of_index_two hindex
    (a := ⟨element * vector * element⁻¹, hconj⟩)
    (b := ⟨vector⁻¹, moduleGroup.inv_mem hvector⟩)
  apply hmem.mpr
  change element * vector * element⁻¹ ∈ line ↔ vector⁻¹ ∈ line
  rw [line.inv_mem_iff]
  exact (Subgroup.mem_normalizer_iff.mp (hline helement) vector).symm

public theorem eight_six_commutator_sSup_le
    {G : Type*} [Group G] (family : Set (Subgroup G))
    (actors bound container : Subgroup G)
    (hnormal : container ≤ Subgroup.normalizer (bound : Set G))
    (hcontain : ∀ subgroup ∈ family, subgroup ≤ container)
    (hcomm : ∀ subgroup ∈ family, ⁅subgroup, actors⁆ ≤ bound) :
    ⁅sSup family, actors⁆ ≤ bound := by
  let controlled : Subgroup G := {
    carrier := {element | element ∈ container ∧
      ∀ actor ∈ actors, ⁅element, actor⁆ ∈ bound}
    one_mem' := ⟨container.one_mem, by simp⟩
    mul_mem' := by
      rintro first second ⟨hfirst, hfirstComm⟩ ⟨hsecond, hsecondComm⟩
      refine ⟨container.mul_mem hfirst hsecond, ?_⟩
      intro actor hactor
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact bound.mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hnormal hfirst) _).mp
          (hsecondComm actor hactor)) (hfirstComm actor hactor)
    inv_mem' := by
      rintro element ⟨helement, hcomm⟩
      refine ⟨container.inv_mem helement, ?_⟩
      intro actor hactor
      rw [commutatorElement_inv_left, ← commutatorElement_inv]
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (hnormal (container.inv_mem helement)) _).mp
          (bound.inv_mem (hcomm actor hactor)) }
  have hle : sSup family ≤ controlled := by
    apply sSup_le
    intro subgroup hsubgroup element helement
    exact ⟨hcontain subgroup hsubgroup helement, fun actor hactor =>
      hcomm subgroup hsubgroup (Subgroup.commutator_mem_commutator helement hactor)⟩
  exact Subgroup.commutator_le.mpr fun element helement actor hactor =>
    (hle helement).2 actor hactor

public theorem eight_six_first_commutator_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hlength : ctx.criticalPath.length = 2) :
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep, QAt ctx.Γ ctx.criticalPath.firstStep⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  have hlength' : path.length = 2 := hlength
  have hline := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  have hback : path.a ∈ neighborhood graph path.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr (graph.adjacent_symm path.firstStep_adj)
  have hindex : ((z graph path.firstStep).subgroupOf (z graph path.a)).index = 2 := by
    have hnative : Nat.card ((z graph path.firstStep).subgroupOf (z graph path.a)) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hline.2).toEquiv]
      exact hline.1
    have hproduct := ((z graph path.firstStep).subgroupOf (z graph path.a)).card_mul_index
    rw [hnative, hcard] at hproduct
    omega
  have hQinitial : q graph path.firstStep ≤ stabilizer graph path.a :=
    (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven graph path).2.trans
      (path.S_le_edge_stabilizers.trans inf_le_left)
  have hQfirst : q graph path.firstStep ≤ stabilizer graph path.firstStep := by
    rw [q, graph.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hseed : ⁅z graph path.a, q graph path.firstStep⁆ ≤ z graph path.firstStep :=
    eight_six_commutator_le_of_line_index_two _ _ _ hindex
      (hQinitial.trans (stabilizer_le_normalizer_z graph path.a))
      (hQfirst.trans (stabilizer_le_normalizer_z graph path.firstStep))
  have hupper : ⁅v graph path.firstStep, q graph path.firstStep⁆ ≤ z graph path.firstStep := by
    rw [v, graph.vAt_def]
    apply eight_six_commutator_sSup_le _ _ _ (stabilizer graph path.firstStep)
      (stabilizer_le_normalizer_z graph path.firstStep)
    · rintro subgroup ⟨neighbor, hneighbor, rfl⟩
      apply le_trans (SevenSix.critical_minimality graph path (d := neighbor)
        (l := path.firstStep) ?_) hQfirst
      have hdistance : graph.distance neighbor path.firstStep = 1 := by
        simpa only [graph.neighbors_def, Set.mem_ofPred_eq] using hneighbor
      omega
    · rintro subgroup ⟨neighbor, hneighbor, rfl⟩
      obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven graph).local_transitivity
        path.firstStep hback hneighbor
      have hfix : graph.act actor path.firstStep = path.firstStep :=
        Set.ext_iff.mp (graph.stabilizer_def path.firstStep) actor |>.mp actor.property
      have hmap := Subgroup.map_mono (f := (MulAut.conj (actor : G)⁻¹).toMonoidHom) hseed
      rw [Subgroup.map_commutator, ← z_act, ← SevenSix.q_act, ← z_act, hactor, hfix] at hmap
      exact hmap
  have hterminal : z graph path.a' ≤ q graph path.firstStep := by
    apply SevenSix.critical_minimality graph path
    have hbound := SevenSix.path_distance_le graph path 1 path.length (by omega) (by omega)
    simp only [path.path_first, path.path_end] at hbound
    have hdist : graph.distance path.firstStep path.a' ≤ 1 := by
      simpa only [hlength', Nat.reduceSub] using hbound
    rw [graph.distance_symm]
    omega
  have hinitial : z graph path.a ≤ v graph path.firstStep := by
    rw [v, graph.vAt_def]
    exact le_sSup ⟨path.a, hback, rfl⟩
  have hne : ⁅v graph path.firstStep, q graph path.firstStep⁆ ≠ ⊥ := by
    intro hzero
    exact ctx.commutator_ne (le_bot_iff.mp
      ((Subgroup.commutator_mono hinitial hterminal).trans_eq hzero))
  apply Subgroup.eq_of_le_of_card_ge hupper
  have hpositive := Nat.card_pos (α := (⁅v graph path.firstStep, q graph path.firstStep⁆ : Subgroup G))
  have hnotone : Nat.card (⁅v graph path.firstStep, q graph path.firstStep⁆ : Subgroup G) ≠ 1 :=
    fun hone => hne (Subgroup.card_eq_one.mp hone)
  have htwo : Nat.card (z graph path.firstStep) = 2 := hline.1
  omega

end Stellmacher.SectionEight
