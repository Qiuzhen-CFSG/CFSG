module
public import Stellmacher.SectionNine.NineThreeBaumannCenterCommutator
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Stellmacher.SectionNine.NineThreeFourCenterIndices
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricCoatomCoreJoin
public import Stellmacher.SectionFiveToSeven.SixFourQuadraticCriticalFixed
public import Stellmacher.SectionFiveToSeven.SixFourNativeBaumannFixed
public import Stellmacher.SectionNine.NineTwoCommutatorCenter

/-!
# A nontrivial canonical offender for the paired configuration

The actual normalized configurations from (9.3), with critical distance greater
than one and initial center larger than four, force the Section Six canonical
barred offender to be nontrivial. We do not require nontrivial native Thompson
action as an additional hypothesis.

If native Thompson acts nontrivially, the native Baumann fixed-space theorem
supplies the conclusion. Otherwise the mixed center commutator is trivial:
its intersection with the Baumann center is trivial, while native centralization
places the initial center in that Baumann center. The four center indices and
actor generation then show that the intersection of the other center with the
initial stabilizer has fixed index two on the initial center. The geometric
coatom commutator puts this actor inside the actual Sylow group, and (7.5)
makes its action quadratic. Transport through the given injective embedding
allows the quadratic fixed-index theorem to produce the canonical offender.

Source: Stellmacher (9.3), Journal of Algebra 190 (1997), pp.49–50,
`refs/files/stellmacher-n-group.pdf`. This proves the canonical input needed
by the rank calculation without asserting the stronger native-action jump.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem omega_thompson_le_baumann_center
    {G : Type u} [Group G] [Finite G] (T : Subgroup G) :
    omegaOneCenterAmbient (elementaryAbelianMaxJ T) ≤
      (Subgroup.center (baumannIn T)).map (baumannIn T).subtype := by
  let W := omegaOneCenterAmbient (elementaryAbelianMaxJ T)
  have hJT : elementaryAbelianMaxJ T ≤ T := sSup_le fun _ ha => ha.1
  have hWT : W ≤ T := fun w hw => hJT ((mem_omegaOneCenterAmbient_iff _ _).mp hw).1
  have hWB : W ≤ baumannIn T := by
    change W ≤ T ⊓ Subgroup.centralizer (W : Set G)
    refine le_inf hWT ?_
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hw' := (mem_omegaOneCenterAmbient_iff _ _).mp hw
    exact hw'.2.2 z ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  intro w hw
  refine ⟨⟨w,hWB hw⟩,?_,rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro b
  apply Subtype.ext
  have hb : (b : G) ∈ Subgroup.centralizer (W : Set G) := b.property.2
  exact (Subgroup.mem_centralizer_iff.mp hb w hw).symm

private theorem native_centralization_forces_mixed_bot
    {G : Type u} [Group G] [Finite G]
    (T Z R : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZT : Z ≤ T) (hRZ : R ≤ Z)
    (hzero : R ⊓ (Subgroup.center (baumannIn T)).map (baumannIn T).subtype = ⊥)
    (hJ : elementaryAbelianMaxJ T ≤ Subgroup.centralizer (Z : Set G)) : R = ⊥ := by
  have hZomega := elementary_centralizer_maxJ_le_omegaCenter T Z hZT
    (Subgroup.le_centralizer_iff.mp hJ)
  have hRcenter := hRZ.trans (hZomega.trans (omega_thompson_le_baumann_center T))
  exact (inf_eq_left.mpr hRcenter).symm.trans hzero

private theorem normalized_native_centralization_forces_mixed_bot
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hJ : elementaryAbelianMaxJ T ≤
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)) :
    let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m,
      ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act config.g (Γ.act first.extraction.x⁻¹ first.l)
  let R := (⁅ZAt Γ cp.a ⊓ GAt Γ m,ZAt Γ m ⊓ GAt Γ cp.a⁆ : Subgroup G)
  have ha : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ ha
  have hZaT : ZAt Γ cp.a ≤ T :=
    (((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep ha).trans
      ((omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))).trans
      (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
  have hRZa : R ≤ ZAt Γ cp.a :=
    (Subgroup.commutator_mono inf_le_left (le_refl _)).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (inf_le_right.trans (stabilizer_le_normalizer_z Γ cp.a)))
  exact native_centralization_forces_mixed_bot T (ZAt Γ cp.a) R hZaT hRZa
    (nine_three_normalized_baumann_center_commutator_bot ctx hb hlarge first second config) hJ
end Stellmacher.SectionNine

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem extracted_intersection_not_centralized
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B) (Γ : CosetGraphContext G T A B)
    (u0 d l : Γ.Vertex) (V E A0 : Subgroup G) (actor : G)
    (haZ : actor ∈ ZAt Γ u0) (haV : actor ∈ V)
    (data : NineThreeGeometricData Γ d l V E A0 actor)
    (hnot : ¬ ZAt Γ (Γ.act data.x⁻¹ l) ⊓ GAt Γ u0 ≤ ZAt Γ l) :
    ¬ ZAt Γ u0 ≤ Subgroup.centralizer
      (ZAt Γ (Γ.act data.x⁻¹ l) ⊓ GAt Γ u0 : Set G) := by
  let m := Γ.act data.x⁻¹ l
  let Y := ZAt Γ m ⊓ GAt Γ u0
  have hmback : d ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
  have hZmC := ((lemma_seven_three h Γ).center_core m d hmback).trans
    ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  intro hcent
  have hEC : E ≤ Subgroup.centralizer (Y : Set G) := by
    rw [data.actor_generated actor haV data.actor_outside]
    refine sup_le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr (hcent haZ))) ?_
    exact data.conjugate_core_le.trans ((Subgroup.le_centralizer_iff.mp hZmC).trans
      (Subgroup.centralizer_le inf_le_left))
  apply hnot
  intro z hz
  have hxE : data.x ∈ E := Subgroup.map_subtype_le _ data.residual_mem
  have hcomm := Subgroup.mem_centralizer_iff.mp (hEC hxE) z hz
  have hzM := hz.1
  change z ∈ CosetGraphContext.z Γ (Γ.act data.x⁻¹ l) at hzM
  rw [z_act, inv_inv] at hzM
  have hzBack := (Subgroup.mem_map_equiv).mp hzM
  change data.x⁻¹ * z * data.x ∈ ZAt Γ l at hzBack
  rwa [mul_assoc,hcomm,inv_mul_cancel_left] at hzBack

private theorem fixed_hyperplane_of_mixed_commutator_bot
    {G : Type u} [Group G] [Finite G] (Z K Y : Subgroup G)
    (hindex : Nat.card Z = 2 * Nat.card (Z ⊓ K : Subgroup G))
    (hcomm : ⁅Z ⊓ K,Y⁆ = ⊥)
    (hnot : ¬ Z ≤ Subgroup.centralizer (Y : Set G)) :
    Z ⊓ Subgroup.centralizer (Y : Set G) = Z ⊓ K := by
  let F := Z ⊓ K
  let C := Z ⊓ Subgroup.centralizer (Y : Set G)
  have hFC : F ≤ C := le_inf inf_le_left
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hCZ : C ≤ Z := inf_le_left
  have hCne : C ≠ Z := fun he => hnot (he ▸ (inf_le_right : C ≤ Subgroup.centralizer (Y : Set G)))
  have hlt : Nat.card C < Nat.card Z := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le hCZ)
    intro he
    exact hCne (Subgroup.eq_of_le_of_card_ge hCZ he.ge)
  have hD := Subgroup.card_dvd_of_le hCZ
  obtain ⟨n,hn⟩ := hD
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hn2 : 2 ≤ n := by nlinarith
  have hbound : Nat.card C ≤ Nat.card F := by change Nat.card Z = 2 * Nat.card F at hindex; nlinarith
  exact (Subgroup.eq_of_le_of_card_ge hFC hbound).symm
end Stellmacher.SectionNine

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
private theorem normalized_native_centralization_fixed_hyperplane
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hJ : elementaryAbelianMaxJ T ≤
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)) :
    let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    ZAt ctx.Γ ctx.criticalPath.a ⊓
      Subgroup.centralizer (ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a : Set G) =
        ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m ∧
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 2 * Nat.card
      (ZAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let c := MulAut.conj config.g⁻¹
  let m0 := Γ.act first.extraction.x⁻¹ first.l
  let n0 := Γ.act second.extraction.x⁻¹ second.l
  let m := Γ.act config.g m0
  let l := Γ.act config.g first.l
  have hZnmap : (ZAt Γ n0).map c.toMonoidHom = ZAt Γ cp.a := by
    change (z Γ n0).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act,config.maps_new_vertex]
  have hGnmap : (GAt Γ n0).map c.toMonoidHom = GAt Γ cp.a := by
    change conjugateBy (stabilizer Γ n0) config.g⁻¹ = _
    rw [← stabilizer_act,config.maps_new_vertex]
  have hZmmap : (ZAt Γ m0).map c.toMonoidHom = ZAt Γ m := by
    change (z Γ m0).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act]
  have hGmmap : (GAt Γ m0).map c.toMonoidHom = GAt Γ m := by
    change conjugateBy (stabilizer Γ m0) config.g⁻¹ = _
    rw [← stabilizer_act]
  have hZlmap : (ZAt Γ first.l).map c.toMonoidHom = ZAt Γ l := by
    change (z Γ first.l).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act]
  have hfour := nine_three_four_center_indices ctx hb hlarge first second
  have hindex : Nat.card (ZAt Γ cp.a) = 2 * Nat.card (ZAt Γ cp.a ⊓ GAt Γ m : Subgroup G) := by
    rw [← hZnmap,← hGmmap,← Subgroup.map_inf _ _ _ c.injective,
      Subgroup.card_map_of_injective c.injective,Subgroup.card_map_of_injective c.injective]
    exact hfour.2.2.1
  have hinner : Nat.card (ZAt Γ m ⊓ GAt Γ cp.a : Subgroup G) =
      2 * Nat.card (ZAt Γ m ⊓ ZAt Γ l : Subgroup G) := by
    rw [← hZmmap,← hGnmap,← hZlmap,← Subgroup.map_inf _ _ _ c.injective,
      ← Subgroup.map_inf _ _ _ c.injective,
      Subgroup.card_map_of_injective c.injective,Subgroup.card_map_of_injective c.injective]
    exact hfour.2.1
  have hnotOld : ¬ ZAt Γ m ⊓ GAt Γ cp.a ≤ ZAt Γ l := by
    intro hh
    have hc := Subgroup.card_le_of_le (le_inf inf_le_left hh)
    have hp : 0 < Nat.card (ZAt Γ m ⊓ ZAt Γ l : Subgroup G) := Nat.card_pos
    omega
  have hnot := extracted_intersection_not_centralized ctx.sectionSeven Γ cp.a
    (Γ.act config.g cp.a') l (VAt Γ cp.firstStep)
    (first.E.map c.toMonoidHom) (first.A0.map c.toMonoidHom) config.first_actor
    config.first_actor_initial
    ((lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 config.first_actor_initial)
    config.first_geometry
  rw [config.first_new_vertex] at hnot
  have hzero := normalized_native_centralization_forces_mixed_bot ctx hb hlarge first second config hJ
  have heq := fixed_hyperplane_of_mixed_commutator_bot (ZAt Γ cp.a) (GAt Γ m)
    (ZAt Γ m ⊓ GAt Γ cp.a) hindex hzero (hnot hnotOld)
  exact ⟨heq,heq.symm ▸ hindex⟩
end Stellmacher.SectionNine

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
private theorem normalized_terminal_coatom_le_sylow
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    VAt ctx.Γ (ctx.Γ.act config.g ctx.criticalPath.a') ⊓
      GAt ctx.Γ ctx.criticalPath.a ≤ T := by
  have hh := geometric_coatom_le_core_join ctx.Γ ctx.criticalPath.firstStep
    (ctx.Γ.act config.g second.l) _ _ _ _ config.second_geometry
  rw [config.second_new_vertex] at hh
  have hcoatom := config.second_geometry.coatom_eq
  rw [config.second_new_vertex] at hcoatom
  rw [hcoatom] at hh
  exact hh.trans (sup_le (local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
    (local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1)
private theorem map_inf_centralizer
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (A K : Subgroup G) :
    (A ⊓ Subgroup.centralizer (K : Set G)).map f =
      A.map f ⊓ Subgroup.centralizer (K.map f : Set H) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f ha.1, ?_⟩
    change f a ∈ Subgroup.centralizer (K.map f : Set H)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_iff.mp ha.2 k hk)
  · rintro _ ⟨⟨a, ha, rfl⟩, hcent⟩
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    change a ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    apply hf
    simpa only [map_mul] using
      Subgroup.mem_centralizer_iff.mp hcent (f k) (Subgroup.mem_map_of_mem f hk)


public theorem nine_three_canonical_offender_nontrivial
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    sectionSixBarredCritical ctx.hypothesisTwo ≠ ⊥ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hGa : (GAt Γ cp.a).map embedding = P1 := (nine_two_ambient_setup ctx).2.1
  have hZa : (ZAt Γ cp.a).map embedding = sectionSixV S P1 :=
    nine_two_center_eq_sectionSixV ctx hGa
  by_cases hJ : elementaryAbelianMaxJ T ≤
      Subgroup.centralizer (ZAt Γ cp.a : Set G)
  · let m := Γ.act config.g (Γ.act first.extraction.x⁻¹ first.l)
    let d := Γ.act config.g cp.a'
    let Y := ZAt Γ m ⊓ GAt Γ cp.a
    let U := VAt Γ cp.firstStep
    let V := VAt Γ d
    have hZmV : ZAt Γ m ≤ V := by
      change z Γ (Γ.act config.g (Γ.act first.extraction.x⁻¹ first.l)) ≤
        v Γ (Γ.act config.g cp.a')
      rw [z_act,v_act]
      apply Subgroup.map_mono
      rw [v,Γ.vAt_def]
      exact le_sSup ⟨_,first.extraction.neighbor,rfl⟩
    have hYV : Y ≤ V := inf_le_left.trans hZmV
    have hYT : Y ≤ T := (le_inf hYV inf_le_right).trans
      (normalized_terminal_coatom_le_sylow ctx first second config)
    have hYS : Y.map embedding ≤ S := by
      rw [← ctx.map_S]
      exact Subgroup.map_mono hYT
    have hfixed := (normalized_native_centralization_fixed_hyperplane
      ctx hb hlarge first second config hJ).2
    have hindex : Nat.card (sectionSixV S P1) = 2 * Nat.card
        (sectionSixV S P1 ⊓ Subgroup.centralizer (Y.map embedding : Set H) : Subgroup H) := by
      rw [← hZa,← map_inf_centralizer embedding ctx.embedding_injective,
        Subgroup.card_map_of_injective ctx.embedding_injective,
        Subgroup.card_map_of_injective ctx.embedding_injective]
      exact hfixed
    have hquadUV : ⁅⁅U,V⁆,V⁆ = ⊥ := by
      have hq := ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).2.2
      change ⁅⁅v Γ cp.firstStep,v Γ cp.a'⁆,v Γ cp.a'⁆ = ⊥ at hq
      have hh := congrArg (fun K : Subgroup G => K.map (MulAut.conj config.g⁻¹).toMonoidHom) hq
      rw [Subgroup.map_commutator,Subgroup.map_commutator,← v_act,
        config.fixes_firstStep,← v_act,Subgroup.map_bot] at hh
      exact hh
    have hquad : ⁅⁅ZAt Γ cp.a,Y⁆,Y⁆ = ⊥ := by
      apply le_bot_iff.mp
      exact (Subgroup.commutator_mono (Subgroup.commutator_mono
        (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 hYV) hYV).trans_eq hquadUV
    have hquadAmbient : ⁅⁅sectionSixV S P1,Y.map embedding⁆,Y.map embedding⁆ = ⊥ := by
      rw [← hZa,← Subgroup.map_commutator,← Subgroup.map_commutator,hquad,Subgroup.map_bot]
    exact (sixFour_quadratic_index_two_barred_fixed ctx.hypothesisTwo
      (Y.map embedding) hYS hindex hquadAmbient).1
  · have hJambient : ¬ elementaryAbelianMaxJ S ≤
        Subgroup.centralizer (sectionSixV S P1 : Set H) := by
      intro hc
      apply hJ
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      apply ctx.embedding_injective
      have hjm : embedding j ∈ elementaryAbelianMaxJ S := by
        rw [← ctx.map_S,elementaryAbelianMaxJ_map_injective embedding ctx.embedding_injective]
        exact Subgroup.mem_map_of_mem embedding hj
      have hvm : embedding v ∈ sectionSixV S P1 := hZa ▸ Subgroup.mem_map_of_mem embedding hv
      simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp (hc hjm) (embedding v) hvm
    exact (sixFour_native_baumann_barred_fixed ctx.hypothesisTwo hJambient).1
end Stellmacher.SectionNine
