module
public import Stellmacher.SectionNine.NineThreeFinalCoreIntersectionBound
public import Stellmacher.SectionNine.NineThreeFinalCoreTransvectionBound
public import Stellmacher.SectionOne.SmallDisplacementOddCoreLayer

/-!
# Final large-center contradiction for Stellmacher (9.3)

The actual final core-intersection bound makes the initial-center actor's
displacement have order at most two on O₂(C₀)/(Φ(O₂(C₀))R₀). This action
has kernel exactly O₂(C₀). Descending through that kernel gives a faithful
binary action of the original quotient C₀/O₂(C₀), retaining the same
conjugation map and its literal vector module.

The initial center has nontrivial elementary image. Involution rank-nullity
and (1.7) put that small-displacement actor in the odd-core layer. Exact
prescribed-actor generation then contradicts the independently proved
first-residual exclusion. Thus the normalized order-sixteen configuration
cannot occur. The private quotient-action helper keeps the large graph
context out of repeated dependent-action elaboration and returns only the
needed subgroup containment.

Source: Stellmacher (9.3), printed p.50/PDF p.40, the final R₀,C₀ argument
of `refs/files/stellmacher-n-group.pdf`. All contexts and actions are the
production ones; no extra premise enters the numbered theorem.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem small_core_action_odd_layer
    {C V : Type u} [Group C] [Finite C] [Group V] [Finite V]
    [IsElementaryAbelian 2 V]
    (hsolvable : Group.IsSolvable C)
    (action : C →* MulAut V) (hkernel : action.ker = pCore 2 C)
    (internal : Subgroup C) [IsElementaryAbelian 2 internal]
    (hnot : ¬ internal ≤ pCore 2 C)
    (hsmall : Nat.card (commutatorAction (internal.map action) V) ≤ 2) :
    (internal.map (QuotientGroup.mk' (pCore 2 C))).map
      (QuotientGroup.mk' (pPrimeCore 2 (C ⧸ pCore 2 C))) ≤
        pCore 2 ((C ⧸ pCore 2 C) ⧸ pPrimeCore 2 (C ⧸ pCore 2 C)) := by
  classical
  let _ := hsolvable
  let core := pCore 2 C
  let q := QuotientGroup.mk' core
  change action.ker = core at hkernel
  let quotientAction : (C ⧸ core) →* MulAut V :=
    QuotientGroup.lift core action (by rw [hkernel])
  let _ : MulDistribMulAction (C ⧸ core) V := MulDistribMulAction.compHom V quotientAction
  have hformula (actor : C) : quotientAction (q actor) = action actor := rfl
  let Y := internal.map q
  let _ : IsElementaryAbelian 2 Y := IsElementaryAbelian.map q
  have hYne : Y ≠ ⊥ := by
    intro hbot
    have hle : internal ≤ core := by
      have hh := (Subgroup.map_eq_bot_iff internal).mp hbot
      rwa [QuotientGroup.ker_mk'] at hh
    exact hnot hle
  have hfaithful : fixingSubgroup (C ⧸ core) (Set.univ : Set V) = ⊥ := by
    apply bot_unique
    intro actor hactor
    obtain ⟨original,rfl⟩ := QuotientGroup.mk'_surjective core actor
    have htrivial : action original = 1 := by
      ext vector
      exact ((mem_fixingSubgroup_iff (C ⧸ core)).mp hactor) vector (Set.mem_univ vector)
    have hmem : original ∈ core := hkernel ▸ MonoidHom.mem_ker.mpr htrivial
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  have heven : Even (Nat.card (C ⧸ core)) := by
    apply even_iff_two_dvd.mpr
    have htwo : 2 ∣ Nat.card Y :=
      (IsElementaryAbelian.isPGroup 2 Y).card_eq_or_dvd.resolve_left
        (fun hc => hYne (Subgroup.card_eq_one.mp hc))
    exact htwo.trans Y.card_subgroup_dvd_card
  have hquotientCore : pCore 2 (C ⧸ core) = ⊥ := by
    rw [← pCore_map_mk'_eq_of_normal_isPGroup (p := 2) core
      (pCore_isPGroup (p := 2) (G := C)), QuotientGroup.map_mk'_self]
  have hyp : SectionOne.Hypotheses (C ⧸ core) V :=
    ⟨inferInstance, heven, hfaithful, hquotientCore⟩
  rcases subsingleton_or_nontrivial V with hsub | hnon
  · let _ := hsub
    exfalso
    apply hYne
    apply bot_unique
    intro actor _
    apply hfaithful.le
    rw [mem_fixingSubgroup_iff]
    intro vector _
    exact Subsingleton.elim _ _
  let _ := hnon
  have hcomm : commutatorAction Y V ≤ commutatorAction (internal.map action) V := by
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro _ ⟨actor,vector,rfl⟩
    obtain ⟨original,horiginal,heq⟩ := actor.property
    change vector⁻¹ * quotientAction (actor : C ⧸ core) vector ∈ _
    rw [← heq,hformula]
    exact Subgroup.subset_closure
      ⟨⟨action original,Subgroup.mem_map_of_mem action horiginal⟩,vector,Subgroup.mem_top vector,rfl⟩
  have hdisplacement : Nat.card (commutatorAction Y V) ≤ 2 :=
    (Subgroup.card_le_of_le hcomm).trans hsmall
  obtain ⟨sylow,hle⟩ := IsPGroup.exists_le_sylow (IsElementaryAbelian.isPGroup 2 Y)
  exact SectionOne.oneSeven_small_displacement_le_oddCoreLayer hyp sylow Y hle hdisplacement

public theorem nine_three_large_center_false
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (rank : NineThreeNativeActionRankData ctx) : False := by
  classical
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let C := Subgroup.centralizer (mixed.map embedding : Set H)
  let vectors := (ZAt ctx.Γ ctx.criticalPath.a).map embedding
  let internal := vectors.subgroupOf C
  let line := (mixed.map embedding).subgroupOf C
  let core := pCore 2 C
  let q := QuotientGroup.mk' core
  have hgeometry := nine_three_mixed_order_two_and_sylow ctx hb hlarge first second config rank
  have hsolvable := (nine_three_final_centralizer_setup_of_mixed_sylow
    ctx first second config hgeometry).1
  let _ := hsolvable
  have hcoreBound := nine_three_final_core_intersection_card_le_four
    ctx hb hlarge first second config rank
  obtain ⟨normal, hmodule, action, _, hkernel, hsmall⟩ :=
    nine_three_final_core_action_displacement_le_two ctx hb hlarge first second config rank hcoreBound
  let _ := normal
  let layer := frattini core ⊔ line.subgroupOf core
  let V := core ⧸ layer
  let _ : IsElementaryAbelian 2 V := hmodule
  have hdata := nine_three_final_centralizer_center_core ctx hb hlarge first second config
  have hneighbor : ctx.criticalPath.firstStep ∈ neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hneighbor
  let _ : IsElementaryAbelian 2 vectors := IsElementaryAbelian.map embedding
  let _ : IsElementaryAbelian 2 internal := IsElementaryAbelian.subgroupOf hdata.1
  have hnotInternal : ¬ internal ≤ core := by
    intro hle
    have hmap := Subgroup.map_mono (f := C.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hdata.1] at hmap
    exact nine_three_initial_center_not_le_final_centralizer_core
      ctx hb hlarge first second config hmap
  have hbound := small_core_action_odd_layer hsolvable action hkernel internal hnotInternal hsmall
  exact nine_three_final_contradiction_of_initial_center_oddCoreLayer
    ctx hb hlarge first second config hbound

end Stellmacher.SectionNine
