module
public import Stellmacher.SectionEight.EightFourSourceNineFinalCaseReduction
public import Stellmacher.QuotientModuleFixedPoints

/-!
# Transport of source-nine fixed cardinalities

For the actual faithful quotient witness and source-nine configuration, the
J-fixed subgroup has twice the cardinality of the Sylow-fixed subgroup. The
local proof identifies Sylow fixed points with the centered first vertex,
uses the proved index-two intersection, and transports both cardinalities
through the same ordered-edge actor. Reversed orientation contradicts the
supplied endpoint noncommutation. The action and quotient instances remain
those of the supplied witness; the canonical statement is an exact wrapper.
Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.4), p.40.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
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

public theorem eight_four_sylow_fixed_center_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ZAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (S : Set H) =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Za := z Γ cp.a
  let Zfirst := z Γ cp.firstStep
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hback : cp.a ∈ neighborhood Γ cp.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hback
  have hlocal := SevenSix.edge_local_data h Γ cp
  have hSylow : IsSylowTwoIn S (stabilizer Γ cp.a) := hlocal.1.1.1.2.1
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
  apply le_antisymm
  · apply le_trans _ hOmegaFirst
    exact elementary_centralizer_le_omega (inf_le_left.trans hZaS) inf_le_right
      (fun element helement => elemPow_eq_one_of_isElementaryAbelian element helement.1)
  · exact le_inf (hZfirstOmega.trans hOmegaZa) hZfirstCentral

public theorem eight_four_source_nine_fixed_card_transport_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    let Sb := (S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection
    Nat.card (FixedPoints.subgroup (SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a) Sb)
      (ZAt ctx.Γ ctx.criticalPath.a)) =
        2 * Nat.card (FixedPoints.subgroup Sb (ZAt ctx.Γ ctx.criticalPath.a)) := by
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act configuration.y⁻¹ cp.a'
  let h := ctx.sectionSeven
  let Sb := (S.subgroupOf (GAt Γ cp.a)).map w.projection
  have hfixed := eight_four_sylow_fixed_center_local ctx hcenter
  have hfixedCard := w.fixedPoints_card S (cp.S_le_edge_stabilizers.trans inf_le_left)
  dsimp only at hfixedCard
  rw [show ZAt ctx.Γ ctx.criticalPath.a = ZAt Γ cp.a from rfl,
    show ZAt ctx.Γ ctx.criticalPath.firstStep =
      ZAt Γ cp.firstStep from rfl] at hfixed
  rw [hfixed] at hfixedCard
  have hseedCard : Nat.card (w.oneJFixedPoints S) =
      Nat.card (FixedPoints.subgroup (SectionOne.oneJ (V := ZAt Γ cp.a) Sb)
        (ZAt Γ cp.a)) := by
    unfold QuotientModuleWitness.oneJFixedPoints
    exact Subgroup.card_map_of_injective (ZAt Γ cp.a).subtype_injective
  have hindex := eight_four_source_nine_fixed_center_index_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  have heq := eight_four_source_nine_fixed_core_intersection_local ctx hcenter w
    F hbase hcov hsub configuration
  have hle : ZAt Γ configuration.d ≤ F next configuration.d := heq.ge.trans inf_le_left
  have hprod := (ZAt Γ configuration.d).subgroupOf (F next configuration.d) |>.card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hprod
  change Nat.card (ZAt Γ configuration.d) *
    (ZAt Γ configuration.d).relIndex (F next configuration.d) =
      Nat.card (F next configuration.d) at hprod
  change (ZAt Γ configuration.d).relIndex (F next configuration.d) = 2 at hindex
  rw [hindex, mul_comm] at hprod
  have hpos := cp.length_pos
  have hprevious : Γ.adjacent cp.a' (cp.path ⟨cp.length - 1, by omega⟩) := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hpathIndex : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [hpathIndex, cp.path_end] at hedge
    exact Γ.adjacent_symm hedge
  have hfix : Γ.act configuration.x⁻¹ cp.a' = cp.a' := by
    have hmem := (GAt Γ cp.a').inv_mem (configuration.hL0 configuration.hx)
    change configuration.x⁻¹ ∈ (Γ.vertexStabilizer cp.a' : Set H) at hmem
    rwa [Γ.stabilizer_def] at hmem
  have hmiddle : Γ.adjacent cp.a' configuration.d := by
    have hedge := adjacent_act Γ configuration.x⁻¹ hprevious
    rwa [hfix, ← configuration.hd] at hedge
  have hcentral := eight_four_terminal_neighbor_central_local ctx hcenter configuration.d hmiddle
  obtain ⟨actor, horient | horient⟩ :=
    (lemma_seven_one h Γ).edge_not_vertex_transitive.1
      cp.firstStep_adj (Γ.adjacent_symm configuration.hadj)
  · have hF := hcov actor cp.a cp.firstStep
    rw [horient.1, horient.2, hbase] at hF
    have hZ := z_act Γ actor cp.firstStep
    rw [horient.2] at hZ
    have hFcard : Nat.card (F next configuration.d) = Nat.card (w.oneJFixedPoints S) := by
      rw [hF]
      exact Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective
    have hZcard : Nat.card (ZAt Γ configuration.d) = Nat.card (ZAt Γ cp.firstStep) := by
      change Nat.card (z Γ configuration.d) = Nat.card (z Γ cp.firstStep)
      rw [hZ]
      exact Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective
    change Nat.card (FixedPoints.subgroup (SectionOne.oneJ (V := ZAt Γ cp.a) Sb)
      (ZAt Γ cp.a)) = 2 * Nat.card (FixedPoints.subgroup Sb (ZAt Γ cp.a))
    rw [← hseedCard, hfixedCard, ← hFcard, ← hZcard]
    exact hprod.symm
  · have hZendP : z Γ (Γ.act actor cp.a') ≤ stabilizer Γ configuration.d := by
      rw [← horient.1, stabilizer_act, z_act]
      exact Subgroup.map_mono (lemma_seven_four h Γ cp).reverse_containment.1
    have hcomm : ⁅z Γ configuration.d, z Γ (Γ.act actor cp.a')⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hcentral.trans ((SevenSix.centerAmbient_le_centralizer _).trans
          (Subgroup.centralizer_le hZendP)))
    rw [← horient.1, z_act, z_act, ← Subgroup.map_commutator] at hcomm
    exact (ctx.commutator_ne (Subgroup.map_injective (MulAut.conj actor⁻¹).injective
      (hcomm.trans (Subgroup.map_bot _).symm))).elim

public theorem eight_four_source_nine_fixed_card_transport
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    let Sb := (S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection
    Nat.card (FixedPoints.subgroup (SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a) Sb)
      (ZAt ctx.Γ ctx.criticalPath.a)) =
        2 * Nat.card (FixedPoints.subgroup Sb (ZAt ctx.Γ ctx.criticalPath.a))  := by
  exact eight_four_source_nine_fixed_card_transport_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula
    configuration.toLocal hlen

end Stellmacher.SectionEight
