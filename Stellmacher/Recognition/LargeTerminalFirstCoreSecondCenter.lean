module

public import Stellmacher.Recognition.LargeTerminalContext
public import Stellmacher.Recognition.LargeTerminalDerivedSecondCenterBound
public import Stellmacher.Recognition.LargeTerminalSecondCenterDerived
public import Theory.GroupTheory.PGroup.SmallElementaryNormal

/-!
# The neighboring core and the second center of the original Sylow

The actual first core is the centralizer, inside the prescribed Sylow S,
of its own omega-center W. The edge-centralizer identity (7.4) supplies
this equality; (9.3) and the core omega-center theorem give |W| = 4.
All three subgroups are transported from the original graph through the
inclusion of the generated join, so no subgroup is selected by order.

The normal elementary four-group W lies in Z₂(S): the commutator of a
normal subgroup of order four with a two-group is central. Consequently
C_S(Z₂(S)) lies in the actual first core. The faithful five-four action
bounds the intersection of the derived residual with Z₂(S) by four.
An identification of the actual second core with the Ree coordinate core
puts Z₂(S) in that derived residual, so |Z₂(S)| ≤ 4. Thus W = Z₂(S),
and the actual first core is C_S(Z₂(S)). No Sylow model is assumed.

Source: Stellmacher, Journal of Algebra 190 (1997), (7.4), (9.3), and the
Section Ten opening, via `NineThreeCoreOmega`. The small normal subgroup
argument is `PGroup.SmallElementaryNormal`. The derived-residual bounds
come from `LargeTerminalDerivedSecondCenterBound` and
`LargeTerminalSecondCenterDerived`.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped commutatorElement
universe u

private theorem core_le_sylow
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) : twoCoreIn ctx.first ≤ (S : Subgroup G) := by
  have hSP : (S : Subgroup G) ≤ ctx.first :=
    ctx.terminal.hypothesisTwo.fiveOne.P1_mem.1.2.1.1
  rintro x ⟨p, hp, rfl⟩
  exact (pCore_isPGroup (p := 2) (G := ctx.first)).le_sylow_of_normal (S.subtype hSP) hp

private theorem core_omega_geometry
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    Nat.card (omegaOneCenter (twoCoreIn ctx.first)) = 4 ∧
    (S : Subgroup G) ⊓ centralizer (omegaOneCenter (twoCoreIn ctx.first) : Set G) =
      twoCoreIn ctx.first := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  let nc := (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext
  let P := GAt Γ cp.a
  have hP : P.map K.subtype = ctx.first := (nine_two_ambient_setup nc).2.1
  have hQ : (QAt Γ cp.a).map K.subtype = twoCoreIn ctx.first := by
    let e := P.equivMapOfInjective K.subtype K.subtype_injective
    have h := pCore_map_iso 2 e
    have hh : (twoCoreIn P).map K.subtype = twoCoreIn (P.map K.subtype) := by
      change ((pCore 2 P).map P.subtype).map K.subtype =
        (pCore 2 (P.map K.subtype)).map (P.map K.subtype).subtype
      rw [← h, map_map, map_map]
      rfl
    change (Γ.twoCoreAt _).map K.subtype = _
    rw [Γ.twoCoreAt_def]
    change (twoCoreIn P).map K.subtype = _
    rw [hh, hP]
  have hb : 1 < cp.length := by
    have hl : cp.length = 3 := ctx.length_three
    omega
  have hW : (ZAt Γ cp.a).map K.subtype = omegaOneCenter (twoCoreIn ctx.first) := by
    rw [← hQ]
    exact (congrArg (map K.subtype)
      (nine_three_core_omega_eq_center nc hb cp.a ⟨1, Γ.act_one _⟩)).symm.trans
      (omegaOneCenterAmbient_map_injective K.subtype K.subtype_injective _).symm
  constructor
  · rw [← hW, card_map_of_injective K.subtype_injective]
    exact (lemma_nine_three_ambient nc hb cp.a ⟨1, Γ.act_one _⟩).2
  · have he := (lemma_seven_four ctx.terminal.sectionSeven Γ cp).edge_centralizer
    change ((S : Subgroup G).subgroupOf K) ⊓ centralizer (ZAt Γ cp.a : Set K) = QAt Γ cp.a at he
    apply le_antisymm
    · rintro x ⟨hxS, hxC⟩
      let k : K := ⟨x, ctx.terminal.sylow_le_join hxS⟩
      have hk : k ∈ QAt Γ cp.a := by
        rw [← he]
        refine ⟨hxS, mem_centralizer_iff.mpr ?_⟩
        intro y hy
        apply Subtype.ext
        exact mem_centralizer_iff.mp hxC y (hW ▸ mem_map_of_mem K.subtype hy)
      exact hQ ▸ mem_map_of_mem K.subtype hk
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := hQ.symm ▸ hx
      have h := he.ge hk
      refine ⟨h.1, mem_centralizer_iff.mpr ?_⟩
      intro y hy
      obtain ⟨v, hv, rfl⟩ := hW.symm ▸ hy
      exact congrArg Subtype.val (mem_centralizer_iff.mp h.2 v hv)

private theorem normalizer_le_normalizer_omegaCenter
    {G : Type u} [Group G] (Q : Subgroup G) :
    normalizer (Q : Set G) ≤ normalizer (omegaOneCenter Q : Set G) := by
  let K : Subgroup Q :=
    (omega₁ (G := center Q) (p := 2)).map (center Q).subtype
  let _ : (omega₁ (G := center Q) (p := 2)).Characteristic := omega₁_characteristic (center Q)
  let _ : K.Characteristic := inferInstance
  exact BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic Q K

/-- The first-core omega-center belongs to the second center of the original Sylow. -/
public theorem LargeTerminalContext.first_core_omega_le_second_center
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    (omegaOneCenter (twoCoreIn ctx.first)).subgroupOf (S : Subgroup G) ≤
      Subgroup.upperCentralSeries S 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := twoCoreIn ctx.first
  let W := omegaOneCenter Q
  have hWS : W ≤ (S : Subgroup G) := (map_subtype_le _).trans (core_le_sylow ctx)
  have hSN : (S : Subgroup G) ≤ normalizer (Q : Set G) :=
    ctx.terminal.hypothesisTwo.fiveOne.P1_mem.1.2.1.1.trans
      ((normal_subgroupOf_iff_le_normalizer (twoCoreIn_le ctx.first)).mp (twoCoreIn_normal ctx.first))
  let _ : (W.subgroupOf (S : Subgroup G)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr
      (hSN.trans (normalizer_le_normalizer_omegaCenter Q))
  let _ : IsElementaryAbelian 2 W := omegaOneCenterAmbient_elementaryAbelian Q
  let _ : IsElementaryAbelian 2 (W.subgroupOf (S : Subgroup G)) := IsElementaryAbelian.subgroupOf hWS
  have hcard : Nat.card (W.subgroupOf (S : Subgroup G)) ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWS).toEquiv]
    exact (core_omega_geometry ctx).1.le
  have hcomm := commutator_le_center_of_elementary_card_le_four S.isPGroup'
    (W.subgroupOf (S : Subgroup G)) hcard
  intro x hx
  apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
  intro y
  rw [Subgroup.upperCentralSeries_one]
  exact hcomm (commutator_mem_commutator hx (mem_top y))

/-- The actual first core is the Sylow centralizer of its own omega-center. -/
public theorem LargeTerminalContext.first_core_eq_centralizer_omega
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    (twoCoreIn ctx.first).subgroupOf (S : Subgroup G) =
      centralizer ((omegaOneCenter (twoCoreIn ctx.first)).subgroupOf (S : Subgroup G) : Set S) := by
  have hWS : omegaOneCenter (twoCoreIn ctx.first) ≤ (S : Subgroup G) :=
    (map_subtype_le _).trans (core_le_sylow ctx)
  ext x
  constructor
  · intro hx
    have hc := ((core_omega_geometry ctx).2.ge hx).2
    apply mem_centralizer_iff.mpr
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.mp hc y hy)
  · intro hx
    apply (core_omega_geometry ctx).2.le
    refine ⟨x.property, mem_centralizer_iff.mpr ?_⟩
    intro y hy
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx (⟨y, hWS hy⟩ : S) hy)

/-- The centralizer of the second center lies in the actual neighboring core. -/
public theorem LargeTerminalContext.second_center_centralizer_le_first_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    centralizer (Subgroup.upperCentralSeries S 2 : Set S) ≤
      (twoCoreIn ctx.first).subgroupOf (S : Subgroup G) := by
  rw [ctx.first_core_eq_centralizer_omega]
  exact centralizer_le (ctx.first_core_omega_le_second_center)

/-- The actual first-core omega-center has four elements inside the original Sylow. -/
public theorem LargeTerminalContext.first_core_omega_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    Nat.card ((omegaOneCenter (twoCoreIn ctx.first)).subgroupOf (S : Subgroup G)) = 4 := by
  have hWS : omegaOneCenter (twoCoreIn ctx.first) ≤ (S : Subgroup G) :=
    (map_subtype_le _).trans (core_le_sylow ctx)
  rw [Nat.card_congr (subgroupOfEquivOfLe hWS).toEquiv]
  exact (core_omega_geometry ctx).1

/-- A second-center upper bound identifies it with the actual first-core omega-center. -/
public theorem LargeTerminalContext.second_center_eq_first_core_omega_of_card_le_four
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S)
    (hcard : Nat.card (Subgroup.upperCentralSeries S 2) ≤ 4) :
    Subgroup.upperCentralSeries S 2 =
      (omegaOneCenter (twoCoreIn ctx.first)).subgroupOf (S : Subgroup G) := by
  exact (eq_of_le_of_card_ge ctx.first_core_omega_le_second_center
    (by rw [ctx.first_core_omega_card]; exact hcard)).symm

/-- The intrinsic neighboring-core identity reduces to bounding the second center. -/
public theorem LargeTerminalContext.first_core_eq_second_center_centralizer_of_card_le_four
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S)
    (hcard : Nat.card (Subgroup.upperCentralSeries S 2) ≤ 4) :
    (twoCoreIn ctx.first).subgroupOf (S : Subgroup G) =
      centralizer (Subgroup.upperCentralSeries S 2 : Set S) := by
  rw [ctx.second_center_eq_first_core_omega_of_card_le_four hcard]
  exact ctx.first_core_eq_centralizer_omega

/-- The second center is the omega-center of the actual neighboring core.
Only the actual second core, rather than the whole Sylow, is identified
with a Ree coordinate group. -/
public theorem LargeTerminalContext.second_center_eq_first_core_omega
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core) :
    Subgroup.upperCentralSeries S 2 =
      (omegaOneCenter (twoCoreIn ctx.first)).subgroupOf (S : Subgroup G) := by
  apply ctx.second_center_eq_first_core_omega_of_card_le_four
  have hbound := ctx.derived_inf_second_center_card_le_four
  rwa [inf_eq_right.mpr (ctx.second_center_le_derived_residual hS eQ)] at hbound

/-- The second center of the original Sylow has order four. -/
public theorem LargeTerminalContext.second_center_card_eq_four
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core) :
    Nat.card (Subgroup.upperCentralSeries S 2) = 4 := by
  rw [ctx.second_center_eq_first_core_omega hS eQ]
  exact ctx.first_core_omega_card

/-- The actual neighboring core is the centralizer of the second center
inside the original Sylow. -/
public theorem LargeTerminalContext.first_core_eq_second_center_centralizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core) :
    (twoCoreIn ctx.first).subgroupOf (S : Subgroup G) =
      centralizer (Subgroup.upperCentralSeries S 2 : Set S) := by
  rw [ctx.second_center_eq_first_core_omega hS eQ]
  exact ctx.first_core_eq_centralizer_omega

end Stellmacher.Recognition
