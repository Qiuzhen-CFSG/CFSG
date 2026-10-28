module

public import Stellmacher.Recognition.LargeTerminalFixedLayerKernel
public import Stellmacher.Recognition.LargeTerminalFourFixedCoreFrattini
public import Theory.SpecificGroups.ReeTwo.CoreSecondCenterDerived

/-!
# The original Sylow second center and the derived residual

The first-step module detects the local core: an element of the second
stabilizer acting trivially on the derived residual modulo its center lies
in the core. This first puts the center of the original Sylow in the
residual center, then places its second center in the local core. The
intrinsic Ree core calculation completes the derived containment.

Source: Stellmacher (1997), (10.1)(18)-(20), and Shinoda (1975), (2.3).
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
open scoped commutatorElement
universe u

private theorem second_module_kernel
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (t : G) (ht : t ∈ ctx.second)
    (hcomm : ⁅DerivedAmbient ctx.firstResidual, zpowers t⁆ ≤
      CenterAmbient ctx.firstResidual) : t ∈ twoCoreIn ctx.second := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  have hshort : 1 < cp.length := by rw [ctx.length_three]; decide
  have hP : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup tenCtx.toAmbientSectionNineContext).2.2.1
  have hD : DerivedAmbient ctx.firstResidual = V.map K.subtype :=
    ctx.first_residual_structure.2.2.1
  have hZ : CenterAmbient ctx.firstResidual = Z.map K.subtype :=
    ctx.first_residual_structure.2.1
  let tK : K := ⟨t, (le_sup_right : ctx.second ≤ K) ht⟩
  have htP : tK ∈ P := by
    apply (mem_map_iff_mem K.subtype_injective).mp
    change t ∈ P.map K.subtype
    rwa [hP]
  have hcommK : ⁅V, zpowers tK⁆ ≤ Z := by
    apply (map_le_map_iff_of_injective (f := K.subtype) K.subtype_injective).mp
    rw [map_commutator, MonoidHom.map_zpowers, ← hD, ← hZ]
    exact hcomm
  have hcore := (nine_next_center_commutator_and_kernel
    tenCtx.toAmbientSectionNineContext hshort cp.firstStep ⟨1, Γ.act_one _⟩).2.2
    tK htP |>.mp hcommK
  have hQ : (QAt Γ cp.firstStep).map K.subtype = twoCoreIn ctx.second := by
    let e := P.equivMapOfInjective K.subtype K.subtype_injective
    have hh := pCore_map_iso 2 e
    have hc : (twoCoreIn P).map K.subtype = twoCoreIn (P.map K.subtype) := by
      change ((pCore 2 P).map P.subtype).map K.subtype =
        (pCore 2 (P.map K.subtype)).map (P.map K.subtype).subtype
      rw [← hh, map_map, map_map]
      rfl
    change (Γ.twoCoreAt _).map K.subtype = _
    rw [Γ.twoCoreAt_def]
    change (twoCoreIn P).map K.subtype = _
    rw [hc, hP]
  rw [← hQ]
  exact mem_map_of_mem K.subtype hcore

private theorem sylow_center_le_residual_center
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    (center S).map (S : Subgroup G).subtype ≤ CenterAmbient ctx.firstResidual := by
  have hSP : (S : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  have hRS : ctx.firstResidual ≤ (S : Subgroup G) :=
    (ctx.derived_centralizer_supplement.1 ▸ le_sup_right).trans (by
      rintro x ⟨q, hq, rfl⟩
      exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
        (S.subtype hSP) hq)
  rintro x ⟨s, hs, rfl⟩
  have hsP : (s : G) ∈ ctx.second := hSP s.property
  have hsC : (s : G) ∈ centralizer (ctx.firstResidual : Set G) := by
    apply mem_centralizer_iff.mpr
    intro r hr
    have hrS : r ∈ (S : Subgroup G) := hRS hr
    exact congrArg Subtype.val (mem_center_iff.mp hs ⟨r, hrS⟩)
  have hsComm : ⁅DerivedAmbient ctx.firstResidual, zpowers (s : G)⁆ ≤
      CenterAmbient ctx.firstResidual := by
    have hsD : (s : G) ∈ centralizer (DerivedAmbient ctx.firstResidual : Set G) :=
      centralizer_le (map_subtype_le _) hsC
    have hcyc : zpowers (s : G) ≤ centralizer (DerivedAmbient ctx.firstResidual : Set G) := by
      intro y hy
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
      exact (centralizer (DerivedAmbient ctx.firstResidual : Set G)).zpow_mem hsD n
    have hb : ⁅DerivedAmbient ctx.firstResidual, zpowers (s : G)⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr hcyc)
    rw [hb]
    exact bot_le
  have hsQ := second_module_kernel ctx (s : G) hsP hsComm
  rw [← ctx.core_inf_residual_centralizer]
  exact ⟨hsQ, hsC⟩

private theorem second_center_le_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    Subgroup.upperCentralSeries S 2 ≤
      (twoCoreIn ctx.second).subgroupOf (S : Subgroup G) := by
  have hSP : (S : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  have hRS : ctx.firstResidual ≤ (S : Subgroup G) :=
    (ctx.derived_centralizer_supplement.1 ▸ le_sup_right).trans (by
      rintro x ⟨q, hq, rfl⟩
      exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
        (S.subtype hSP) hq)
  have hD : DerivedAmbient ctx.firstResidual ≤ (S : Subgroup G) :=
    (map_subtype_le _).trans hRS
  have hcommS : ⁅(⊤ : Subgroup S), Subgroup.upperCentralSeries S 2⁆ ≤ center S := by
    rw [commutator_comm]
    simpa only [Subgroup.upperCentralSeries_one] using
      (Subgroup.commutator_upperCentralSeries_top_le S 1)
  have hmap := map_mono (f := (S : Subgroup G).subtype) hcommS
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hmap
  intro x hx
  have hxcyc : zpowers (x : G) ≤
      (Subgroup.upperCentralSeries S 2).map (S : Subgroup G).subtype :=
    zpowers_le.mpr (mem_map_of_mem _ hx)
  have hcomm : ⁅DerivedAmbient ctx.firstResidual, zpowers (x : G)⁆ ≤
      CenterAmbient ctx.firstResidual :=
    (commutator_mono hD hxcyc).trans
      (hmap.trans (sylow_center_le_residual_center ctx))
  exact second_module_kernel ctx (x : G) (hSP x.property) hcomm

/-- The second center of the original Sylow lies in the derived first
residual, given an identification of the actual second core with the Ree
coordinate core. -/
public theorem LargeTerminalContext.second_center_le_derived_residual
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (_hS : Nat.card S = 4096)
    (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core) :
    Subgroup.upperCentralSeries S 2 ≤
      (DerivedAmbient ctx.firstResidual).subgroupOf (S : Subgroup G) := by
  have hQS : twoCoreIn ctx.second ≤ (S : Subgroup G) := by
    have hSP : (S : Subgroup G) ≤ ctx.second :=
      ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S.subtype hSP) hq
  intro x hx
  let q : twoCoreIn ctx.second := ⟨(x : G), second_center_le_core ctx hx⟩
  have hqCenter : q ∈ Subgroup.upperCentralSeries (twoCoreIn ctx.second) 2 := by
    apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
    intro y
    rw [Subgroup.upperCentralSeries_one]
    have hx' := Subgroup.mem_upperCentralSeries_succ_iff.mp hx
      (⟨(y : G), hQS y.property⟩ : S)
    rw [Subgroup.upperCentralSeries_one] at hx'
    apply mem_center_iff.mpr
    intro z
    have hz := mem_center_iff.mp hx'
      (⟨(z : G), hQS z.property⟩ : S)
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def] using
      congrArg Subtype.val hz
  have he : eQ q ∈ Subgroup.upperCentralSeries ReeTwo.Core 2 := by
    have hh : q ∈ (Subgroup.upperCentralSeries ReeTwo.Core 2).comap eQ := by
      rw [Subgroup.comap_upperCentralSeries eQ 2]
      exact hqCenter
    exact hh
  have hderCore : eQ q ∈ commutator ReeTwo.Core :=
    ReeTwo.Core.second_center_le_derived he
  have hderQ : q ∈ commutator (twoCoreIn ctx.second) := by
    have hm : (commutator ReeTwo.Core).map eQ.symm.toMonoidHom =
        commutator (twoCoreIn ctx.second) := by
      rw [map_commutator_eq]
      rw [MonoidHom.range_eq_top_of_surjective eQ.symm.toMonoidHom eQ.symm.surjective]
      rfl
    have hh : eQ.symm (eQ q) ∈
        (commutator ReeTwo.Core).map eQ.symm.toMonoidHom :=
      mem_map_of_mem eQ.symm.toMonoidHom hderCore
    simpa only [eQ.symm_apply_apply, hm] using hh
  have hder : (x : G) ∈ DerivedAmbient (twoCoreIn ctx.second) :=
    mem_map_of_mem (twoCoreIn ctx.second).subtype hderQ
  rw [ctx.second_core_derived_eq] at hder
  exact hder

end Stellmacher.Recognition
