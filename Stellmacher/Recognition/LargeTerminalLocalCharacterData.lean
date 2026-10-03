module

public import Stellmacher.Recognition.LargeTerminalCentralizerCore
public import Stellmacher.SectionTen.TenOneLargeSylowCard

/-!
# Native Sylow data for the large terminal local character

The residual and the second local core restrict to normal subgroups of the
prescribed Sylow. At Sylow order 4096 their orders are 512 and 1024. The
Frobenius quotient embeds the Sylow image in its cyclic complement. A terminal
module involution escapes the first core; Sylow conjugacy inside that vertex
moves it into the prescribed Sylow without losing this escape.

These are the native subgroup inputs for character extension; no splitting
or character is assumed. Source: Stellmacher (10.1)(18)--(20), together with
the critical module/core noncontainment and the neighborhood containment (9.7).
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
universe u

private theorem core_map_injective_local
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (P : Subgroup G) :
    (twoCoreIn P).map f = twoCoreIn (P.map f) := by
  let e := P.equivMapOfInjective f hf
  have h := pCore_map_iso 2 e
  change ((pCore 2 P).map P.subtype).map f =
    (pCore 2 (P.map f)).map (P.map f).subtype
  rw [← h, map_map, map_map]
  rfl

private theorem first_core_map
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    (QAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
      (ctx.first ⊔ ctx.second).subtype = twoCoreIn ctx.second := by
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  change (ctx.terminal.Γ.twoCoreAt _).map _ = _
  rw [ctx.terminal.Γ.twoCoreAt_def,
    core_map_injective_local _ (ctx.first ⊔ ctx.second).subtype_injective]
  exact congrArg twoCoreIn (nine_two_ambient_setup tenCtx.toAmbientSectionNineContext).2.2.1

private theorem second_core_le_sylow
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) : twoCoreIn ctx.second ≤ (S : Subgroup G) := by
  have hSP : (S : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  rintro x ⟨p, hp, rfl⟩
  exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal (S.subtype hSP) hp

/-- The actual first residual is normal in the prescribed Sylow. -/
public theorem LargeTerminalContext.local_character_residual_normal
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    (ctx.firstResidual.subgroupOf (S : Subgroup G)).Normal := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let P := GAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep
  let E := EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep
  have hE : E = twoResidualIn P := ctx.terminal.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRP : twoCoreIn E ≤ P := (twoCoreIn_le E).trans hEP
  have hPN : P ≤ normalizer (twoCoreIn E : Set K) :=
    (normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hmap : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup
      (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext).2.2.1
  have hN : ctx.second ≤ normalizer (ctx.firstResidual : Set G) := by
    rw [← hmap]
    exact (map_mono hPN).trans (le_normalizer_map K.subtype)
  exact normal_subgroupOf_of_le_normalizer
    (ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1.trans hN)

/-- The second local core is normal in the prescribed Sylow. -/
public theorem LargeTerminalContext.local_character_core_normal
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ((twoCoreIn ctx.second).subgroupOf (S : Subgroup G)).Normal := by
  have hN := (pCore 2 ctx.second).le_normalizer_map ctx.second.subtype
  rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hN
  exact normal_subgroupOf_of_le_normalizer
    (ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1.trans hN)

/-- The residual is contained in the local core, inside the prescribed Sylow. -/
public theorem LargeTerminalContext.local_character_residual_le_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ctx.firstResidual.subgroupOf (S : Subgroup G) ≤
      (twoCoreIn ctx.second).subgroupOf (S : Subgroup G) := by
  obtain ⟨_, _, _, hlow, hhigh, _⟩ := ctx.involution_centralizer_core
  exact fun _ hx => hhigh (hlow hx)

/-- Restricting the residual to the prescribed Sylow retains its order 512. -/
public theorem LargeTerminalContext.local_character_residual_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    Nat.card (ctx.firstResidual.subgroupOf (S : Subgroup G)) = 512 := by
  obtain ⟨_, _, _, hlow, hhigh, _⟩ := ctx.involution_centralizer_core
  exact (Nat.card_congr (subgroupOfEquivOfLe
    (hlow.trans (hhigh.trans (second_core_le_sylow ctx)))).toEquiv).trans
      ctx.first_residual_structure.1

/-- At the upper Sylow endpoint the native local core has order 1024. -/
public theorem LargeTerminalContext.local_character_core_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    Nat.card ((twoCoreIn ctx.second).subgroupOf (S : Subgroup G)) = 1024 := by
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let cp := ctx.terminal.criticalPath
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset ctx.terminal.Γ cp 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  have hratio := ten_one_large_sylow_card tenCtx middle hpath ctx.noTransvections
  have hT : Nat.card ((S : Subgroup G).subgroupOf (ctx.first ⊔ ctx.second)) = Nat.card S :=
    Nat.card_congr (subgroupOfEquivOfLe ctx.terminal.sylow_le_join).toEquiv
  have hQ : Nat.card (twoCoreIn ctx.second) =
      Nat.card (QAt ctx.terminal.Γ cp.firstStep) := by
    rw [← first_core_map ctx]
    exact card_map_of_injective (ctx.first ⊔ ctx.second).subtype_injective
  change Nat.card ((S : Subgroup G).subgroupOf (ctx.first ⊔ ctx.second)) =
    4 * Nat.card (QAt ctx.terminal.Γ cp.firstStep) at hratio
  rw [hT, hS, ← hQ] at hratio
  rw [Nat.card_congr (subgroupOfEquivOfLe (second_core_le_sylow ctx)).toEquiv]
  omega

private theorem two_subgroup_cyclic
    (φ : C4 →* MulAut C5) (A : Subgroup (SemidirectProduct C5 C4 φ))
    (hA : IsPGroup 2 A) : IsCyclic A := by
  let projection : SemidirectProduct C5 C4 φ →* C4 := SemidirectProduct.rightHom
  have hfive : IsPGroup 5 C5 := IsPGroup.of_card (n := 1) (by simp [C5])
  have hkernel : IsPGroup 5 projection.ker := by
    rw [show projection.ker = (SemidirectProduct.inl : C5 →*
      SemidirectProduct C5 C4 φ).range from SemidirectProduct.range_inl_eq_ker_rightHom.symm]
    exact hfive.of_surjective _ (MonoidHom.rangeRestrict_surjective SemidirectProduct.inl)
  have hd : Disjoint A projection.ker := hA.disjoint_of_coprime hkernel (by decide)
  apply isCyclic_of_injective (projection.comp A.subtype)
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro x hx
  exact Subtype.ext (hd.le_bot ⟨x.property, hx⟩)

/-- The quotient by the native local core is cyclic. The normality argument
is explicit so this can be used with any installed proof of core normality. -/
public theorem LargeTerminalContext.local_character_quotient_cyclic
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S)
    [((twoCoreIn ctx.second).subgroupOf (S : Subgroup G)).Normal] :
    IsCyclic (S ⧸ (twoCoreIn ctx.second).subgroupOf (S : Subgroup G)) := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let cp := ctx.terminal.criticalPath
  let P := GAt ctx.terminal.Γ cp.firstStep
  let Q := QAt ctx.terminal.Γ cp.firstStep
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset ctx.terminal.Γ cp 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  have hmap : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup tenCtx.toAmbientSectionNineContext).2.2.1
  let e : P ≃* ctx.second := (P.equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)
  have hSP : (S : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  let f : S →* P := e.symm.toMonoidHom.comp (inclusion hSP)
  have hf (s : S) : ((f s : K) : G) = (s : G) := by
    change ((e (f s) : ctx.second) : G) = (s : G)
    simp [f]
  obtain ⟨φ, _, projection, _, hker⟩ :=
    ten_one_large_first_frobenius tenCtx middle hpath ctx.noTransvections
  let π := projection.comp f
  have hπ : π.ker = (twoCoreIn ctx.second).subgroupOf (S : Subgroup G) := by
    ext s
    change projection (f s) = 1 ↔ (s : G) ∈ twoCoreIn ctx.second
    change f s ∈ projection.ker ↔ _
    rw [hker]
    change (f s : K) ∈ Q ↔ _
    rw [← first_core_map ctx, ← hf s]
    exact (mem_map_iff_mem K.subtype_injective).symm
  have htwo : IsPGroup 2 π.range :=
    S.isPGroup'.of_surjective π.rangeRestrict (MonoidHom.rangeRestrict_surjective π)
  let _ : IsCyclic π.range := two_subgroup_cyclic φ π.range htwo
  exact ((QuotientGroup.quotientMulEquivOfEq hπ.symm).trans
    (QuotientGroup.quotientKerEquivRange π)).isCyclic.mpr inferInstance

private theorem conjugate_involution_into_sylow
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (Q : Subgroup G) [Q.Normal] (x : G) (hx : x ^ 2 = 1) (hxQ : x ∉ Q) :
    ∃ t : S, t ^ 2 = 1 ∧ (t : G) ∉ Q := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hx
  obtain ⟨T, hT⟩ := (IsElementaryAbelian.isPGroup 2 (zpowers x)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have ht : MulAut.conj g x ∈ (S : Subgroup G) := by
    rw [← hg]
    exact smul_mem_pointwise_smul x (MulAut.conj g) (T : Subgroup G) (hT (mem_zpowers x))
  refine ⟨⟨MulAut.conj g x, ht⟩, Subtype.ext ?_, ?_⟩
  · change (MulAut.conj g x) ^ 2 = 1
    rw [← map_pow, hx, map_one]
  · intro h
    have hh := Subgroup.Normal.conj_mem (inferInstance : Q.Normal) _ h g⁻¹
    apply hxQ
    simpa [MulAut.conj_apply, mul_assoc] using hh

/-- The prescribed Sylow contains an involution outside its local core. -/
public theorem LargeTerminalContext.local_character_escaping_involution
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ∃ t : S, t ^ 2 = 1 ∧
      t ∉ (twoCoreIn ctx.second).subgroupOf (S : Subgroup G) := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  let P := GAt Γ cp.firstStep
  let Q := QAt Γ cp.firstStep
  let V := VAt Γ cp.a'
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle := ⟨⟨2, by omega⟩, rfl, rfl⟩
  obtain ⟨_, hfirst, hterminal, hne⟩ := sectionTenOpeningGeometry tenCtx middle hpath
  have hVP : V ≤ P := by
    have hVQ : V ≤ QAt Γ middle := (show V ≤ GeneratedNeighborhoodV Γ middle from
      le_sSup ⟨_, (mem_neighborhood_iff_adjacent Γ).mpr hterminal, rfl⟩).trans
        (nine_seven_neighborhood_le_own_core tenCtx.toLocalContext.toSectionNineLocalContext
          (by change 2 < cp.length; omega) middle)
    exact hVQ.trans ((lemma_seven_three tenCtx.sectionSeven Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent Γ).mpr hfirst) default).2.2
  have hVelementary : IsElementaryAbelian 2 V := by
    obtain ⟨actor, hactor⟩ := (lemma_seven_one tenCtx.sectionSeven Γ).local_transitivity
      middle ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
        ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
    have hb : 1 < cp.length := by omega
    let _ : IsElementaryAbelian 2 (VAt Γ cp.firstStep) :=
      ((lemma_seven_five tenCtx.sectionSeven Γ cp ctx.commuting).longer_case hb).1
    change Γ.act (actor : K) cp.firstStep = cp.a' at hactor
    change IsElementaryAbelian 2 (VAt Γ cp.a')
    rw [← hactor, VAt, v_act]
    exact IsElementaryAbelian.map (MulAut.conj (actor : K)⁻¹).toMonoidHom
  have hescape : ¬ V ≤ Q :=
    ten_one_neighbor_module_not_le_core tenCtx middle hpath hterminal hfirst hne.symm
  obtain ⟨x, hxV, hxQ⟩ : ∃ x : K, x ∈ V ∧ x ∉ Q := by
    simpa only [SetLike.le_def, not_forall, exists_prop] using hescape
  let _ := hVelementary
  have hx2 : x ^ 2 = 1 := congrArg (fun v : V => (v : K))
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) ⟨x, hxV⟩)
  have hmap : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup tenCtx.toAmbientSectionNineContext).2.2.1
  have hxP : (x : G) ∈ ctx.second := hmap ▸ mem_map_of_mem K.subtype (hVP hxV)
  let xP : ctx.second := ⟨(x : G), hxP⟩
  have hxP2 : xP ^ 2 = 1 := Subtype.ext (congrArg (fun k : K => (k : G)) hx2)
  have hxPC : xP ∉ pCore 2 ctx.second := by
    intro hx
    have hm : (x : G) ∈ twoCoreIn ctx.second := mem_map_of_mem ctx.second.subtype hx
    rw [← first_core_map ctx] at hm
    exact hxQ ((mem_map_iff_mem K.subtype_injective).mp hm)
  have hSP : (S : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  obtain ⟨y, hy2, hyC⟩ := conjugate_involution_into_sylow (S.subtype hSP)
    (pCore 2 ctx.second) xP hxP2 hxPC
  refine ⟨⟨((y : ctx.second) : G), y.property⟩, ?_, ?_⟩
  · exact Subtype.ext (congrArg (fun y : S.subtype hSP => ((y : ctx.second) : G)) hy2)
  · intro hy
    apply hyC
    exact (mem_map_iff_mem ctx.second.subtype_injective).mp hy

end Stellmacher.Recognition
