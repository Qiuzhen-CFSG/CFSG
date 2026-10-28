module

public import Stellmacher.Recognition.LargeTerminalDerivedCentralizer
public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData
public import Stellmacher.SectionTen.TenOneLargeCoreDerivedContainment
public import Theory.GroupAction.FiveFourFixedQuotientKernel

/-!
# Large fixed layers detect the full involution-centralizer core

Write Q for the second local core, R for the first residual, D for R', and
Z for Z(R). The lower Section Ten results give Q' = D. Consequently the
full centralizer of the omega-central involution normalizes D, since its
two-core is Q at Sylow order 4096.

An element of square one in the second local group that fixes a subgroup
of D of order at least sixteen modulo Z belongs to Q. Indeed D/Z is
elementary of order sixteen, and the faithful five-four quotient action
has only four fixed points for a nontrivial involution. A fixed layer of
order sixteen gives at least eight fixed quotient points.

For the full involution centralizer, conjugate the element into the
prescribed Sylow within that centralizer. Both D and Z are invariant, so
the large fixed layer survives this conjugation. The local test applies;
normality of Q then returns the original element to Q. No identification
of the full centralizer with the second local group is needed.

Source: Thompson VI, printed p.630, the bound on the fixed subgroup of
D*/Z* immediately before transport; Stellmacher (10.1)(18)--(20).
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup

universe u

private theorem first_core_image
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    (QAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
      (ctx.first ⊔ ctx.second).subtype = twoCoreIn ctx.second := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let P := GAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep
  have hP : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup
      (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext).2.2.1
  have hcore : (twoCoreIn P).map K.subtype = twoCoreIn (P.map K.subtype) := by
    let e := P.equivMapOfInjective K.subtype K.subtype_injective
    have h := pCore_map_iso 2 e
    change ((pCore 2 P).map P.subtype).map K.subtype =
      (pCore 2 (P.map K.subtype)).map (P.map K.subtype).subtype
    rw [← h, map_map, map_map]
    rfl
  change (ctx.terminal.Γ.twoCoreAt _).map K.subtype = _
  rw [ctx.terminal.Γ.twoCoreAt_def]
  change (twoCoreIn P).map K.subtype = _
  rw [hcore, hP]

/-- The derived subgroup of the full local core is the derived residual. -/
public theorem LargeTerminalContext.second_core_derived_eq
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    DerivedAmbient (twoCoreIn ctx.second) = DerivedAmbient ctx.firstResidual := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let cp := ctx.terminal.criticalPath
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset ctx.terminal.Γ cp 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  have h := ten_one_large_first_core_derived_le_module
    tenCtx middle hpath ctx.noTransvections
  change DerivedAmbient (QAt ctx.terminal.Γ cp.firstStep) ≤
    VAt ctx.terminal.Γ cp.firstStep at h
  have hmap := map_mono (f := K.subtype) h
  rw [show DerivedAmbient (QAt ctx.terminal.Γ cp.firstStep) =
    ⁅QAt ctx.terminal.Γ cp.firstStep, QAt ctx.terminal.Γ cp.firstStep⁆ from
      map_subtype_commutator _, map_commutator, first_core_image ctx] at hmap
  have hRQ : ctx.firstResidual ≤ twoCoreIn ctx.second :=
    (ctx.derived_centralizer_supplement.1 ▸ le_sup_right)
  rw [show DerivedAmbient (twoCoreIn ctx.second) =
    ⁅twoCoreIn ctx.second, twoCoreIn ctx.second⁆ from map_subtype_commutator _]
  apply le_antisymm
  · rwa [ctx.first_residual_structure.2.2.1]
  · rw [show DerivedAmbient ctx.firstResidual =
      ⁅ctx.firstResidual, ctx.firstResidual⁆ from map_subtype_commutator _]
    exact commutator_mono hRQ hRQ

/-- The full distinguished involution centralizer normalizes the derived
residual, because that subgroup is the derived group of its two-core. -/
public theorem LargeTerminalContext.involution_centralizer_normalizes_derived
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    centralizer ({z} : Set G) ≤ normalizer (DerivedAmbient ctx.firstResidual : Set G) := by
  let C := centralizer ({z} : Set G)
  have hCQ : C ≤ normalizer (twoCoreIn ctx.second : Set G) := by
    rw [← (ctx.involution_centralizer_core_eq_at_generator hS z hgen).1]
    have h := (pCore 2 C).le_normalizer_map C.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  rw [← ctx.second_core_derived_eq, show DerivedAmbient (twoCoreIn ctx.second) =
    ⁅twoCoreIn ctx.second, twoCoreIn ctx.second⁆ from map_subtype_commutator _]
  intro c hc
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hCQ hc)]

private theorem first_fixed_layer_detects_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S)
    (t : (ctx.first ⊔ ctx.second : Subgroup G))
    (ht : t ∈ GAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep)
    (ht2 : t ^ 2 = 1)
    (E : Subgroup (ctx.first ⊔ ctx.second : Subgroup G))
    (hEV : E ≤ VAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep)
    (hE : 16 ≤ Nat.card E)
    (hcomm : ⁅E, zpowers t⁆ ≤ ZAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep) :
    t ∈ QAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := tenCtx.Γ
  let cp := tenCtx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle := ⟨⟨2, by omega⟩, rfl, rfl⟩
  have hshort : 1 < cp.length := by omega
  have hdata := nine_next_center_commutator_and_kernel
    tenCtx.toAmbientSectionNineContext hshort cp.firstStep ⟨1, Γ.act_one _⟩
  have hZcard : Nat.card Z = 2 := hdata.1
  have hZV : Z ≤ V := hdata.2.1.symm.le.trans
    (le_normalizer_iff_commutator_le_left.mp
      ((show QAt Γ cp.firstStep ≤ P from by
        change Γ.twoCoreAt _ ≤ _
        rw [Γ.twoCoreAt_def]
        exact twoCoreIn_le _).trans (stabilizer_le_normalizer_v Γ _)))
  have hVcard : Nat.card V = 32 := by
    have hcard : Nat.card (DerivedAmbient ctx.firstResidual) = 32 :=
      (card_map_of_injective ctx.firstResidual.subtype_injective).trans
        ctx.first_residual_structure.2.2.2.2.1
    rw [ctx.first_residual_structure.2.2.1,
      card_map_of_injective K.subtype_injective] at hcard
    exact hcard
  obtain ⟨hN, hW, action, hformula, hkernel⟩ :=
    nine_next_quotient_conjugation_action tenCtx.toAmbientSectionNineContext
      hshort cp.firstStep ⟨1, Γ.act_one _⟩
  let _ : (Z.subgroupOf V).Normal := hN
  let _ : IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V) := hW
  have hWcard : Nat.card (V ⧸ Z.subgroupOf V) = 16 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (subgroupOfEquivOfLe hZV).toEquiv, hZcard, hVcard] at hh
    omega
  obtain ⟨φ, hφ, π, hπ, hker⟩ :=
    ten_one_large_first_frobenius tenCtx middle hpath ctx.noTransvections
  have hk : π.ker = action.ker := by
    rw [hker, hkernel]
    change (Γ.twoCoreAt _).subgroupOf P = pCore 2 P
    rw [Γ.twoCoreAt_def]
    exact comap_map_eq_self_of_injective P.subtype_injective _
  have hm := Theory.GroupAction.mem_ker_of_five_four_quotient_action_layer
    P V Z hZV hWcard hZcard.le (stabilizer_le_normalizer_v Γ _)
    φ hφ π hπ action hk hformula ⟨t, ht⟩ (Subtype.ext ht2) E hEV hE hcomm
  rw [hker] at hm
  exact hm

/-- In the second local group, sixteen points fixed modulo the residual
center force an element of square one into the local two-core. -/
public theorem LargeTerminalContext.second_fixed_layer_mem_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S)
    (t : G) (ht : t ∈ ctx.second) (ht2 : t ^ 2 = 1)
    (E : Subgroup G) (hED : E ≤ DerivedAmbient ctx.firstResidual)
    (hE : 16 ≤ Nat.card E)
    (hcomm : ⁅E, zpowers t⁆ ≤ CenterAmbient ctx.firstResidual) :
    t ∈ twoCoreIn ctx.second := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  have hP : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup
      (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext).2.2.1
  have hD : DerivedAmbient ctx.firstResidual = V.map K.subtype :=
    ctx.first_residual_structure.2.2.1
  have hZ : CenterAmbient ctx.firstResidual = Z.map K.subtype :=
    ctx.first_residual_structure.2.1
  have htK : t ∈ K := (le_sup_right : ctx.second ≤ K) ht
  let tK : K := ⟨t, htK⟩
  have htP : tK ∈ P := by
    apply (mem_map_iff_mem K.subtype_injective).mp
    change t ∈ P.map K.subtype
    rwa [hP]
  have hEK : E ≤ K := hED.trans (hD ▸ map_subtype_le V)
  let E₀ := E.subgroupOf K
  have hE₀V : E₀ ≤ V := by
    intro e he
    apply (mem_map_iff_mem K.subtype_injective).mp
    exact hD ▸ hED he
  have hE₀ : 16 ≤ Nat.card E₀ := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv]
    exact hE
  have hcomm₀ : ⁅E₀, zpowers tK⁆ ≤ Z := by
    apply (map_le_map_iff_of_injective (f := K.subtype) K.subtype_injective).mp
    rw [map_commutator, MonoidHom.map_zpowers]
    change ⁅(E.subgroupOf K).map K.subtype, zpowers t⁆ ≤ Z.map K.subtype
    rw [map_subgroupOf_eq_of_le hEK, ← hZ]
    exact hcomm
  have htQ := first_fixed_layer_detects_core ctx tK htP
    (Subtype.ext ht2) E₀ hE₀V hE₀ hcomm₀
  rw [← first_core_image ctx]
  exact mem_map_of_mem K.subtype htQ

/-- In the full omega-central involution centralizer, a fixed derived layer
of order at least sixteen detects the actual second local core. -/
public theorem LargeTerminalContext.involution_centralizer_fixed_layer_mem_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (t : G) (ht : t ∈ centralizer ({z} : Set G)) (ht2 : t ^ 2 = 1)
    (E : Subgroup G) (hED : E ≤ DerivedAmbient ctx.firstResidual)
    (hE : 16 ≤ Nat.card E)
    (hcomm : ⁅E, zpowers t⁆ ≤ CenterAmbient ctx.firstResidual) :
    t ∈ twoCoreIn ctx.second := by
  classical
  let C := centralizer ({z} : Set G)
  let Q := twoCoreIn ctx.second
  let D := DerivedAmbient ctx.firstResidual
  let Z := CenterAmbient ctx.firstResidual
  have hSC : (S : Subgroup G) ≤ C := by
    change (S : Subgroup G) ≤ centralizer ({z} : Set G)
    rw [← centralizer_closure, ← zpowers_eq_closure, hgen]
    exact le_centralizer_iff.mpr ((omegaOneCenter_le_centerAmbient _).trans
      (centerAmbient_le_centralizer _))
  have hCQ : C ≤ normalizer (Q : Set G) := by
    change C ≤ normalizer (twoCoreIn ctx.second : Set G)
    rw [← (ctx.involution_centralizer_core_eq_at_generator hS z hgen).1]
    have h := (pCore 2 C).le_normalizer_map C.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  have hCD : C ≤ normalizer (D : Set G) :=
    ctx.involution_centralizer_normalizes_derived hS z hgen
  have hCZ : C ≤ normalizer (Z : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer (Z : Set G))
    change C ≤ centralizer (CenterAmbient ctx.firstResidual : Set G)
    rw [ctx.first_residual_center_eq_omegaOneCenter, ← hgen,
      zpowers_eq_closure, centralizer_closure]
  let tC : C := ⟨t, ht⟩
  let SC := S.subtype hSC
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 (zpowers tC) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (Subtype.ext ht2)
  obtain ⟨T, hT⟩ := (IsElementaryAbelian.isPGroup 2 (zpowers tC)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C T SC
  let e := MulAut.conj (c : G)
  have hxS : e t ∈ (S : Subgroup G) := by
    have hh : MulAut.conj c tC ∈ (SC : Subgroup C) := by
      rw [← hc]
      exact mem_map_of_mem (MulAut.conj c).toMonoidHom (hT (mem_zpowers tC))
    exact hh
  have hDmap : D.map e.toMonoidHom = D :=
    mem_normalizer_iff_map_conj_eq.mp (hCD c.property)
  have hZmap : Z.map e.toMonoidHom = Z :=
    mem_normalizer_iff_map_conj_eq.mp (hCZ c.property)
  have hED' : E.map e.toMonoidHom ≤ D := hDmap ▸ map_mono hED
  have hE' : 16 ≤ Nat.card (E.map e.toMonoidHom) := by
    rw [card_map_of_injective e.injective]
    exact hE
  have hcomm' : ⁅E.map e.toMonoidHom, zpowers (e t)⁆ ≤ Z := by
    have hh := map_mono (f := e.toMonoidHom) hcomm
    rw [map_commutator, MonoidHom.map_zpowers] at hh
    exact hZmap ▸ hh
  have hx2 : (e t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hxQ := ctx.second_fixed_layer_mem_core (e t)
    (ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1 hxS)
    hx2 (E.map e.toMonoidHom) hED' hE' hcomm'
  exact (mem_normalizer_iff.mp (hCQ c.property) t).mpr hxQ

end Stellmacher.Recognition
