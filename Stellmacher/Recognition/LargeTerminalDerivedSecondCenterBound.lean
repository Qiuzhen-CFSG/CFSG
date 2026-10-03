module

public import Stellmacher.Recognition.LargeTerminalDerivedCentralizer
public import Stellmacher.Recognition.LargeTerminalFourFixedCoreFrattini
public import Theory.GroupAction.FiveFourSylowFixedLayer

/-!
# The derived residual meets the second center in at most four elements

For the original large terminal context, write R for the first residual,
D for its derived subgroup, Z for its center, and Q for the second local
core. Characteristic-two type puts the Sylow center inside Q; the identity
C_Q(R) = Z then puts that center inside Z. Thus D ∩ Z₂(S) is fixed modulo
Z by the prescribed Sylow subgroup.

The literal conjugation action on D/Z factors faithfully through the
five-four quotient. Its Sylow image contains an element of order four,
which fixes two of the sixteen quotient points. Since |Z| = 2, the fixed
layer has order at most four. No Sylow-order assumption or group model
is required.

Sources: Stellmacher (5.3), (9.3), (10.1)(18)--(20); the derived-quotient
fixed-point argument in Thompson VI, printed p.630.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
open scoped commutatorElement
universe u

/-- The center of the prescribed Sylow lies in the center of the actual
first residual, using characteristic-two type and its core centralizer. -/
public theorem LargeTerminalContext.sylow_center_le_residual_center
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    CenterAmbient (S : Subgroup G) ≤ CenterAmbient ctx.firstResidual := by
  let Q := twoCoreIn ctx.second
  have hSP : (S : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  have hQS : Q ≤ (S : Subgroup G) := by
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S.subtype hSP) hq
  have hRQ : ctx.firstResidual ≤ Q := by
    change ctx.firstResidual ≤ twoCoreIn ctx.second
    rw [ctx.derived_centralizer_supplement.1]
    exact le_sup_right
  have hchar : IsCharacteristicTwoType ctx.second :=
    (lemma_five_three S (S : Subgroup G) ctx.first ctx.second
      ctx.terminal.hypothesisTwo).2.2.2
  have hZS : CenterAmbient (S : Subgroup G) ≤ (S : Subgroup G) := map_subtype_le _
  have hZC : CenterAmbient (S : Subgroup G) ≤ centralizer (S : Set G) :=
    centerAmbient_le_centralizer _
  rw [← ctx.core_inf_residual_centralizer]
  apply le_inf ?_ (hZC.trans (centralizer_le (hRQ.trans hQS)))
  intro x hx
  have hxP : x ∈ ctx.second := hSP (hZS hx)
  refine ⟨⟨x, hxP⟩, ?_, rfl⟩
  apply hchar
  apply mem_centralizer_iff.mpr
  intro q hq
  apply Subtype.ext
  exact mem_centralizer_iff.mp (hZC hx) q
    (hQS (mem_map_of_mem ctx.second.subtype hq))

private theorem first_sylow_fixed_layer_card_le_four
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S)
    (E : Subgroup (ctx.first ⊔ ctx.second : Subgroup G))
    (hEV : E ≤ VAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep)
    (hcomm : ⁅E, (S : Subgroup G).subgroupOf (ctx.first ⊔ ctx.second)⁆ ≤
      ZAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep) :
    Nat.card E ≤ 4 := by
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
  obtain ⟨_, T, hT⟩ := (SevenSix.edge_sylow_data tenCtx.sectionSeven Γ cp).2
  let q := QuotientGroup.mk' (Z.subgroupOf V)
  have hq : Nat.card q.ker ≤ 2 := by
    rw [QuotientGroup.ker_mk', Nat.card_congr (subgroupOfEquivOfLe hZV).toEquiv, hZcard]
  have hbound := Theory.GroupAction.five_four_sylow_fixed_layer_card_le_four
    hWcard φ hφ π hπ action hk T q hq (E.subgroupOf V) (by
      intro t ht e
      rw [hformula]
      apply QuotientGroup.eq_iff_div_mem.mpr
      change (t : K) * ((e : V) : K) * (t : K)⁻¹ / ((e : V) : K) ∈ Z
      have htS : (t : K) ∈ (S : Subgroup G).subgroupOf K := by
        exact hT.le (mem_map_of_mem P.subtype ht)
      have hc : ⁅(t : K), ((e : V) : K)⁆ ∈ Z := by
        rw [commutator_comm] at hcomm
        exact hcomm (commutator_mem_commutator htS e.property)
      simpa only [commutatorElement_def, div_eq_mul_inv] using hc)
  have hEV' : E ≤ V := hEV
  rwa [Nat.card_congr (subgroupOfEquivOfLe hEV').toEquiv] at hbound

private theorem derived_sylow_fixed_layer_card_le_four
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (E : Subgroup G)
    (hED : E ≤ DerivedAmbient ctx.firstResidual)
    (hcomm : ⁅E, (S : Subgroup G)⁆ ≤ CenterAmbient ctx.firstResidual) :
    Nat.card E ≤ 4 := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  have hD : DerivedAmbient ctx.firstResidual = V.map K.subtype :=
    ctx.first_residual_structure.2.2.1
  have hZ : CenterAmbient ctx.firstResidual = Z.map K.subtype :=
    ctx.first_residual_structure.2.1
  have hEK : E ≤ K := hED.trans (hD ▸ map_subtype_le V)
  let E₀ := E.subgroupOf K
  have hE₀V : E₀ ≤ V := by
    intro e he
    apply (mem_map_iff_mem K.subtype_injective).mp
    exact hD ▸ hED he
  have hcomm₀ : ⁅E₀, (S : Subgroup G).subgroupOf K⁆ ≤ Z := by
    apply (map_le_map_iff_of_injective (f := K.subtype) K.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le ctx.terminal.sylow_le_join,
      map_subgroupOf_eq_of_le hEK, ← hZ]
    exact hcomm
  have hbound := first_sylow_fixed_layer_card_le_four ctx E₀ hE₀V hcomm₀
  rwa [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv] at hbound

/-- The derived first residual intersects the second center of the original
Sylow in at most four elements. -/
public theorem LargeTerminalContext.derived_inf_second_center_card_le_four
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    Nat.card ((DerivedAmbient ctx.firstResidual).subgroupOf (S : Subgroup G) ⊓
      Subgroup.upperCentralSeries S 2 : Subgroup S) ≤ 4 := by
  let E := (DerivedAmbient ctx.firstResidual).subgroupOf (S : Subgroup G) ⊓
    Subgroup.upperCentralSeries S 2
  have hED : E.map (S : Subgroup G).subtype ≤ DerivedAmbient ctx.firstResidual := by
    rintro x ⟨e, he, rfl⟩
    exact he.1
  have hcomm : ⁅E.map (S : Subgroup G).subtype, (S : Subgroup G)⁆ ≤
      CenterAmbient ctx.firstResidual := by
    have hlocal : ⁅E, ⊤⁆ ≤ center S := by
      rw [← Subgroup.upperCentralSeries_one]
      exact (commutator_mono (show E ≤ Subgroup.upperCentralSeries S 2 from inf_le_right)
        le_rfl).trans (Subgroup.commutator_upperCentralSeries_top_le S 1)
    have hmap := map_mono (f := (S : Subgroup G).subtype) hlocal
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hmap
    exact hmap.trans ctx.sylow_center_le_residual_center
  have hbound := derived_sylow_fixed_layer_card_le_four ctx _ hED hcomm
  rwa [card_map_of_injective (S : Subgroup G).subtype_injective] at hbound

end Stellmacher.Recognition
