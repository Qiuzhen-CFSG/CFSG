module

public import Stellmacher.Recognition.LargeTerminalContext

/-!
# The actual first residual in the large terminal configuration

For the retained large terminal context, the two-core of the first vertex's
residual, included in the original ambient group, has order 512 and
nilpotency class three. Its center and derived subgroup are exactly the
included first center and first module, with orders two and thirty-two.
The exposed `firstResidual` accessor keeps this literal subgroup available
to the later involution-centralizer and order-five action arguments.

The existing large Section Ten results give the terminal module order 32,
residual quotient order 16, residual derived subgroup equal to that module,
and centralizer of the residual inside the full vertex core equal to the
center line. Hence the residual center is that line. The relation
[V,Q]=Z makes the third lower central term trivial; class at most two would
put the order-32 derived group in the order-two center. The middle vertex
stabilizer conjugates terminal to first, and the generated-join inclusion
transports all these exact subgroup identities into the original group.

No equality between the residual and the full vertex core, or between a
vertex and a full ambient involution centralizer, is used. This is a core
structure input for the subsequent Parrott bridge. Source: consequences of
Stellmacher (10.1)(18)--(20), printed pp.64--65 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
universe u

private theorem center_ambient_map
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (R : Subgroup G) :
    CenterAmbient (R.map f) = (CenterAmbient R).map f := by
  let e := R.equivMapOfInjective f hf
  have hc : (center R).map e.toMonoidHom = center (R.map f) := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (centerCongr e ⟨a, ha⟩).property
    · intro hb
      exact ⟨e.symm b, (centerCongr e.symm ⟨b, hb⟩).property, e.apply_symm_apply b⟩
  change (center (R.map f)).map (R.map f).subtype = ((center R).map R.subtype).map f
  rw [← hc, map_map, map_map]
  rfl

private theorem class_three_of_layers
    {G : Type*} [Group G] [Finite G] (R V Z : Subgroup G)
    (hR : IsPGroup 2 R) (hVcard : Nat.card V = 32) (hZcard : Nat.card Z = 2)
    (hcenter : CenterAmbient R = Z) (hderived : DerivedAmbient R = V)
    (hcomm : ⁅V, R⁆ ≤ Z) :
    Nat.card (center R) = 2 ∧ Nat.card (commutator R) = 32 ∧
      Group.nilpotencyClass R = 3 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Group.IsNilpotent R := hR.isNilpotent
  have hZ : Nat.card (center R) = 2 := by
    rw [← hZcard, ← hcenter]
    exact (card_map_of_injective R.subtype_injective).symm
  have hD : Nat.card (commutator R) = 32 := by
    rw [← hVcard, ← hderived]
    exact (card_map_of_injective R.subtype_injective).symm
  have hLcenter : ⁅commutator R, (⊤ : Subgroup R)⁆ ≤ center R := by
    apply (map_le_map_iff_of_injective (f := R.subtype) R.subtype_injective).mp
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    change ⁅DerivedAmbient R, R⁆ ≤ CenterAmbient R
    rw [hderived, hcenter]
    exact hcomm
  have hL3 : (⊤ : Subgroup R).lowerCentralSeries 3 = ⊥ := by
    change ⁅⁅commutator R, (⊤ : Subgroup R)⁆, (⊤ : Subgroup R)⁆ = ⊥
    exact commutator_top_right_eq_bot_iff_le_center.mpr hLcenter
  have hle := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hL3
  have hnle : ¬ Group.nilpotencyClass R ≤ 2 := by
    intro htwo
    have hL2 := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr htwo
    have hDC : commutator R ≤ center R :=
      commutator_top_right_eq_bot_iff_le_center.mp hL2
    have hc := card_le_of_le hDC
    rw [hD, hZ] at hc
    omega
  exact ⟨hZ, hD, by omega⟩

private theorem terminal_layers
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    let R := twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
    let V := VAt ctx.Γ ctx.criticalPath.a'
    let Z := ZAt ctx.Γ ctx.criticalPath.a'
    Nat.card R = 512 ∧ Nat.card V = 32 ∧ Nat.card Z = 2 ∧
      CenterAmbient R = Z ∧ DerivedAmbient R = V ∧ ⁅V, R⁆ ≤ Z := by
  let R := twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  have hRQ : R ≤ Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt _) ≤ ctx.Γ.twoCoreAt _
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hVcard : Nat.card V = 32 := (ten_one_large_terminal_structure ctx middle hpath hno).2.1
  have hRcard : Nat.card R = 512 := by
    have h : Nat.card R = 16 * Nat.card V := ten_one_large_residual_quotient_card ctx middle hpath hno
    rw [hVcard] at h
    exact h
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment, _, halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hcenter := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.a' ⟨alignment, halign⟩
  have hfixed : Q ⊓ centralizer (R : Set G) = Z :=
    ten_one_large_residual_core_centralizer ctx middle hpath hno
      (ten_one_large_first_residual_five ctx middle hpath hno)
  have hZR : Z ≤ R :=
    (ten_one_large_terminal_core_fixed_line ctx middle hpath hno).ge.trans inf_le_left |>.trans
      (ten_one_large_terminal_core_commutator_escape ctx middle hpath hno).1
  have hRC : CenterAmbient R = Z := by
    apply le_antisymm
    · exact (le_inf ((map_subtype_le _).trans hRQ) (centerAmbient_le_centralizer R)).trans_eq hfixed
    · intro z hz
      refine mem_map.mpr ⟨⟨z, hZR hz⟩, ?_, rfl⟩
      rw [mem_center_iff]
      intro r
      apply Subtype.ext
      exact mem_centralizer_iff.mp (hfixed.ge hz).2 r r.property
  exact ⟨hRcard, hVcard, hcenter.1, hRC,
    ten_one_large_terminal_residual_derived_eq ctx middle hpath hno,
    (commutator_mono le_rfl hRQ).trans hcenter.2.1.le⟩

/-- The literal first residual two-core, included in the original ambient group. -/
@[expose] public def LargeTerminalContext.firstResidual
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) : Subgroup G :=
  (twoCoreIn (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep)).map
    (ctx.first ⊔ ctx.second).subtype

/-- The first residual has the exact order, central layers, and class required
by the subsequent involution-centralizer analysis. -/
public theorem LargeTerminalContext.first_residual_structure
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) :
    let V := (VAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
      (ctx.first ⊔ ctx.second).subtype
    let Z := (ZAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
      (ctx.first ⊔ ctx.second).subtype
    Nat.card ctx.firstResidual = 512 ∧
      CenterAmbient ctx.firstResidual = Z ∧ DerivedAmbient ctx.firstResidual = V ∧
      Nat.card (center ctx.firstResidual) = 2 ∧
      Nat.card (commutator ctx.firstResidual) = 32 ∧
      Group.nilpotencyClass ctx.firstResidual = 3 := by
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  let R := twoCoreIn (EAt Γ cp.a')
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  obtain ⟨hRcard, hVcard, hZcard, hcenter, hderived, hcomm⟩ :=
    terminal_layers tenCtx middle hpath ctx.noTransvections
  change Nat.card R = 512 at hRcard
  change Nat.card V = 32 at hVcard
  change Nat.card Z = 2 at hZcard
  change CenterAmbient R = Z at hcenter
  change DerivedAmbient R = V at hderived
  change ⁅V, R⁆ ≤ Z at hcomm
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry tenCtx middle hpath
  obtain ⟨mover, hmove⟩ := (lemma_seven_one tenCtx.sectionSeven Γ).local_transitivity middle
    ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
  change Γ.act (mover : K) cp.a' = cp.firstStep at hmove
  let e := MulAut.conj (mover : K)⁻¹
  have hPmap : (GAt Γ cp.a').map e.toMonoidHom = GAt Γ cp.firstStep := by
    change conjugateBy (stabilizer Γ cp.a') (mover : K)⁻¹ = stabilizer Γ cp.firstStep
    rw [← stabilizer_act, hmove]
  have hEmap : (EAt Γ cp.a').map e.toMonoidHom = EAt Γ cp.firstStep := by
    change (Γ.twoResidualAt cp.a').map _ = Γ.twoResidualAt cp.firstStep
    rw [Γ.twoResidualAt_def, Γ.twoResidualAt_def, ← twoResidualIn_map_equiv]
    exact congrArg twoResidualIn hPmap
  have hRmap : R.map e.toMonoidHom = twoCoreIn (EAt Γ cp.firstStep) := by
    change (twoCoreIn (EAt Γ cp.a')).map _ = _
    rw [← twoCoreIn_map_equiv, hEmap]
  have hVmap : V.map e.toMonoidHom = VAt Γ cp.firstStep := by
    change (v Γ cp.a').map _ = v Γ cp.firstStep
    rw [← v_act, hmove]
  have hZmap : Z.map e.toMonoidHom = ZAt Γ cp.firstStep := by
    change (z Γ cp.a').map _ = z Γ cp.firstStep
    rw [← z_act, hmove]
  let f : K →* G := K.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.injective
  have hRimage : R.map f = ctx.firstResidual := by
    change R.map (K.subtype.comp e.toMonoidHom) = _
    rw [← map_map, hRmap]
    rfl
  have hVimage : V.map f = (VAt Γ cp.firstStep).map K.subtype := by
    change V.map (K.subtype.comp e.toMonoidHom) = _
    rw [← map_map, hVmap]
  have hZimage : Z.map f = (ZAt Γ cp.firstStep).map K.subtype := by
    change Z.map (K.subtype.comp e.toMonoidHom) = _
    rw [← map_map, hZmap]
  have hC : CenterAmbient (R.map f) = Z.map f := by
    rw [center_ambient_map f hf, hcenter]
  have hD : DerivedAmbient (R.map f) = V.map f := by
    rw [show DerivedAmbient (R.map f) = ⁅R.map f, R.map f⁆ from map_subtype_commutator _,
      ← map_commutator]
    rw [← map_subtype_commutator R]
    exact congrArg (fun U => U.map f) hderived
  have hRtwo : IsPGroup 2 (R.map f) :=
    ((pCore_isPGroup (p := 2) (G := EAt Γ cp.a')).map (EAt Γ cp.a').subtype).map f
  have hnumeric := class_three_of_layers (R.map f) (V.map f) (Z.map f) hRtwo
    ((card_map_of_injective hf).trans hVcard)
    ((card_map_of_injective hf).trans hZcard) hC hD
    (by rw [← map_commutator]; exact map_mono hcomm)
  rw [hRimage, hZimage] at hC
  rw [hRimage, hVimage] at hD
  rw [hRimage] at hnumeric
  refine ⟨?_, hC, hD, hnumeric⟩
  rw [← hRimage]
  exact (card_map_of_injective hf).trans hRcard

end Stellmacher.Recognition
