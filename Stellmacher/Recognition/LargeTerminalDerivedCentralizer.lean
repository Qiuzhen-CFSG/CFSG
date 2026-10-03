module

public import Stellmacher.Recognition.LargeTerminalLocalCharacterData
public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData
public import Stellmacher.SectionTen.TenOneLargeCoreCentralizerSupplement
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The ambient derived centralizer at the large terminal endpoint

Write R for the first residual, D for its derived subgroup, and Q for the
second local core. The perfect commutator pairing proved in Section Ten
gives Q = C_Q(D) R and C_Q(D) ∩ R = D. We transport these identities from
the terminal vertex to the first vertex and then to the ambient group.
At Sylow order 4096 this gives |C_Q(D)| = 64 and [Q : C_Q(D)] = 16.

The second local group normalizes this order-64 subgroup. Its normalizer
is a solvable two-local subgroup of characteristic two.

These are the subgroup and cardinal inputs to the outer-coset census;
they do not assert which cosets contain involutions or establish fusion.
Sources: Stellmacher (10.1), the core supplement after (20); Thompson VI,
printed p.630, the fifteen outer cosets.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup

universe u

private theorem relative_centralizer_map
    {K L : Type*} [Group K] [Group L] (R V : Subgroup K) (f : K →* L)
    (hf : Function.Injective f) :
    (R ⊓ centralizer (V : Set K)).map f =
      R.map f ⊓ centralizer (V.map f : Set L) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨mem_map_of_mem f hx.1, ?_⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨v, hv, rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hx.2 v hv)
  · rintro _ ⟨⟨x, hx, rfl⟩, hc⟩
    refine mem_map_of_mem f ⟨hx, ?_⟩
    apply mem_centralizer_iff.mpr
    intro v hv
    apply hf
    simpa only [map_mul] using mem_centralizer_iff.mp hc (f v) (mem_map_of_mem f hv)

/-- The actual ambient core is supplemented by its derived centralizer,
whose intersection with the residual is exactly the derived subgroup. -/
public theorem LargeTerminalContext.derived_centralizer_supplement
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    let Q := twoCoreIn ctx.second
    let R := ctx.firstResidual
    let D := DerivedAmbient R
    let Q₀ := Q ⊓ centralizer (D : Set G)
    Q = Q₀ ⊔ R ∧ Q₀ ⊓ R = D := by
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  obtain ⟨hQ, hR⟩ :=
    ten_one_large_core_centralizer_supplement tenCtx middle hpath ctx.noTransvections
  change QAt Γ cp.a' =
    (QAt Γ cp.a' ⊓ centralizer (VAt Γ cp.a' : Set K)) ⊔
      twoCoreIn (EAt Γ cp.a') at hQ
  change (QAt Γ cp.a' ⊓ centralizer (VAt Γ cp.a' : Set K)) ⊓
    twoCoreIn (EAt Γ cp.a') = VAt Γ cp.a' at hR
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
  have hRmap : (twoCoreIn (EAt Γ cp.a')).map e.toMonoidHom =
      twoCoreIn (EAt Γ cp.firstStep) := by
    rw [← twoCoreIn_map_equiv, hEmap]
  have hVmap : (VAt Γ cp.a').map e.toMonoidHom = VAt Γ cp.firstStep := by
    change (v Γ cp.a').map _ = v Γ cp.firstStep
    rw [← v_act, hmove]
  let f : K →* G := K.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.injective
  have hRimage : (twoCoreIn (EAt Γ cp.a')).map f = ctx.firstResidual := by
    change (_ : Subgroup K).map (K.subtype.comp e.toMonoidHom) = _
    rw [← map_map, hRmap]
    rfl
  have hDimage : (VAt Γ cp.a').map f = DerivedAmbient ctx.firstResidual := by
    rw [ctx.first_residual_structure.2.2.1]
    change (_ : Subgroup K).map (K.subtype.comp e.toMonoidHom) = _
    rw [← map_map, hVmap]
  have hPimage : (GAt Γ cp.a').map f = ctx.second := by
    change (_ : Subgroup K).map (K.subtype.comp e.toMonoidHom) = _
    rw [← map_map, hPmap]
    exact (nine_two_ambient_setup tenCtx.toAmbientSectionNineContext).2.2.1
  have hQimage : (QAt Γ cp.a').map f = twoCoreIn ctx.second := by
    change (Γ.twoCoreAt cp.a').map f = _
    rw [Γ.twoCoreAt_def]
    change (twoCoreIn (GAt Γ cp.a')).map f = _
    let j := (GAt Γ cp.a').equivMapOfInjective f hf
    have hj := pCore_map_iso 2 j
    have hc : (twoCoreIn (GAt Γ cp.a')).map f =
        twoCoreIn ((GAt Γ cp.a').map f) := by
      change ((pCore 2 (GAt Γ cp.a')).map (GAt Γ cp.a').subtype).map f =
        (pCore 2 ((GAt Γ cp.a').map f)).map ((GAt Γ cp.a').map f).subtype
      rw [← hj, map_map, map_map]
      rfl
    rw [hc, hPimage]
  have hCimage := relative_centralizer_map (QAt Γ cp.a') (VAt Γ cp.a') f hf
  rw [hQimage, hDimage] at hCimage
  constructor
  · have hh := congrArg (fun U : Subgroup K => U.map f) hQ
    simpa only [Subgroup.map_sup, hQimage, hRimage, hCimage] using hh
  · have hh := congrArg (fun U : Subgroup K => U.map f) hR
    rw [map_inf _ _ f hf, hCimage, hRimage, hDimage] at hh
    exact hh

/-- At the upper endpoint the derived centralizer has order 64, so its
index in the second core is 16, as in the source's fifteen outer cosets. -/
public theorem LargeTerminalContext.derived_centralizer_card_and_index
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    let Q := twoCoreIn ctx.second
    let D := DerivedAmbient ctx.firstResidual
    let Q₀ := Q ⊓ centralizer (D : Set G)
    Nat.card Q₀ = 64 ∧ Q₀.relIndex Q = 16 := by
  let Q := twoCoreIn ctx.second
  let R := ctx.firstResidual
  let D := DerivedAmbient R
  let Q₀ := Q ⊓ centralizer (D : Set G)
  obtain ⟨hsup, hinf⟩ := ctx.derived_centralizer_supplement
  change Q = Q₀ ⊔ R at hsup
  change Q₀ ⊓ R = D at hinf
  have hRQ : R ≤ Q := hsup ▸ le_sup_right
  have hQ₀Q : Q₀ ≤ Q := inf_le_left
  have hD₀ : D ≤ Q₀ := hinf ▸ inf_le_left
  have hQS : Q ≤ (S : Subgroup G) := by
    have hSP : (S : Subgroup G) ≤ ctx.second :=
      ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S.subtype hSP) hq
  have hQcard : Nat.card Q = 1024 := by
    have hh := ctx.local_character_core_card hS
    rwa [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv] at hh
  have hRcard : Nat.card R = 512 := ctx.first_residual_structure.1
  have hDcard : Nat.card D = 32 := by
    change Nat.card ((commutator R).map R.subtype) = 32
    rw [card_map_of_injective R.subtype_injective]
    exact ctx.first_residual_structure.2.2.2.2.1
  let _ : (R.subgroupOf (S : Subgroup G)).Normal := ctx.local_character_residual_normal
  let _ : (R.subgroupOf Q).Normal :=
    (inferInstance : (R.subgroupOf (S : Subgroup G)).Normal).comap (inclusion hQS)
  have hindex : R.relIndex Q = 2 := by
    have hh := (R.subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hRQ).toEquiv, hRcard, hQcard] at hh
    change R.relIndex Q * 512 = 1024 at hh
    omega
  have hindex₀ : D.relIndex Q₀ = 2 := by
    rw [← hinf, inf_relIndex_left]
    have hh := relIndex_sup_right (Q₀.subgroupOf Q) (R.subgroupOf Q)
    rw [← subgroupOf_sup hQ₀Q hRQ, ← hsup,
      relIndex_subgroupOf le_rfl, relIndex_subgroupOf hQ₀Q] at hh
    exact hh.symm.trans hindex
  have hcard₀ : Nat.card Q₀ = 64 := by
    have hh := (D.subgroupOf Q₀).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hD₀).toEquiv, hDcard] at hh
    change D.relIndex Q₀ * 32 = Nat.card Q₀ at hh
    rw [hindex₀] at hh
    exact hh.symm
  refine ⟨hcard₀, ?_⟩
  have hh := (Q₀.subgroupOf Q).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hQ₀Q).toEquiv, hcard₀, hQcard] at hh
  change Q₀.relIndex Q * 64 = 1024 at hh
  change Q₀.relIndex Q = 16
  omega

/-- The order-64 derived centralizer is normalized by the second local
group; its ambient normalizer has the available two-local structure. -/
public theorem LargeTerminalContext.derived_centralizer_normalizer_local_data
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    let W := twoCoreIn ctx.second ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
    Nat.card W = 64 ∧ ctx.second ≤ normalizer (W : Set G) ∧
      IsTwoLocal (normalizer (W : Set G)) ∧
      Group.IsSolvable (normalizer (W : Set G)) ∧
      IsCharacteristicTwoType (normalizer (W : Set G)) := by
  let Q := twoCoreIn ctx.second
  let D := DerivedAmbient ctx.firstResidual
  let W := Q ⊓ centralizer (D : Set G)
  have hW : Nat.card W = 64 := (ctx.derived_centralizer_card_and_index hS).1
  have hMQ : ctx.second ≤ normalizer (Q : Set G) := by
    exact ctx.second.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image ctx.second (pCore 2 ctx.second))
  have hMD : ctx.second ≤ normalizer (D : Set G) :=
    ctx.second_le_residual_normalizer.trans
      (normalizer_le_normalizer_characteristic_image ctx.firstResidual
        (commutator ctx.firstResidual))
  have hMW : ctx.second ≤ normalizer (W : Set G) :=
    (le_inf hMQ (hMD.trans (normalizer_le_normalizer_centralizer D))).trans
      inf_normalizer_le_normalizer_inf
  have htwo : IsPGroup 2 W :=
    ((pCore_isPGroup (p := 2) (G := ctx.second)).map ctx.second.subtype).to_le
      (show W ≤ Q from inf_le_left)
  have hne : W ≠ ⊥ := by
    intro h
    simp [h] at hW
  have hlocal : IsTwoLocal (normalizer (W : Set G)) := ⟨W, hne, htwo, rfl⟩
  exact ⟨hW, hMW, hlocal, ctx.localStructure _ hlocal⟩

end Stellmacher.Recognition
