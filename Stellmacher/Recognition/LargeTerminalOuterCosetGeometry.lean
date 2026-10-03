module

public import Stellmacher.Recognition.LargeTerminalDerivedCentralizer
public import Theory.GroupTheory.CentralCommutatorFixedIndex

/-!
# The conjugate module meeting the outer cosets

The terminal module D* is an actual conjugate of the derived first residual D.
It is elementary of order 32, meets D in order 8, and meets the first residual
R in order 16. Thus D* contains an involution in R outside C_Q(D), since
C_Q(D) ∩ R = D. These are the native subgroup inputs for choosing F₁ in the
outer-coset argument. The coset Df has sixteen involutions, eight in the
terminal module and eight outside it. No census of all outer cosets or
ambient fusion is assumed.

The middle vertex action interchanges the first and terminal neighbors. We
transport the source-(15) residual intersection across that interchange and
then through the inclusion of the generated join in the ambient group.
Sources: Stellmacher (10.1)(14)--(15); Thompson VI, printed p.630, the choice
of F₁ in the intersection of the conjugate module with the core.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup

universe u

/-- The terminal module, in the original ambient group. -/
@[expose] public def LargeTerminalContext.terminalModule
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) : Subgroup G :=
  (VAt ctx.terminal.Γ ctx.terminal.criticalPath.a').map
    (ctx.first ⊔ ctx.second).subtype

/-- The two neighboring modules are conjugate; their common subgroup has
order eight and the terminal module meets the first residual in order sixteen. -/
public theorem LargeTerminalContext.terminal_module_outer_geometry
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    let D := DerivedAmbient ctx.firstResidual
    let E := ctx.terminalModule
    IsElementaryAbelian 2 E ∧ Nat.card E = 32 ∧
      Nat.card (D ⊓ E : Subgroup G) = 8 ∧
      Nat.card (E ⊓ ctx.firstResidual : Subgroup G) = 16 ∧
      ∃ g : G, E.map (MulAut.conj g).toMonoidHom = D := by
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle := ⟨⟨2, by omega⟩, rfl, rfl⟩
  let V := VAt Γ cp.a'
  let W := VAt Γ cp.firstStep
  let U := twoCoreIn (EAt Γ cp.a')
  obtain ⟨_, hVcard, hIcard⟩ :=
    ten_one_large_terminal_structure tenCtx middle hpath ctx.noTransvections
  obtain ⟨hindex, _⟩ :=
    ten_one_large_first_residual_index tenCtx middle hpath ctx.noTransvections
  obtain ⟨_, hfirst, hterminal, hne⟩ := sectionTenOpeningGeometry tenCtx middle hpath
  obtain ⟨mover, _, hswapW, hswapV⟩ :=
    ten_one_neighbor_pair_alignment tenCtx middle hpath hterminal hfirst hne.symm
  change Γ.act mover cp.firstStep = cp.a' at hswapW
  change Γ.act mover cp.a' = cp.firstStep at hswapV
  let e := MulAut.conj mover⁻¹
  have hWmap : W.map e.toMonoidHom = V := by
    change (v Γ cp.firstStep).map _ = v Γ cp.a'
    rw [← v_act, hswapW]
  have hVmap : V.map e.toMonoidHom = W := by
    change (v Γ cp.a').map _ = v Γ cp.firstStep
    rw [← v_act, hswapV]
  have hPmap : (GAt Γ cp.a').map e.toMonoidHom = GAt Γ cp.firstStep := by
    change conjugateBy (stabilizer Γ cp.a') mover⁻¹ = stabilizer Γ cp.firstStep
    rw [← stabilizer_act, hswapV]
  have hEmap : (EAt Γ cp.a').map e.toMonoidHom = EAt Γ cp.firstStep := by
    change (Γ.twoResidualAt cp.a').map _ = Γ.twoResidualAt cp.firstStep
    rw [Γ.twoResidualAt_def, Γ.twoResidualAt_def, ← twoResidualIn_map_equiv]
    exact congrArg twoResidualIn hPmap
  have hUmap : U.map e.toMonoidHom = twoCoreIn (EAt Γ cp.firstStep) := by
    rw [← twoCoreIn_map_equiv, hEmap]
  let f : K →* G := K.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.injective
  have hWimage : W.map f = ctx.terminalModule := by
    change W.map (K.subtype.comp e.toMonoidHom) = _
    rw [← map_map, hWmap]
    rfl
  have hUimage : U.map f = ctx.firstResidual := by
    change U.map (K.subtype.comp e.toMonoidHom) = _
    rw [← map_map, hUmap]
    rfl
  have hDimage : W.map K.subtype = DerivedAmbient ctx.firstResidual :=
    ctx.first_residual_structure.2.2.1.symm
  have hWcard : Nat.card W = 32 := by
    rw [← hVmap, card_map_of_injective e.injective]
    exact hVcard
  have hWUcard : Nat.card (W ⊓ U : Subgroup K) = 16 := by
    change Nat.card W = 2 * Nat.card (W ⊓ U : Subgroup K) at hindex
    rw [hWcard] at hindex
    omega
  have hshort : 1 < cp.length := by omega
  let _ : IsElementaryAbelian 2 V :=
    (nine_three_second_extraction_inputs tenCtx.toLocalContext.toSectionNineLocalContext
      hshort).2.2.1
  refine ⟨IsElementaryAbelian.map K.subtype, ?_, ?_, ?_, ?_⟩
  · change Nat.card (V.map K.subtype) = 32
    rw [card_map_of_injective K.subtype_injective]
    exact hVcard
  · rw [← hDimage]
    change Nat.card (W.map K.subtype ⊓ V.map K.subtype : Subgroup G) = 8
    rw [← map_inf _ _ _ K.subtype_injective, card_map_of_injective K.subtype_injective]
    exact hIcard
  · rw [← hWimage, ← hUimage, ← map_inf _ _ _ hf, card_map_of_injective hf]
    exact hWUcard
  · refine ⟨(mover : G)⁻¹, ?_⟩
    rw [← hDimage, ← hVmap]
    change (V.map K.subtype).map _ = (V.map e.toMonoidHom).map K.subtype
    rw [map_map, map_map]
    rfl

/-- Every element of the terminal module is conjugate into the derived residual. -/
public theorem LargeTerminalContext.terminal_module_isConj_derived
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (x : G) (hx : x ∈ ctx.terminalModule) :
    ∃ t : G, t ∈ DerivedAmbient ctx.firstResidual ∧ IsConj x t := by
  obtain ⟨_, _, _, _, g, hg⟩ := ctx.terminal_module_outer_geometry
  refine ⟨MulAut.conj g x, ?_, isConj_iff.mpr ⟨g, rfl⟩⟩
  rw [← hg]
  exact mem_map_of_mem _ hx

/-- The derived residual is an elementary abelian subgroup. -/
public theorem LargeTerminalContext.derived_residual_elementary
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    IsElementaryAbelian 2 (DerivedAmbient ctx.firstResidual) := by
  obtain ⟨helem, _, _, _, g, hg⟩ := ctx.terminal_module_outer_geometry
  let _ := helem
  rw [← hg]
  exact IsElementaryAbelian.map _

/-- A residual element acting nontrivially on D fixes exactly sixteen elements
of D. This is the centralizer that parametrizes the involutions of Df. -/
public theorem LargeTerminalContext.derived_fixed_card_of_residual_not_centralizing
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (f : G) (hf : f ∈ ctx.firstResidual)
    (hfc : f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G)) :
    Nat.card (DerivedAmbient ctx.firstResidual ⊓ centralizer ({f} : Set G) :
      Subgroup G) = 16 := by
  let R := ctx.firstResidual
  let fR : R := ⟨f, hf⟩
  have hR : IsPGroup 2 R := IsPGroup.of_card (n := 9) ctx.first_residual_structure.1
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Group.IsNilpotent R := hR.isNilpotent
  have hclass : (⊤ : Subgroup R).lowerCentralSeries 3 = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr
      ctx.first_residual_structure.2.2.2.2.2.le
  have hcomm : ⁅commutator R, (⊤ : Subgroup R)⁆ ≤ center R :=
    commutator_top_right_eq_bot_iff_le_center.mp hclass
  have hnon : fR ∉ centralizer (commutator R : Set R) := by
    intro hh
    apply hfc
    apply mem_centralizer_iff.mpr
    rintro _ ⟨d, hd, rfl⟩
    exact congrArg (fun r : R => (r : G)) (mem_centralizer_iff.mp hh d hd)
  have hindex := centralizer_relIndex_eq_two_of_commutator_le_center
    (commutator R) hcomm ctx.first_residual_structure.2.2.2.1 fR hnon
  let C := commutator R ⊓ centralizer ({fR} : Set R)
  have hcard : Nat.card C = 16 := by
    have hc := (C.subgroupOf (commutator R)).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show C ≤ commutator R from inf_le_left)).toEquiv] at hc
    change C.relIndex (commutator R) * Nat.card C = Nat.card (commutator R) at hc
    have hi : C.relIndex (commutator R) = 2 := by
      change (commutator R ⊓ centralizer ({fR} : Set R)).relIndex (commutator R) = 2
      rw [inf_relIndex_left]
      exact hindex
    rw [hi, ctx.first_residual_structure.2.2.2.2.1] at hc
    omega
  have hmap : C.map R.subtype =
      DerivedAmbient R ⊓ centralizer ({f} : Set G) := by
    ext d
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨mem_map_of_mem _ hr.1, mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg (fun r : R => (r : G))
        (mem_centralizer_singleton_iff.mp hr.2)
    · rintro ⟨⟨r, hr, rfl⟩, hc⟩
      refine mem_map_of_mem R.subtype ⟨hr, mem_centralizer_singleton_iff.mpr ?_⟩
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hc)
  rw [← hmap, card_map_of_injective R.subtype_injective]
  exact hcard

/-- In Df, precisely the coefficients fixed by f give involutions. -/
public theorem LargeTerminalContext.derived_coset_involution_iff
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (f : G) (hf : orderOf f = 2)
    (hfD : f ∉ DerivedAmbient ctx.firstResidual)
    (d : G) (hd : d ∈ DerivedAmbient ctx.firstResidual) :
    orderOf (d * f) = 2 ↔ d ∈ centralizer ({f} : Set G) := by
  let D := DerivedAmbient ctx.firstResidual
  let _ : IsElementaryAbelian 2 D := ctx.derived_residual_elementary
  have hd2 : d ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := D) d hd
  have hf2 : f ^ 2 = 1 := hf ▸ pow_orderOf_eq_one f
  have hdInv : d⁻¹ = d := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hd2)
  have hfInv : f⁻¹ = f := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hf2)
  constructor
  · intro h
    have hprod : (d * f) * (d * f) = 1 := by
      have hp : (d * f) ^ 2 = 1 := by
        rw [← h]
        exact pow_orderOf_eq_one (d * f)
      simpa only [pow_two] using hp
    have hi := inv_eq_of_mul_eq_one_right hprod
    rw [mul_inv_rev, hdInv, hfInv] at hi
    exact mem_centralizer_singleton_iff.mpr hi.symm
  · intro hc
    have hcomm : Commute d f := mem_centralizer_singleton_iff.mp hc
    have hp : (d * f) ^ 2 = 1 := by rw [hcomm.mul_pow, hd2, hf2, one_mul]
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime hp
    intro he
    exact hfD ((inv_eq_of_mul_eq_one_right he) ▸ D.inv_mem hd)

/-- The distinguished residual coset has sixteen involutions. The remaining
outer-coset census must still exclude the other ten cosets of C_Q(D). -/
public theorem LargeTerminalContext.derived_coset_involution_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (f : G) (hfR : f ∈ ctx.firstResidual)
    (hfc : f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (hf : orderOf f = 2) :
    {x : G | x * f⁻¹ ∈ DerivedAmbient ctx.firstResidual ∧ orderOf x = 2}.ncard = 16 := by
  let D := DerivedAmbient ctx.firstResidual
  let _ : IsElementaryAbelian 2 D := ctx.derived_residual_elementary
  have hfD : f ∉ D := fun h => hfc (le_centralizer D h)
  have heq : {x : G | x * f⁻¹ ∈ D ∧ orderOf x = 2} =
      (fun d : G => d * f) '' ((D ⊓ centralizer ({f} : Set G) : Subgroup G) : Set G) := by
    ext x
    constructor
    · rintro ⟨hd, hx⟩
      refine ⟨x * f⁻¹, ⟨hd, ?_⟩, by simp⟩
      apply (ctx.derived_coset_involution_iff f hf hfD _ hd).mp
      simpa only [inv_mul_cancel_right] using hx
    · rintro ⟨d, hd, rfl⟩
      exact ⟨by rw [mul_inv_cancel_right]; exact hd.1,
        (ctx.derived_coset_involution_iff f hf hfD d hd.1).mpr hd.2⟩
  rw [heq, Set.ncard_image_of_injective _ (fun a b h => mul_right_cancel h), ← Nat.card_coe_set_eq]
  exact ctx.derived_fixed_card_of_residual_not_centralizing f hfR hfc

/-- The actual terminal module supplies the source's outer involution F₁. -/
public theorem LargeTerminalContext.exists_terminal_module_outer_involution
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ∃ f : G, f ∈ ctx.terminalModule ∧ f ∈ ctx.firstResidual ∧
      f ∈ twoCoreIn ctx.second ∧
      f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) ∧ orderOf f = 2 := by
  let D := DerivedAmbient ctx.firstResidual
  let E := ctx.terminalModule
  let R := ctx.firstResidual
  let Q := twoCoreIn ctx.second
  obtain ⟨helem, _, hDE, hER, _⟩ := ctx.terminal_module_outer_geometry
  obtain ⟨hsup, hinf⟩ := ctx.derived_centralizer_supplement
  change Q = (Q ⊓ centralizer (D : Set G)) ⊔ R at hsup
  change (Q ⊓ centralizer (D : Set G)) ⊓ R = D at hinf
  have hRQ : R ≤ Q := hsup ▸ le_sup_right
  have hnot : ¬ E ⊓ R ≤ D := by
    intro h
    have hc := card_le_of_le (le_inf h (show E ⊓ R ≤ E from inf_le_left))
    rw [hER, hDE] at hc
    omega
  obtain ⟨f, hf, hfD⟩ : ∃ f : G, f ∈ E ⊓ R ∧ f ∉ D := by
    simpa only [SetLike.le_def, not_forall, exists_prop] using hnot
  have hfQ := hRQ hf.2
  have hfC : f ∉ centralizer (D : Set G) := by
    intro hc
    exact hfD (hinf ▸ (show f ∈ (Q ⊓ centralizer (D : Set G)) ⊓ R from
      ⟨⟨hfQ, hc⟩, hf.2⟩))
  let _ : IsElementaryAbelian 2 E := helem
  have hf2 : f ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := E) f hf.1
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨f, hf.1, hf.2, hfQ, hfC,
    orderOf_eq_prime hf2 (fun h => hfD (h ▸ D.one_mem))⟩

/-- The sixteen involutions of the distinguished derived coset split into
eight in the terminal module and eight outside it. -/
public theorem LargeTerminalContext.derived_coset_terminal_partition
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (f : G) (hfE : f ∈ ctx.terminalModule)
    (hfR : f ∈ ctx.firstResidual)
    (hfc : f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (hf : orderOf f = 2) :
    let T := {x : G | x * f⁻¹ ∈ DerivedAmbient ctx.firstResidual ∧ orderOf x = 2}
    (T ∩ (ctx.terminalModule : Set G)).ncard = 8 ∧
      (T \ (ctx.terminalModule : Set G)).ncard = 8 := by
  let D := DerivedAmbient ctx.firstResidual
  let E := ctx.terminalModule
  let T := {x : G | x * f⁻¹ ∈ D ∧ orderOf x = 2}
  change (T ∩ (E : Set G)).ncard = 8 ∧ (T \ (E : Set G)).ncard = 8
  let _ : IsElementaryAbelian 2 D := ctx.derived_residual_elementary
  let _ : IsElementaryAbelian 2 E := ctx.terminal_module_outer_geometry.1
  have hfD : f ∉ D := fun h => hfc (le_centralizer D h)
  have hset : T ∩ (E : Set G) = (fun d : G => d * f) '' ((D ⊓ E : Subgroup G) : Set G) := by
    ext x
    constructor
    · rintro ⟨⟨hd, _⟩, hxE⟩
      exact ⟨x * f⁻¹, ⟨hd, E.mul_mem hxE (E.inv_mem hfE)⟩, by simp⟩
    · rintro ⟨d, hd, rfl⟩
      refine ⟨⟨by rw [mul_inv_cancel_right]; exact hd.1, ?_⟩,
        E.mul_mem hd.2 hfE⟩
      apply (ctx.derived_coset_involution_iff f hf hfD d hd.1).mpr
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (le_centralizer E hfE) d hd.2)
  have hblock : (T ∩ (E : Set G)).ncard = 8 := by
    rw [hset, Set.ncard_image_of_injective _ (fun a b h => mul_right_cancel h), ← Nat.card_coe_set_eq]
    exact ctx.terminal_module_outer_geometry.2.2.1
  refine ⟨hblock, ?_⟩
  have htotal := Set.ncard_inter_add_ncard_sdiff_eq_ncard T (E : Set G)
  rw [hblock, ctx.derived_coset_involution_card f hfR hfc hf] at htotal
  omega


end Stellmacher.Recognition
