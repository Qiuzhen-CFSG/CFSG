module

public import Stellmacher.Recognition.LargeTerminalOuterCosetGeometry
public import Stellmacher.Recognition.LargeTerminalFixedLayerKernel

/-!
# Moving the terminal block of a derived coset

Write Q for the second core, R for the first residual, D for its derived
subgroup, and E for the terminal module. The core normalizes I = D ∩ E
and preserves every coset of D in Q. The first residual escapes the middle
core, so its action on the cubic neighborhood interchanges the two neighbors
other than the first. A resulting conjugate of E meets E exactly in I.
This moves every element of E outside D out of E; on the distinguished
coset Df, conjugation still stays inside that coset.

This gives the block mover directly from terminal graph geometry, without
outer-coset selection or fusion assumptions. No assumption on the Sylow
order or on a five-fixed subgroup is needed. Source: Thompson, *Nonsolvable
finite groups VI*, printed p.630, the paragraph choosing H outside C_H(Z*);
Stellmacher (7.6)(b) and (10.1), the common neighbor-module intersection.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
open scoped commutatorElement

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

/-- The whole second core normalizes the common elementary eight. -/
public theorem LargeTerminalContext.second_core_normalizes_terminal_intersection
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    twoCoreIn ctx.second ≤ normalizer
      (DerivedAmbient ctx.firstResidual ⊓ ctx.terminalModule : Set G) := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle := ⟨⟨2, by omega⟩, rfl, rfl⟩
  obtain ⟨_, hfirst, _, _⟩ := sectionTenOpeningGeometry tenCtx middle hpath
  have hQM : QAt Γ cp.firstStep ≤ GAt Γ middle :=
    ((lemma_seven_three tenCtx.sectionSeven Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hfirst)) default).2.2
  have hQI := hQM.trans (ten_one_common_intersection_normalized tenCtx middle hpath)
  have hmap := (map_mono (f := K.subtype) hQI).trans (le_normalizer_map K.subtype)
  rw [map_inf _ _ _ K.subtype_injective, first_core_image ctx] at hmap
  rw [ctx.first_residual_structure.2.2.1]
  exact hmap

/-- Conjugation by the second core preserves every derived coset in that core. -/
public theorem LargeTerminalContext.second_core_conj_preserves_derived_coset
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (f b g : G)
    (hfR : f ∈ ctx.firstResidual)
    (hb : b * f⁻¹ ∈ DerivedAmbient ctx.firstResidual)
    (hg : g ∈ twoCoreIn ctx.second) :
    MulAut.conj g b * f⁻¹ ∈ DerivedAmbient ctx.firstResidual := by
  let D := DerivedAmbient ctx.firstResidual
  let Q := twoCoreIn ctx.second
  have hRQ : ctx.firstResidual ≤ Q := by
    change ctx.firstResidual ≤ twoCoreIn ctx.second
    rw [ctx.derived_centralizer_supplement.1]
    exact le_sup_right
  have hDQ : D ≤ Q := (map_subtype_le _).trans hRQ
  have hbQ : b ∈ Q := by
    have h := Q.mul_mem (hDQ hb) (hRQ hfR)
    simpa only [inv_mul_cancel_right] using h
  have hc : ⁅g, b⁆ ∈ D := by
    change ⁅g, b⁆ ∈ DerivedAmbient ctx.firstResidual
    rw [← ctx.second_core_derived_eq,
      show DerivedAmbient (twoCoreIn ctx.second) = ⁅twoCoreIn ctx.second, twoCoreIn ctx.second⁆
        from map_subtype_commutator _]
    exact commutator_mem_commutator hg hbQ
  have h := D.mul_mem hc hb
  convert h using 1
  simp only [MulAut.conj_apply, commutatorElement_def, mul_assoc, inv_mul_cancel_left]

/-- A first-residual element moves the terminal module to the third neighbor,
whose intersection with the terminal module is the common elementary eight. -/
public theorem LargeTerminalContext.exists_residual_terminal_module_mover
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ∃ g : G, g ∈ ctx.firstResidual ∧
      ctx.terminalModule.map (MulAut.conj g).toMonoidHom ⊓ ctx.terminalModule =
        DerivedAmbient ctx.firstResidual ⊓ ctx.terminalModule := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle := ⟨⟨2, by omega⟩, rfl, rfl⟩
  let U := twoCoreIn (EAt Γ cp.firstStep)
  obtain ⟨_, hfirst, hterminal, hends⟩ := sectionTenOpeningGeometry tenCtx middle hpath
  have hUQ : U ≤ QAt Γ cp.firstStep := by
    change twoCoreIn (Γ.twoResidualAt cp.firstStep) ≤ Γ.twoCoreAt cp.firstStep
    rw [Γ.twoResidualAt_def, Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hUP : U ≤ GAt Γ cp.firstStep := by
    change twoCoreIn (Γ.twoResidualAt cp.firstStep) ≤ Γ.stabilizer cp.firstStep
    rw [Γ.twoResidualAt_def]
    exact (twoCoreIn_le _).trans (twoResidualIn_le _)
  have hUedge : U ≤ GAt Γ middle ⊓ GAt Γ cp.firstStep := le_inf
    (hUQ.trans (((lemma_seven_three tenCtx.sectionSeven Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hfirst)) default).2.2)) hUP
  have hescape := nine_seven_residual_core_escapes_neighbor
    tenCtx.toLocalContext.toSectionNineLocalContext cp.firstStep middle
      ⟨1, Γ.act_one _⟩ (Γ.adjacent_symm hfirst)
  have hcubic := cubic_local_action_of_sl2Two_quotient Γ tenCtx.sectionSeven middle
    (sectionTenOpeningData tenCtx middle hpath).quotient_model
  let Neighbors := {neighbor : Γ.Vertex // Γ.adjacent middle neighbor}
  let _ : Finite Γ.Vertex := Γ.finiteVertex
  have hthree : 3 ≤ ENat.card Neighbors := by
    rw [ENat.card_eq_coe_natCard, hcubic.degree]
    norm_num
  obtain ⟨third, hthirdFirst, hthirdTerminal⟩ := ENat.exists_ne_ne_of_three_le hthree
    (⟨cp.firstStep, hfirst⟩ : Neighbors) (⟨cp.a', hterminal⟩ : Neighbors)
  have hthirdFirst' : (third : Γ.Vertex) ≠ cp.firstStep :=
    fun heq => hthirdFirst (Subtype.ext heq)
  have hthirdTerminal' : (third : Γ.Vertex) ≠ cp.a' :=
    fun heq => hthirdTerminal (Subtype.ext heq)
  obtain ⟨actor, hmove⟩ := hcubic.punctured_transitivity cp.firstStep hfirst U hUedge hescape
    ⟨(mem_neighborhood_iff_adjacent Γ).mpr hterminal, hends.symm⟩
    ⟨(mem_neighborhood_iff_adjacent Γ).mpr third.property, hthirdFirst'⟩
  change Γ.act (actor : K) cp.a' = (third : Γ.Vertex) at hmove
  let e := MulAut.conj (actor : K)⁻¹
  have hE : (VAt Γ cp.a').map e.toMonoidHom = VAt Γ third := by
    change (v Γ cp.a').map _ = v Γ third
    rw [← hmove, v_act]
  have hinter := ten_one_neighbor_intersection tenCtx middle hpath
    third.property hterminal hthirdTerminal'
  have hamb := congrArg (fun L : Subgroup K => L.map K.subtype) hinter
  rw [map_inf _ _ _ K.subtype_injective, map_inf _ _ _ K.subtype_injective] at hamb
  refine ⟨((actor : K) : G)⁻¹, ?_, ?_⟩
  · exact mem_map_of_mem K.subtype (U.inv_mem actor.property)
  · have hmap : ctx.terminalModule.map (MulAut.conj ((actor : K) : G)⁻¹).toMonoidHom =
        (VAt Γ third).map K.subtype := by
      rw [← hE]
      change ((VAt Γ cp.a').map K.subtype).map _ =
        ((VAt Γ cp.a').map e.toMonoidHom).map K.subtype
      rw [map_map, map_map]
      rfl
    rw [hmap, ctx.first_residual_structure.2.2.1]
    exact hamb

/-- The actual terminal geometry supplies a mover for the entire block.
The witness belongs to the first residual, hence also to the second core. -/
public theorem LargeTerminalContext.exists_terminal_block_mover
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S)
    (f : G) (hfE : f ∈ ctx.terminalModule) (hfR : f ∈ ctx.firstResidual)
    (hfc : f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G)) :
    ∃ g : G, g ∈ ctx.firstResidual ∧ g ∈ twoCoreIn ctx.second ∧
      ∀ b : G, b * f⁻¹ ∈ DerivedAmbient ctx.firstResidual → b ∈ ctx.terminalModule →
        MulAut.conj g b * f⁻¹ ∈ DerivedAmbient ctx.firstResidual ∧
          MulAut.conj g b ∉ ctx.terminalModule := by
  let D := DerivedAmbient ctx.firstResidual
  let E := ctx.terminalModule
  let I := D ⊓ E
  let _ : IsElementaryAbelian 2 D := ctx.derived_residual_elementary
  have hfD : f ∉ I := fun h => hfc (le_centralizer D h.1)
  obtain ⟨g, hgR, hg⟩ := ctx.exists_residual_terminal_module_mover
  have hgQ : g ∈ twoCoreIn ctx.second :=
    (ctx.derived_centralizer_supplement.1 ▸ le_sup_right) hgR
  have hI := ctx.second_core_normalizes_terminal_intersection hgQ
  refine ⟨g, hgR, hgQ, ?_⟩
  intro b hb hbE
  refine ⟨ctx.second_core_conj_preserves_derived_coset f b g hfR hb hgQ, ?_⟩
  intro hbe
  have hbi : MulAut.conj g b ∈ I := by
    change MulAut.conj g b ∈ DerivedAmbient ctx.firstResidual ⊓ ctx.terminalModule
    rw [← hg]
    exact ⟨mem_map_of_mem _ hbE, hbe⟩
  have hbI : b ∈ I := (mem_normalizer_iff.mp hI b).mpr hbi
  apply hfD
  refine ⟨?_, hfE⟩
  change f ∈ D
  have h := D.mul_mem (D.inv_mem hb) hbI.1
  simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using h

end Stellmacher.Recognition
