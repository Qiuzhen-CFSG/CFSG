module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# Normalizing a selected neighboring edge and its Sylow

For a supplied neighbor n of the first critical-path step and a supplied
Sylow of their edge stabilizer, an element of the first-step stabilizer
carries n to the initial vertex and the supplied Sylow image to the
distinguished subgroup T, using the graph action's inverse-conjugation
convention.

Local transitivity first aligns the vertices while fixing the first step.
Transport the chosen Sylow to that edge. The distinguished T is a Sylow
there because it is Sylow in the first-step stabilizer and lies in the
edge. Sylow conjugacy inside the edge gives a correction that preserves
both vertices; append its inverse to the initial graph actor.

This is the selected-edge normalization needed for the second Baumann
configuration in Stellmacher (9.3), Journal of Algebra 190 (1997), p.49.
All groups remain in the original local graph context; no Hypothesis Two
or critical-path data is transported. Source: `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem isSylowTwoIn_map_equiv
    {G : Type u} [Group G] [Finite G]
    (e : G ≃* G) (S P : Subgroup G) (h : IsSylowTwoIn S P) :
    IsSylowTwoIn (S.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  obtain ⟨hSP, U, hU⟩ := h
  let eP := P.equivMapOfInjective e.toMonoidHom e.injective
  let U' := U.mapSurjective (f := eP.toMonoidHom) eP.surjective
  refine ⟨Subgroup.map_mono hSP, U', ?_⟩
  have heq : (U' : Subgroup (P.map e.toMonoidHom)) =
      (U : Subgroup P).map eP.toMonoidHom := Sylow.coe_mapSurjective eP.surjective U
  rw [heq, Subgroup.map_map, ← hU, Subgroup.map_map]
  congr 1

/-- An element fixing the first step aligns both the supplied neighboring
vertex and its selected edge Sylow with the initial distinguished edge. -/
public theorem nine_three_selected_edge_normalization
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (n : ctx.Γ.Vertex) (hn : n ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (U : Sylow 2 ↥(GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ n)) :
    ∃ g : G, g ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      ctx.Γ.act g n = ctx.criticalPath.a ∧
      (sylowTwoAmbient (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ n) U).map
        (MulAut.conj g⁻¹).toMonoidHom = T := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let E := P ⊓ GAt Γ cp.a
  let W := sylowTwoAmbient (P ⊓ GAt Γ n) U
  have ha : cp.a ∈ neighborhood Γ cp.firstStep :=
    (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  obtain ⟨a, han⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    cp.firstStep hn ha
  have hafix : Γ.act (a : G) cp.firstStep = cp.firstStep :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) (a : G)).mp a.property
  let e : G ≃* G := MulAut.conj (a : G)⁻¹
  have hPmap : P.map e.toMonoidHom = P := by
    change conjugateBy (stabilizer Γ cp.firstStep) (a : G)⁻¹ = _
    rw [← stabilizer_act, hafix]
  have hNmap : (GAt Γ n).map e.toMonoidHom = GAt Γ cp.a := by
    change conjugateBy (stabilizer Γ n) (a : G)⁻¹ = _
    rw [← stabilizer_act, han]
  have hEmap : (P ⊓ GAt Γ n).map e.toMonoidHom = E := by
    rw [Subgroup.map_inf _ _ _ e.injective, hPmap, hNmap]
  have hW : IsSylowTwoIn W (P ⊓ GAt Γ n) := ⟨Subgroup.map_subtype_le _, U, rfl⟩
  have hWmap := isSylowTwoIn_map_equiv e W (P ⊓ GAt Γ n) hW
  rw [hEmap] at hWmap
  obtain ⟨_, R, hR⟩ := hWmap
  have hTE : T ≤ E := by
    change T ≤ GAt Γ cp.firstStep ⊓ GAt Γ cp.a
    rw [inf_comm]
    exact cp.S_le_edge_stabilizers
  obtain ⟨hTP, T0, hT0⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).2
  have hTp : IsPGroup 2 T := hT0 ▸ T0.isPGroup'.map P.subtype
  have hTpE : IsPGroup 2 (T.subgroupOf E) :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTE).symm
  obtain ⟨R0, hTR0⟩ := hTpE.exists_le_sylow
  let Rg := (R0 : Subgroup E).map E.subtype
  have hTRg : T ≤ Rg := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hTE]
    exact Subgroup.map_mono hTR0
  have hRgP : Rg ≤ P := (Subgroup.map_subtype_le _).trans inf_le_left
  have hRgp : IsPGroup 2 (Rg.subgroupOf P) :=
    (R0.isPGroup'.map E.subtype).of_equiv (Subgroup.subgroupOfEquivOfLe hRgP).symm
  have hT0R : (T0 : Subgroup P) ≤ Rg.subgroupOf P := by
    intro t ht
    exact hTRg (hT0 ▸ Subgroup.mem_map_of_mem P.subtype ht)
  have hRgT : Rg = T := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hRgP, T0.is_maximal' hRgp hT0R, hT0]
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq E R R0
  have hconj : (W.map e.toMonoidHom).map (MulAut.conj (b : G)).toMonoidHom = T := by
    rw [← hRgT]
    change _ = (R0 : Subgroup E).map E.subtype
    rw [← hb, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, ← hR]
    change ((R : Subgroup E).map E.subtype).map (MulAut.conj (b : G)).toMonoidHom =
      ((R : Subgroup E).map (MulAut.conj b).toMonoidHom).map E.subtype
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  let g : G := (a : G) * (b : G)⁻¹
  have hbP : (b : G) ∈ P := b.property.1
  have hbA : (b : G) ∈ GAt Γ cp.a := b.property.2
  have hbfix : Γ.act (b : G)⁻¹ cp.a = cp.a :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.a) ((b : G)⁻¹)).mp
      ((GAt Γ cp.a).inv_mem hbA)
  refine ⟨g, P.mul_mem a.property (P.inv_mem hbP), ?_, ?_⟩
  · change Γ.act ((a : G) * (b : G)⁻¹) n = cp.a
    rw [Γ.act_mul, han, hbfix]
  · change W.map (MulAut.conj g⁻¹).toMonoidHom = T
    rw [← hconj, Subgroup.map_map]
    congr 1
    ext x
    simp [g, e, MulAut.conj_apply, mul_assoc]

end Stellmacher.SectionNine
