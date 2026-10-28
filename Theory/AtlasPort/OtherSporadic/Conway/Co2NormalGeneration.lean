/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co2NormalGeneration.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co2LocalNormal

/-!
Normal generation and perfectness of the actual norm-four vector stabilizer.
Shortened signs force the local stabilizer; its primitive action then forces the whole group.

Source: Gerald Höhn, `Atlas/Conway/Co2NormalGeneration.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The local group is forced by the normal closure of the actual shortened signs. -/
theorem co2_local_le_normal_of_short_signs (N : Subgroup Co2MarkedModel) [N.Normal]
    (hE : ∀ (c : golay) (hi : c.val ((0,0),0) = 0) (hj : c.val ((0,0),1) = 0),
      co2ShortSignElement c hi hj ∈ N) : Atlas.Sporadic.Conway2.LocalGroup ≤ N := by
  let H := Atlas.Sporadic.Conway2.LocalGroup
  let P := N.comap H.subtype
  have : P.Normal := (inferInstance : N.Normal).comap H.subtype
  let f := Atlas.Sporadic.Conway2.pairProjection
  have hf : Function.Surjective f := fun q =>
    ⟨Atlas.Sporadic.Conway2.pairSection q,Atlas.Sporadic.Conway2.pairProjection_section q⟩
  have hker : f.ker ≤ P := by
    rw [Atlas.Sporadic.Conway2.pairProjection_kernel]
    rintro g ⟨c,rfl⟩
    have hi : c.toAdd.val.val ((0,0),0) = 0 := congrArg Prod.fst c.toAdd.prop
    have hj : c.toAdd.val.val ((0,0),1) = 0 := congrArg Prod.snd c.toAdd.prop
    exact hE c.toAdd.val hi hj
  have : (P.map f).Normal := (inferInstance : P.Normal).map f hf
  have hs : co2LocalSwap ∈ P.map f := by
    refine ⟨⟨co2NormalWitness,co2NormalWitness_local⟩,?_,co2NormalWitness_projection⟩
    exact co2NormalWitness_mem_normal N (hE _ _ _)
  have htop := co2Pair_normal_eq_top (P.map f) hs
  have he := Subgroup.comap_map_eq_self hker
  rw [htop,Subgroup.comap_top] at he
  intro g hg
  have hh : (⟨g,hg⟩ : H) ∈ P := he ▸ Subgroup.mem_top _
  exact hh

theorem co2_normal_eq_top_of_short_signs (N : Subgroup Co2MarkedModel) [N.Normal]
    (hE : ∀ (c : golay) (hi : c.val ((0,0),0) = 0) (hj : c.val ((0,0),1) = 0),
      co2ShortSignElement c hi hj ∈ N) : N = ⊤ := by
  let X := Atlas.Sporadic.Conway2.Points
  let a := Atlas.Sporadic.Conway2.basePoint
  have hH := co2_local_le_normal_of_short_signs N hE
  have hstab : MulAction.stabilizer Co2MarkedModel a ≤ N := by
    rw [Atlas.Sporadic.Conway2.full_point_stabilizer]
    exact hH
  have := Atlas.Sporadic.Conway2.primitive
  have := Atlas.Sporadic.Conway2.transitive
  have hnon : Nontrivial {l : X // Atlas.Sporadic.Conway2.suborbitIndex l = 1} := by
    let : Fintype {l : X // Atlas.Sporadic.Conway2.suborbitIndex l = 1} := Fintype.ofFinite _
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rw [← Nat.card_eq_fintype_card,Atlas.Sporadic.Conway2.suborbit_card]
    decide
  obtain ⟨l,m,hlm⟩ := exists_pair_ne {l : X // Atlas.Sporadic.Conway2.suborbitIndex l = 1}
  obtain ⟨s,hs⟩ := Atlas.Sporadic.Conway2.suborbit_transitive l.val m.val
    (l.prop.trans m.prop.symm)
  have hfixed : MulAction.fixedPoints N X ≠ Set.univ := by
    intro he
    have hx : l.val ∈ MulAction.fixedPoints N X := he ▸ Set.mem_univ _
    have hh := MulAction.mem_fixedPoints.mp hx (⟨s.val,hstab s.prop⟩ : N)
    have hsame : l.val = m.val := hh.symm.trans hs
    exact hlm (Subtype.ext hsame)
  have : MulAction.IsPretransitive N X :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed
  apply top_unique
  intro g _
  obtain ⟨n,hn⟩ := MulAction.exists_smul_eq N a (g • a)
  have hk : n.val⁻¹ * g ∈ MulAction.stabilizer Co2MarkedModel a := by
    change (n.val⁻¹ * g) • a = a
    rw [mul_smul,← hn]
    exact inv_smul_smul n.val a
  have hh := N.mul_mem n.prop (hstab hk)
  simpa only [mul_inv_cancel_left] using hh

/-- The concrete local sign subgroup, embedded in the actual vector stabilizer. -/
def co2Signs : Subgroup Co2MarkedModel :=
  Atlas.Sporadic.Conway2.signs.map Atlas.Sporadic.Conway2.LocalGroup.subtype

theorem co2ShortSign_mem_signs (c : golay) (hi : c.val ((0,0),0) = 0)
    (hj : c.val ((0,0),1) = 0) : co2ShortSignElement c hi hj ∈ co2Signs := by
  let d : Multiplicative Atlas.Sporadic.Conway2.SignModule :=
    Multiplicative.ofAdd ⟨c,Prod.ext hi hj⟩
  exact ⟨orthogonalLineSignEmbedding ((0,0),0)
    ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩ d,⟨d,rfl⟩,rfl⟩

theorem co2Signs_normalClosure : Subgroup.normalClosure (co2Signs : Set Co2MarkedModel) = ⊤ := by
  apply co2_normal_eq_top_of_short_signs
  intro c hi hj
  exact Subgroup.subset_normalClosure (co2ShortSign_mem_signs c hi hj)

theorem co2_commutator_eq_top : commutator Co2MarkedModel = ⊤ :=
  co2_normal_eq_top_of_short_signs _ co2_short_sign_mem_commutator

end Atlas.Conway
