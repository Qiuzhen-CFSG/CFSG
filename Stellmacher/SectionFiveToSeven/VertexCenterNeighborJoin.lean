module
public import Stellmacher.SectionFiveToSeven.VertexLocalModule
public import Stellmacher.SectionFiveToSeven.Result7_5

/-!
# Each vertex center lies in its neighbor-center join

For a vertex d and a supplied neighbor m in the actual Section Seven graph,
Z_d lies in V_d. An edge Sylow is Sylow in both stabilizers by (7.3), so its
omega-center lies in Z_m and hence V_d. The G_d-invariance of V_d then puts
the whole native normal closure defining Z_d inside V_d.

This supplies the initial-center containment used for the distance-two
common subgroup in (8.2). Source: Stellmacher, Section Seven notation and
(7.3)(a), with the b=2 paragraph of (8.2), printed p.38,
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionsFiveToSeven
open CosetGraphContext
universe u

public theorem vertex_center_le_neighbor_join
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    (d m : Γ.Vertex) (hm : m ∈ neighborhood Γ d) :
    z Γ d ≤ v Γ d := by
  let P := stabilizer Γ d
  let M := stabilizer Γ m
  let T : Sylow 2 ↥(P ⊓ M) := default
  obtain ⟨hWP, hWM, _⟩ := (lemma_seven_three h Γ).sylow_and_core d m hm T
  obtain ⟨_, U, hU⟩ := hWP
  obtain ⟨_, B, hB⟩ := hWM
  have hOmega : (omegaOneCenterAmbient (U : Subgroup P)).map P.subtype ≤ v Γ d := by
    rw [← omegaOneCenterAmbient_map_injective P.subtype P.subtype_injective]
    change omegaOneCenter ((U : Subgroup P).map P.subtype) ≤ v Γ d
    rw [hU]
    have hOmZm : omegaOneCenter (sylowTwoAmbient (P ⊓ M) T) ≤ z Γ m := by
      rw [z, Γ.zAt_def]
      exact le_sSup ⟨B, congrArg omegaOneCenter hB.symm⟩
    apply hOmZm.trans
    rw [v, Γ.vAt_def]
    exact le_sSup ⟨m, hm, rfl⟩
  let K := (v Γ d).comap P.subtype
  have hK : K.Normal := by
    constructor
    intro x hx g
    exact (Subgroup.mem_normalizer_iff.mp
      (stabilizer_le_normalizer_v Γ d g.property) x).mp hx
  let _ : K.Normal := hK
  rw [← vertexZ_eq_local_vSubgroup Γ d U, Subgroup.map_le_iff_le_comap]
  change Subgroup.normalClosure (omegaOneCenterAmbient (U : Subgroup P) : Set P) ≤ K
  apply Subgroup.normalClosure_le_normal
  exact Subgroup.map_le_iff_le_comap.mp hOmega

end Stellmacher.SectionsFiveToSeven
