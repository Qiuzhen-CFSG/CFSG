module
public import Stellmacher.SectionTen.TenOneLargeFirstResidualIndex
public import Stellmacher.SectionTen.TenOneLargeNeighborhoodQuotient

/-!
# The generated subgroup's terminal-module intersection

In the actual no-transvection Section Ten context, W meets Vend in a
subgroup of order sixteen and W is not contained in Vend. Both conclusions
follow from source (15), with no source-(16) centralizer equality or later
Frobenius quotient assumption.

The first seed Vfirst∩Qend has order sixteen: source (15) identifies it
with Vfirst∩O₂(Eend). The actual middle swap sends that seed to Vend∩Qfirst.
Neighbor-seed containment puts the latter in W, while W≤Qfirst proves it
is exactly W∩Vend. The first seed cannot lie in Vend, since its intersection
with Vend is bounded by I, of order eight.

These are the geometric cardinal inputs to Stellmacher (10.1)(17), Journal
of Algebra 190 (1997), printed pp.63–64. They also expose the incompatibility
of the printed first equality C_W(Vend)=I in (16), which is not used here.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_generated_terminal_intersection
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    let W:=conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep⊓QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle)
    Nat.card (W⊓VAt ctx.Γ ctx.criticalPath.a':Subgroup G)=16 ∧
      ¬ W≤VAt ctx.Γ ctx.criticalPath.a'  := by
  let A:=VAt ctx.Γ ctx.criticalPath.firstStep
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  let seed:=A⊓QAt ctx.Γ ctx.criticalPath.a'
  let W:=conjugateClosure seed (GAt ctx.Γ middle)
  obtain ⟨_,hfirst,hterminal,hends⟩:=sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨mover,_,hmoveA,hmoveV⟩:=ten_one_neighbor_pair_alignment ctx middle hpath
    hterminal hfirst hends.symm
  let e:=MulAut.conj mover⁻¹
  have hAmap : A.map e.toMonoidHom=V:=by
    change (v ctx.Γ ctx.criticalPath.firstStep).map _=v ctx.Γ ctx.criticalPath.a'
    rw [←v_act,hmoveA]
  have hQmap : (QAt ctx.Γ ctx.criticalPath.a').map e.toMonoidHom=QAt ctx.Γ ctx.criticalPath.firstStep:=by
    change (q ctx.Γ ctx.criticalPath.a').map _=q ctx.Γ ctx.criticalPath.firstStep
    rw [←q_act,hmoveV]
  obtain ⟨_,hVcard,hIcard⟩:=ten_one_large_terminal_structure ctx middle hpath hno
  have hAcard : Nat.card A=32:=by
    change Nat.card V=32 at hVcard
    rw [←hAmap,Subgroup.card_map_of_injective e.injective] at hVcard
    exact hVcard
  obtain ⟨hres,hWU⟩:=ten_one_large_first_residual_index ctx middle hpath hno
  have hseedW : seed≤W:=by
    intro x hx
    exact Subgroup.subset_closure ⟨(1:GAt ctx.Γ middle),⟨x,hx⟩,by simp⟩
  have hUQ : U≤QAt ctx.Γ ctx.criticalPath.a':=by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a')≤ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hseedEq : seed=A⊓U:=le_antisymm
    (le_inf inf_le_left (hseedW.trans hWU)) (inf_le_inf_left A hUQ)
  have hseedCard : Nat.card seed=16:=by
    change Nat.card A=2*Nat.card (A⊓U:Subgroup G) at hres
    rw [←hseedEq,hAcard] at hres
    omega
  have hseedMap : seed.map e.toMonoidHom=V⊓QAt ctx.Γ ctx.criticalPath.firstStep:=by
    rw [Subgroup.map_inf _ _ _ e.injective,hAmap,hQmap]
  have hseedMapW : seed.map e.toMonoidHom≤W:=by
    rw [hseedMap]
    exact ten_one_neighbor_seed_le_generated ctx middle hpath hterminal hfirst hends.symm
  have hWQ : W≤QAt ctx.Γ ctx.criticalPath.firstStep:=
    (ten_one_generated_containment ctx middle hpath).trans
      (inf_le_left.trans (sInf_le ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst,rfl⟩))
  have hintersection : W⊓V=seed.map e.toMonoidHom:=by
    rw [hseedMap]
    apply le_antisymm (le_inf inf_le_right (inf_le_left.trans hWQ))
    exact le_inf (hseedMap.symm.le.trans hseedMapW) inf_le_left
  constructor
  · rw [hintersection,Subgroup.card_map_of_injective e.injective,hseedCard]
  · intro hWV
    have hh:=Subgroup.card_le_of_le (le_inf (show seed≤A from inf_le_left) (hseedW.trans hWV))
    change Nat.card seed≤Nat.card (A⊓V:Subgroup G) at hh
    rw [hseedCard,hIcard] at hh
    omega
end Stellmacher.SectionTen
