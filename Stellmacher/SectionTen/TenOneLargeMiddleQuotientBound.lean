module
public import Stellmacher.SectionTen.TenOneLargeSylowBounds
public import Stellmacher.SectionTen.TenOneLargeNeighborhoodAction
public import Stellmacher.SectionTen.TenOneLargeNeighborhoodQuotient
public import Stellmacher.SectionNine.NineInitialEdgeCoreProduct

/-!
# The middle core has at most eight times the neighborhood order

In the actual large Section Ten configuration, Q_middle has cardinality at
most eight times that of the generated middle neighborhood Wnext. The theorem
keeps the original context and no-transvection hypothesis and introduces no
quotient action or normality instance.

The established W/I and Wnext/W indices give |W|=32 and |Wnext|=256.
The original distinguished Sylow T is the initial edge; the initial edge
cardinality and opening conjugacy give |T|=2|Q_middle|. The proved large Sylow
upper bound |T|≤2^12 therefore gives |Q_middle|≤8|Wnext|.

This is the cardinal input to the final middle-residual index calculation in
Stellmacher (10.1), Journal of Algebra 190 (1997), printed p.65. All subgroups
are the original ambient subgroups; passing to a quotient is left to consumers
with their supplied normality instances.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_middle_quotient_card_bound
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    :
    Nat.card (QAt ctx.Γ middle)≤8*Nat.card (GeneratedNeighborhoodV ctx.Γ middle) := by
  have hTupper := (ten_one_large_sylow_card_bounds ctx middle hpath hno).2
  let I:=VAt ctx.Γ ctx.criticalPath.firstStep⊓VAt ctx.Γ ctx.criticalPath.a'
  let W:=conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep⊓QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ middle)
  let Wnext:=GeneratedNeighborhoodV ctx.Γ middle
  have hIcard : Nat.card I=8:=(ten_one_large_terminal_structure ctx middle hpath hno).2.2
  have hWcard : Nat.card W=32:=by
    have hh : Nat.card W=4*Nat.card I:=(ten_one_large_neighborhood_action ctx middle hpath hno).1
    rw [hIcard] at hh
    exact hh
  have hWnextCard : Nat.card Wnext=256:=by
    have hh : Nat.card Wnext=8*Nat.card W:=ten_one_large_neighborhood_quotient
      ctx middle hpath (ten_one_large_first_residual_index ctx middle hpath hno).1 hIcard hno
    rw [hWcard] at hh
    exact hh
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hjoin:=(nine_initial_edge_core_product ctx.toAmbientSectionNineContext hshort).1
  have hcores:=local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath
  have hTedge : T=GAt ctx.Γ ctx.criticalPath.a⊓GAt ctx.Γ ctx.criticalPath.firstStep:=
    le_antisymm ctx.criticalPath.S_le_edge_stabilizers (hjoin ▸ sup_le hcores.1 hcores.2)
  have hTcard : Nat.card T=2*Nat.card (QAt ctx.Γ ctx.criticalPath.a):=by
    exact (congrArg (fun K:Subgroup G=>Nat.card K) hTedge).trans
      (nine_initial_edge_core_product ctx.toAmbientSectionNineContext hshort).2
  obtain ⟨⟨actor,hactor⟩,_,_,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hQmap : (QAt ctx.Γ ctx.criticalPath.a).map (MulAut.conj actor⁻¹).toMonoidHom=
      QAt ctx.Γ middle:=by
    change (q ctx.Γ ctx.criticalPath.a).map _=q ctx.Γ middle
    rw [←q_act,hactor]
  have hQcard : Nat.card (QAt ctx.Γ middle)=Nat.card (QAt ctx.Γ ctx.criticalPath.a):=by
    rw [←hQmap]
    exact Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective
  change Nat.card (QAt ctx.Γ middle)≤8*Nat.card Wnext
  rw [hWnextCard,hQcard]
  norm_num at hTupper ⊢
  omega

end Stellmacher.SectionTen
